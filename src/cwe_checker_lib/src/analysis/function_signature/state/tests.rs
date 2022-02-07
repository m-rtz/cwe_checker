use super::*;

impl State {
    /// Generate a mock state for an ARM-32 state.
    pub fn mock() -> State {
        State::new(
            &Tid::new("mock_fn"),
            &Variable::mock("sp", 4),
            &CallingConvention::mock_standard_arm_32(),
        )
    }

    /// Generate a mock state for an x64 state.
    pub fn mock_x64(tid_name: &str) -> State {
        State::new(
            &Tid::new(tid_name),
            &Variable::mock("RSP", 8),
            &CallingConvention::mock_x64(),
        )
    }
}

/// Mock an abstract ID representing the stack.
fn mock_stack_id() -> AbstractIdentifier {
    AbstractIdentifier::new_from_var(Tid::new("mock_fn"), &Variable::mock("sp", 4))
}

/// Mock an abstract ID of a stack parameter
fn mock_stack_param_id(offset: i64, size: u64) -> AbstractIdentifier {
    AbstractIdentifier::new(
        Tid::new("mock_fn"),
        AbstractLocation::from_stack_position(
            mock_stack_id().unwrap_register(),
            offset,
            ByteSize::new(size),
        ),
    )
}

#[test]
fn test_new() {
    let state = State::mock();
    // Test the generated stack
    assert_eq!(&state.stack_id, &mock_stack_id());
    assert_eq!(state.stack.iter().len(), 0);
    // Assert that the register values are as expected
    assert_eq!(state.register.len(), 9); // 8 parameters plus stack pointer
    assert_eq!(
        state.get_register(&Variable::mock("sp", 4)),
        DataDomain::from_target(
            mock_stack_id(),
            Bitvector::zero(ByteSize::new(4).into()).into()
        )
    );
    // Check the generated tracked IDs
    assert_eq!(state.tracked_ids.len(), 8);
    for (id, access_pattern) in state.tracked_ids.iter() {
        assert_eq!(
            state.get_register(id.unwrap_register()),
            DataDomain::from_target(id.clone(), Bitvector::zero(ByteSize::new(4).into()).into())
        );
        assert_eq!(access_pattern, &AccessPattern::new());
    }
}

#[test]
fn test_store_and_load_from_stack() {
    let mut state = State::mock();
    let address = DataDomain::from_target(mock_stack_id(), Bitvector::from_i32(-4).into());
    let value: DataDomain<BitvectorDomain> = Bitvector::from_i32(0).into();
    // write and load a value to the current stack frame
    state.write_value(address.clone(), value.clone());
    assert_eq!(state.stack.iter().len(), 1);
    assert_eq!(
        state.stack.get(Bitvector::from_i32(-4), ByteSize::new(4)),
        value.clone()
    );
    assert_eq!(state.load_value(address, ByteSize::new(4)), value);
    // Load a parameter register and check that the parameter gets generated
    let address = DataDomain::from_target(mock_stack_id(), Bitvector::from_i32(4).into());
    let stack_param_id = mock_stack_param_id(4, 4);
    let stack_param =
        DataDomain::from_target(stack_param_id.clone(), Bitvector::from_i32(0).into());
    assert_eq!(state.tracked_ids.iter().len(), 8);
    assert_eq!(
        state.load_value(address.clone(), ByteSize::new(4)),
        stack_param
    );
    assert_eq!(state.tracked_ids.iter().len(), 9);
    assert_eq!(
        state
            .tracked_ids
            .get(&stack_param_id)
            .unwrap()
            .is_accessed(),
        false
    ); // The load method does not set access flags.
}

#[test]
fn test_load_unsized_from_stack() {
    let mut state = State::mock();
    // Load an existing stack param (generated by a sized load at the same address)
    let address = DataDomain::from_target(mock_stack_id(), Bitvector::from_i32(0).into());
    let stack_param_id = mock_stack_param_id(0, 4);
    let stack_param =
        DataDomain::from_target(stack_param_id.clone(), Bitvector::from_i32(0).into());
    state.load_value(address, ByteSize::new(4));
    let unsized_load = state.load_unsized_value_from_stack(Bitvector::from_i32(0));
    assert_eq!(unsized_load, stack_param);
    assert!(state.tracked_ids.get(&stack_param_id).is_some());
    // Load a non-existing stack param
    let stack_param_id = mock_stack_param_id(4, 1);
    let stack_param = DataDomain::from_target(stack_param_id.clone(), Bitvector::from_i8(0).into());
    let unsized_load = state.load_unsized_value_from_stack(Bitvector::from_i32(4));
    assert_eq!(unsized_load, stack_param);
    assert!(state.tracked_ids.get(&stack_param_id).is_some());
    // Unsized load from the current stack frame
    let unsized_load = state.load_unsized_value_from_stack(Bitvector::from_i32(-4));
    assert_eq!(unsized_load, DataDomain::new_top(ByteSize::new(1)));
}

#[test]
fn test_eval() {
    let mut state = State::mock();
    // Test the eval method
    let expr = Expression::Var(Variable::mock("sp", 4)).plus_const(42);
    assert_eq!(
        state.eval(&expr),
        DataDomain::from_target(mock_stack_id(), Bitvector::from_i32(42).into())
    );
    // Test the eval_parameter_arg method
    let arg = Arg::from_var(Variable::mock("sp", 4), None);
    assert_eq!(
        state.eval_parameter_arg(&arg),
        DataDomain::from_target(mock_stack_id(), Bitvector::from_i32(0).into())
    );
}

#[test]
fn test_extern_symbol_handling() {
    let mut state = State::mock();
    let extern_symbol = ExternSymbol::mock_arm32();
    let cconv = CallingConvention::mock_arm32();
    let call = Term {
        tid: Tid::new("call_tid"),
        term: Jmp::Call {
            target: extern_symbol.tid.clone(),
            return_: Some(Tid::new("return_tid")),
        },
    };
    let param_id = AbstractIdentifier::new_from_var(Tid::new("mock_fn"), &Variable::mock("r0", 4));
    let return_val_id =
        AbstractIdentifier::new_from_var(Tid::new("call_tid"), &Variable::mock("r0", 4));
    // Test extern symbol handling.
    state.handle_extern_symbol(&call, &extern_symbol, &cconv);
    assert_eq!(
        state
            .tracked_ids
            .get(&param_id)
            .unwrap()
            .is_mutably_dereferenced(),
        true
    );
    let return_val = state.get_register(&Variable::mock("r0", 4));
    assert_eq!(return_val.get_relative_values().iter().len(), 2);
    assert_eq!(
        return_val.get_relative_values().get(&param_id).unwrap(),
        &BitvectorDomain::new_top(ByteSize::new(4))
    );
    assert_eq!(
        return_val.get_relative_values().get(&param_id).unwrap(),
        &BitvectorDomain::new_top(ByteSize::new(4))
    );
    assert_eq!(
        return_val
            .get_relative_values()
            .get(&return_val_id)
            .unwrap(),
        &Bitvector::from_i32(0).into()
    );
}
