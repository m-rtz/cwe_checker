use std::collections::{BTreeMap, HashMap, HashSet};

use itertools::Itertools;

use crate::{
    abstract_domain::AbstractIdentifier,
    abstract_domain::{
        AbstractDomain, DataDomain, HasTop, Interval, IntervalDomain, MemRegion, SizedDomain,
        TryToInterval,
    },
    analysis::{
        function_signature::FunctionSignature,
        graph::Graph,
        pointer_inference::{PointerInference, ValueDomain},
        vsa_results::VsaResult,
    },
    intermediate_representation::*,
    prelude::AnalysisResults,
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum InitializationStatus {
    Init { addresses: HashSet<Tid> },
    MaybeInit { addresses: HashSet<Tid> },
    Uninit,
}

impl InitializationStatus {
    /// merge for in-block statuses (Init + Uninit = Init)
    pub fn merge_precise(&self, other: &Self) -> Self {
        match (self, other) {
            (InitializationStatus::Init { addresses }, InitializationStatus::Uninit)
            | (InitializationStatus::Uninit, InitializationStatus::Init { addresses }) => {
                InitializationStatus::Init {
                    addresses: addresses.clone(),
                }
            }
            (a, b) => a.merge(b),
        }
    }
}

impl AbstractDomain for InitializationStatus {
    /// merges in the sense for merging blocks (Init + Uninit = MaybeInint)
    fn merge(&self, other: &Self) -> Self {
        match (self, other) {
            (
                InitializationStatus::Init { addresses },
                InitializationStatus::Init { addresses: a },
            ) => InitializationStatus::Init {
                addresses: addresses.union(a).cloned().collect(),
            },
            (InitializationStatus::Uninit, InitializationStatus::Uninit) => {
                InitializationStatus::Uninit
            }

            (
                InitializationStatus::MaybeInit { addresses },
                InitializationStatus::Init { addresses: a },
            )
            | (
                InitializationStatus::MaybeInit { addresses },
                InitializationStatus::MaybeInit { addresses: a },
            )
            | (
                InitializationStatus::Init { addresses },
                InitializationStatus::MaybeInit { addresses: a },
            ) => InitializationStatus::MaybeInit {
                addresses: addresses.union(a).cloned().collect(),
            },
            (InitializationStatus::MaybeInit { addresses }, InitializationStatus::Uninit)
            | (InitializationStatus::Uninit, InitializationStatus::Init { addresses })
            | (InitializationStatus::Uninit, InitializationStatus::MaybeInit { addresses })
            | (InitializationStatus::Init { addresses }, InitializationStatus::Uninit) => {
                InitializationStatus::MaybeInit {
                    addresses: addresses.clone(),
                }
            }
        }
    }

    fn is_top(&self) -> bool {
        if let &InitializationStatus::Uninit = self {
            return true;
        }
        false
    }
}

impl SizedDomain for InitializationStatus {
    fn bytesize(&self) -> ByteSize {
        ByteSize::new(1)
    }

    fn new_top(_bytesize: ByteSize) -> Self {
        InitializationStatus::Uninit
    }
}

impl HasTop for InitializationStatus {
    fn top(&self) -> Self {
        InitializationStatus::Uninit
    }
}

impl MemRegion<InitializationStatus> {
    pub fn contains_uninit(&self) -> bool {
        self.entry_map()
            .values()
            .contains(&InitializationStatus::Uninit)
    }

    /// Returns the `InitalizationStatus` at the given offset.
    ///
    /// If no value at the offset is present `InitalizationStatus::Uninit` is returned.
    pub fn get_init_status_at_byte_index(&self, index: i64) -> InitializationStatus {
        if let Some(status) = self.entry_map().get(&index) {
            status.clone()
        } else {
            InitializationStatus::Uninit
        }
    }

    /// Returns true if the `MemRegion` contains at least one `InitalizationStatus::Uninit` value
    /// within the given offset interval.
    ///
    /// Note that values not set are treated as `InitalizationStatus::Uninit`. Positive offsets can be ignored, which
    /// in fact treats them as initialized.
    pub fn contains_uninit_within_interval(
        &self,
        interval: &IntervalDomain,
        ignore_non_neg_offsets: bool,
    ) -> bool {
        if let Ok((lower_bound, upper_bound)) = interval.try_to_offset_interval().as_mut() {
            if ignore_non_neg_offsets {
                if *lower_bound > 0 && *upper_bound > 0 {
                    return false;
                } else if *lower_bound > 0 {
                    *lower_bound = 0;
                }
            }
            println!("\t\t\t bounds: {} - {}", lower_bound, upper_bound);
            for i in *lower_bound..=*upper_bound {
                if let InitializationStatus::Uninit = self.get_init_status_at_byte_index(i) {
                    return true;
                }
            }
            false
        } else {
            println!("could not determine offset interval, so consider it uninit!");
            true
        }
    }

    /// Inserts an `InitalizationStatus` at multiple offsets, utilizing the `merge()` function.
    pub fn insert_interval(&mut self, status: &InitializationStatus, interval: &IntervalDomain) {
        if let Ok((lower_bound, higher_bound)) = interval.try_to_offset_interval() {
            for i in lower_bound..=higher_bound {
                if let Some(init_status) = self.entry_map().get(&i) {
                    self.insert_at_byte_index(init_status.merge(status), i);
                } else {
                    self.insert_at_byte_index(InitializationStatus::Uninit.merge(status), i);
                }
            }
        } else {
            println!(
                "provided interval can not be turned into offset interval... find a solution here!"
            )
        }
    }
}

pub struct Context<'a> {
    graph: &'a Graph<'a>,
    pub pir: &'a PointerInference<'a>,
    pub function_signatures: &'a BTreeMap<Tid, FunctionSignature>,
    pub extern_symbol_whitelist: Vec<String>,
}

impl<'a> Context<'a> {
    /// Create a new context object for the given project and control flow graph.
    pub fn new<'b>(
        analysis_results: &'b AnalysisResults<'a>,
        extern_symbol_whitelist: Vec<String>,
    ) -> Context<'a>
    where
        'a: 'b,
    {
        Context {
            graph: analysis_results.control_flow_graph,
            pir: analysis_results.pointer_inference.unwrap(),
            function_signatures: analysis_results.function_signatures.unwrap(),
            extern_symbol_whitelist: extern_symbol_whitelist,
        }
    }

    fn extract_parameters(
        &self,
        symbol: &ExternSymbol,
        call_tid: &Tid,
    ) -> Vec<Option<DataDomain<ValueDomain>>> {
        symbol
            .parameters
            .iter()
            .map(|param| self.pir.eval_parameter_arg_at_call(call_tid, param))
            .collect()
    }

    fn handle_memset(
        &self,
        call_tid: &Tid,
        memset_symbol: &ExternSymbol,
        value: &HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>,
    ) -> Option<HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>> {
        println!("handeling memset");
        let params = self.extract_parameters(memset_symbol, call_tid);
        if let Some(target) = &params[0] {
            //TODO: Check if param[1] is not uninit
            if let Some(size) = &params[2] {
                for (id, interval) in target.get_relative_values() {
                    // TODO: if relative value is not unique, maybe init as MaybeInit
                    if let Some(mem_region) = value.get(id) {
                        let target_offset = interval.try_to_offset_interval().unwrap().0; // Over approx here
                        let size = size
                            .get_if_absolute_value()
                            .unwrap()
                            .try_to_offset_interval()
                            .unwrap()
                            .1; // Over approx here
                        let mut mem_region = mem_region.clone();
                        // TODO: maybe inserte as interval here
                        for i in target_offset..(target_offset + size) {
                            mem_region.insert_at_byte_index(
                                InitializationStatus::Init {
                                    addresses: [call_tid.clone()].into(),
                                },
                                i,
                            );
                            let mut value = value.clone();
                            value.insert(id.clone(), mem_region);
                            return Some(value);
                        }
                    } else {
                        println!("We are not tracking this mem object :(")
                    }
                }
            } else {
                println!("could not get parm[2]");
            }
        } else {
            println!("could not get parm[0]");
        }

        None
    }

    fn handle_memcpy(
        &self,
        call_tid: &Tid,
        memcpy_symbol: &ExternSymbol,
        value: &HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>,
    ) -> Option<HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>> {
        let params = self.extract_parameters(memcpy_symbol, call_tid);
        if let Some(parm0) = &params[0] {
            for (target_id, target_interval) in parm0.get_relative_values() {
                if let Some(target) = value.get(target_id) {
                    let target_offset = target_interval.try_to_offset_interval().unwrap().0; // Over approx here

                    if let Some(parm1) = &params[1] {
                        for (source_id, source_interval) in parm1.get_relative_values() {
                            if let Some(source) = value.get(source_id) {
                                let source_offset =
                                    source_interval.try_to_offset_interval().unwrap().0; // Over approx here

                                if let Some(parm2) = &params[2] {
                                    let size = parm2
                                        .get_if_absolute_value()
                                        .unwrap()
                                        .try_to_offset_interval()
                                        .unwrap()
                                        .1; //Over approx here

                                    let mut target = target.clone();
                                    for (relative_offset, absolute_offset) in
                                        (source_offset..(source_offset + size)).enumerate()
                                    {
                                        let status =
                                            source.get_init_status_at_byte_index(absolute_offset);
                                        if status == InitializationStatus::Uninit {
                                            println!("Source contains uninit within rellevant interval. TODO: Possible uninit read!")
                                        }
                                        target.insert_at_byte_index(
                                            status,
                                            target_offset + relative_offset as i64,
                                        );
                                    }
                                    let mut value = value.clone();
                                    value.insert(target_id.clone(), target);
                                    return Some(value);
                                } else {
                                    println!("parm[2] was none :(")
                                }
                            } else {
                                println!("We are not tracking source object. TODO: let's consider it uninit")
                            }
                        }
                    } else {
                        println!("parm[1] was none :(")
                    }
                }
            }
        } else {
            println!("parm[0] was None :(")
        }

        None
    }

    fn handle_free(
        &self,
        call_tid: &Tid,
        free_symbol: &ExternSymbol,
        value: &HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>,
    ) -> Option<HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>> {
        println!("in handle_free");
        let params = self.extract_parameters(free_symbol, call_tid);
        if let Some(arg) = &params[0] {
            for (id, interval) in arg.get_relative_values() {
                if let Some(a) = value.get(id) {
                    println!("remove freed memory object");
                    let mut value = value.clone();
                    value.remove(id);
                    return Some(value);
                }
            }
        }

        None
    }
}

impl<'a> crate::analysis::forward_interprocedural_fixpoint::Context<'a> for Context<'a> {
    type Value = HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>;

    fn get_graph(&self) -> &crate::analysis::graph::Graph<'a> {
        self.graph
    }

    /// Merges the set of tracked memory objects and their statuses.
    ///
    /// Both sets are combined, but if the status the same memory object is initialized
    /// and uninitialized, the status is set to `MaybeInit`.
    fn merge(&self, value1: &Self::Value, value2: &Self::Value) -> Self::Value {
        let mut merged = value1.clone();
        for (id, mem_region) in value2.iter() {
            if merged.contains_key(id) {
                let mut mem_region = merged.get(id).unwrap().clone();
                for (i, status) in value2.get(id).unwrap().entry_map().iter() {
                    mem_region.insert_at_byte_index(
                        mem_region.get_init_status_at_byte_index(*i).merge(status),
                        *i,
                    );
                }
            } else {
                merged.insert(id.clone(), mem_region.clone());
            }
        }

        merged
    }

    /// Changes the `InitalizationStatus` of an `Uninit` memory object to `Init`, if a `Store` instruction
    /// manipulates the memory object.
    fn update_def(&self, value: &Self::Value, def: &Term<Def>) -> Option<Self::Value> {
        //println!("{} @ {}", &def.term, &def.tid);
        if let Def::Store { .. } = &def.term {
            if let Some(data_domain) = self.pir.eval_address_at_def(&def.tid) {
                for (id, interval) in data_domain.get_relative_values().iter() {
                    if value.contains_key(id) {
                        // We track this mem object
                        //dbg!( id, interval);
                        if let Ok((offset_start, offset_end)) = interval.try_to_offset_interval() {
                            let mut updated_value = value.get(id).unwrap().clone();
                            for offset in offset_start..=offset_end {
                                let old_status =
                                    updated_value.get_init_status_at_byte_index(offset);
                                updated_value.insert_at_byte_index(
                                    old_status.merge_precise(&InitializationStatus::Init {
                                        addresses: [def.tid.clone()].into(),
                                    }),
                                    offset,
                                );
                            }
                            let mut update = value.clone();
                            update.insert(id.clone(), updated_value.clone()).unwrap();
                            return Some(update);
                        } else {
                            println!("interval was top");
                        }
                    }
                }
            }
        }
        Some(value.clone())
    }

    fn update_jump(
        &self,
        value: &Self::Value,
        jump: &crate::intermediate_representation::Term<crate::intermediate_representation::Jmp>,
        untaken_conditional: Option<
            &crate::intermediate_representation::Term<crate::intermediate_representation::Jmp>,
        >,
        target: &crate::intermediate_representation::Term<crate::intermediate_representation::Blk>,
    ) -> Option<Self::Value> {
        Some(value.clone())
    }

    fn update_call(
        &self,
        value: &Self::Value,
        call: &crate::intermediate_representation::Term<crate::intermediate_representation::Jmp>,
        target: &crate::analysis::graph::Node,
        calling_convention: &Option<String>,
    ) -> Option<Self::Value> {
        None
    }

    fn update_return(
        &self,
        value: Option<&Self::Value>,
        value_before_call: Option<&Self::Value>,
        call_term: &crate::intermediate_representation::Term<
            crate::intermediate_representation::Jmp,
        >,
        return_term: &crate::intermediate_representation::Term<
            crate::intermediate_representation::Jmp,
        >,
        calling_convention: &Option<String>,
    ) -> Option<Self::Value> {
        None
    }

    fn update_call_stub(
        &self,
        value: &Self::Value,
        call: &crate::intermediate_representation::Term<crate::intermediate_representation::Jmp>,
    ) -> Option<Self::Value> {
        if let Some(extern_symbol) = match &call.term {
            Jmp::Call { target, .. } => self
                .pir
                .get_context()
                .project
                .program
                .term
                .extern_symbols
                .get(target),
            _ => None,
        } {
            println!("{:?}: {}", call.tid, extern_symbol.name);
            match extern_symbol.name.as_str() {
                "memset" => return self.handle_memset(&call.tid, extern_symbol, value),
                "memcpy" => return self.handle_memcpy(&call.tid, extern_symbol, value),
                "free" => return self.handle_free(&call.tid, extern_symbol, value),
                _ => {
                    if !self.extern_symbol_whitelist.contains(&extern_symbol.name) {
                        for param in &extern_symbol.parameters {
                            if let Some(data_domain) =
                                self.pir.eval_parameter_arg_at_call(&call.tid, param)
                            {
                                for (id, _interval) in data_domain.get_relative_values() {
                                    if value.contains_key(id) {
                                        println!("tracked object: {id} with uninit values within interval was used as param by {}! TODO: issue warning here!", extern_symbol.name)
                                    }
                                    println!(
                                        "Argument is mem object we do not track :( TODO: handle it"
                                    )
                                }
                            }
                            println!("Could not get argument of call :(")
                        }
                    } else {
                        println!("extern sym: {} is white listed", extern_symbol.name);
                    }
                }
            }
        }

        //dbg!(self.function_signatures);
        //println!("entered update call stub");

        //for (name, pattern) in &self.pir.get_context().extern_fn_param_access_patterns{
        //    println!("{}: {:#?}", name, pattern)
        //}
        //if let Some(a)= self.pir.eval_parameter_arg_at_call(&call.tid, self.pir.get_context().extern_fn_param_access_patterns){

        Some(value.clone())
    }

    fn specialize_conditional(
        &self,
        value: &Self::Value,
        condition: &crate::intermediate_representation::Expression,
        block_before_condition: &crate::intermediate_representation::Term<
            crate::intermediate_representation::Blk,
        >,
        is_true: bool,
    ) -> Option<Self::Value> {
        Some(value.clone())
    }
}
