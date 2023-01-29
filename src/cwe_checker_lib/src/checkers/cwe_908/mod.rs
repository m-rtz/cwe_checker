mod context;

use std::collections::{HashMap, HashSet};

use crate::{
    abstract_domain::AbstractIdentifier,
    analysis::{
        self,
        fixpoint::Computation,
        forward_interprocedural_fixpoint::{create_computation, GeneralizedContext},
        graph::Edge,
        pointer_inference::{PointerInference, State as PiState},
        vsa_results::VsaResult,
    },
    intermediate_representation::*,
};
use petgraph::graph::NodeIndex;
use serde::{Deserialize, Serialize};

use self::{context::Context, init_status::InitializationStatus, state::State};
use crate::{
    analysis::graph::*,
    utils::{
        log::{CweWarning, LogMessage},
        symbol_utils::find_symbol,
    },
    AnalysisResults, CweModule,
};

mod init_status;
mod state;

/// The module name and version
pub static CWE_MODULE: CweModule = CweModule {
    name: "CWE908",
    version: "0.1",
    run: check_cwe,
};

/// The configuration struct.
/// Lists all extern symbols in consideration, which create a memory object.
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash, Clone)]
pub struct Config {
    allocation_symbols: Vec<String>,
    extern_symbol_whitelist: Vec<String>,
}

/// For the provided symbols return the corresponding `Tid` of and `NodeIndex` of the return site.
// TODO: iterating over graph can be combined with heap initialization!
fn get_allocation_return_sites(
    symbols: Vec<String>,
    graph: &Graph,
    analysis_results: &AnalysisResults,
) -> Vec<(Tid, NodeIndex)> {
    let mut symbol_tids = vec![];
    for sym in symbols {
        if let Some((tid, _name)) = find_symbol(&analysis_results.project.program, &sym) {
            symbol_tids.push(tid);
        }
    }

    let mut return_nodes = vec![];

    for edge in graph.edge_indices() {
        if let Edge::ExternCallStub(jmp) = graph[edge] {
            if let Jmp::Call { target, .. } = &jmp.term {
                if symbol_tids.contains(&target) {
                    return_nodes.push((jmp.tid.clone(), graph.edge_endpoints(edge).unwrap().1));
                }
            }
        }
    }
    return_nodes
}

/// Resolves Tid of allocation function and the state of the return site to the
/// AbstractIdentifier of the new mem object.
fn get_abstract_identifier(tid: &Tid, state: &PiState) -> Option<AbstractIdentifier> {
    for id in state.memory.get_all_object_ids() {
        if id.get_tid().address == tid.address {
            return Some(id);
        }
    }
    None
}

/// Creates or updates a node's Value by adding a heap object.
///
/// The nodes after allocation calls are extended by the newly created heap object and an uninitialized `MemRegion`.
/// Already assigned identifier-MemRegion pairs are kept.
fn init_heap_allocation<'a>(
    mut computation: Computation<GeneralizedContext<'a, Context<'a>>>,
    alloc_calls: &Vec<(Tid, NodeIndex)>,
    address_bytesize: ByteSize,
    pir: &PointerInference,
) -> Computation<GeneralizedContext<'a, Context<'a>>> {
    for (call, node) in alloc_calls {
        if let Some(fp_node_value) = pir.get_node_value(*node) {
            if let Some(id) = get_abstract_identifier(call, fp_node_value.unwrap_value()) {
                println!("heap init id: {}", &id);

                let mut state = State::new_with_id(id, address_bytesize);

                if let Some(node_value) = computation.get_node_value(*node) {
                    state
                        .tracked_objects
                        .extend(node_value.unwrap_value().tracked_objects.clone());
                }
                computation.set_node_value(
                    *node,
                    analysis::interprocedural_fixpoint_generic::NodeValue::Value(state),
                );

                computation.get_node_value(*node).unwrap().unwrap_value();
            }
        }
    }
    computation
}

/// Creates or updated the Value for every function's first block.
///
/// The new Value is associated to the first BlkStart-node of a function and adds the stack frame.
/// Note that, the offset `0` is set as `InitializationStatus::Init` and represents the return address.
/// Already assigned identifier-MemRegion pairs are kept.
fn init_stack_allocation<'a>(
    mut computation: Computation<GeneralizedContext<'a, Context<'a>>>,
    address_bytesize: ByteSize,
    pir: &PointerInference,
) -> Computation<GeneralizedContext<'a, Context<'a>>> {
    let graph = computation.get_graph().clone();

    for node in graph.node_indices() {
        if let Node::BlkStart(blk, sub) = graph[node] {
            if let Some(first_block) = sub.term.blocks.first() {
                if first_block == blk {
                    // blk is first block in sub
                    let stack_id = pir
                        .get_node_value(node)
                        .unwrap()
                        .unwrap_value()
                        .stack_id
                        .clone();

                    let mut state = State::new_with_id(stack_id.clone(), address_bytesize);
                    state.insert_single_offset(
                        &stack_id,
                        0,
                        InitializationStatus::Init {
                            addresses: [Tid::new("Return Address")].into(),
                        },
                    );

                    if let Some(node_value) = computation.get_node_value(node) {
                        state
                            .tracked_objects
                            .extend(node_value.unwrap_value().tracked_objects.clone());
                    }
                    computation.set_node_value(
                        node,
                        analysis::interprocedural_fixpoint_generic::NodeValue::Value(state),
                    );
                }
            }
        }
    }
    computation
}

/// Generate the CWE warning for a detected instance of the CWE.
fn generate_cwe_warning_for_uninit_access_(
    location: &Tid,
    is_stack_allocation: bool,
) -> CweWarning {
    CweWarning::new(
        CWE_MODULE.name,
        CWE_MODULE.version,
        format!(
            "Access of uninitialized {} variable at 0x{}",
            match is_stack_allocation {
                true => "stack",
                false => "heap",
            },
            location.address
        ),
    )
    .tids(vec![format!("{}", location)])
    .addresses(vec![location.address.clone()])
    .symbols(vec![])
}

fn generate_cwe_warning_for_maybe_uninit_access(
    location: &Tid,
    is_stack_allocation: bool,
    maybe_uninit_locations: HashMap<i64, HashSet<Tid>>,
) -> CweWarning {
    let mut description = format!(
        "Access of potentially uninitialized {} variable at 0x{}.\n",
        match is_stack_allocation {
            true => "stack",
            false => "heap",
        },
        location.address,
    );
    description.push_str("Offset\tPotential initialization location\n");
    for (offset, init_locations) in maybe_uninit_locations {
        description.push_str(
            format!(
                "{}\t{:?}\n",
                offset,
                init_locations
                    .into_iter()
                    .map(|x| x.address)
                    .collect::<Vec<String>>()
            )
            .as_str(),
        );
    }
    CweWarning::new(CWE_MODULE.name, CWE_MODULE.version, description)
        .tids(vec![format!("{}", location)])
        .addresses(vec![location.address.clone()])
        .symbols(vec![])
}

fn find_uninit_access_in_blk<'a>(
    computation: &Computation<GeneralizedContext<'a, Context<'a>>>,
    value: &State,
    blk: &Blk,
) -> Vec<CweWarning> {
    let pir = computation.get_context().get_context().pir;
    let mut value = value.clone();
    let mut cwe_warnings = Vec::new();

    for def in &blk.defs {
        //println!("\t{}: {}", def.tid.address, def.term);
        match &def.term {
            Def::Load { .. } => {
                if let Some(data_domain) = pir.eval_address_at_def(&def.tid) {
                    for source_id in data_domain.get_relative_values().keys() {
                        if let Some(mem_region) = value.tracked_objects.get(source_id) {
                            if source_id.to_string().contains("instr") {
                                // it is a heap object
                                if mem_region.contains_uninit_within_interval(
                                    data_domain.get_relative_values().get(source_id).unwrap(),
                                    false,
                                ) {
                                    cwe_warnings.push(generate_cwe_warning_for_uninit_access_(
                                        &def.tid, false,
                                    ))
                                }
                                if let Some(maybe_init) = mem_region
                                    .get_maybe_init_locatons_within_interval(
                                        data_domain.get_relative_values().get(source_id).unwrap(),
                                        false,
                                    )
                                {
                                    cwe_warnings.push(generate_cwe_warning_for_maybe_uninit_access(
                                        &def.tid, false, maybe_init,
                                    ))
                                }
                            } else {
                                //println!("\t\t{}", id);

                                //println!("\t\t{:?}", mem_region);
                                //println!(                                    "\t\t{}",                                    data_domain.get_relative_values().get(id).unwrap()                                );

                                // it is a stack frame
                                if mem_region.contains_uninit_within_interval(
                                    data_domain.get_relative_values().get(source_id).unwrap(),
                                    true,
                                ) {
                                    cwe_warnings.push(generate_cwe_warning_for_uninit_access_(
                                        &def.tid, true,
                                    ))
                                }
                                if let Some(maybe_init) = mem_region
                                    .get_maybe_init_locatons_within_interval(
                                        data_domain.get_relative_values().get(source_id).unwrap(),
                                        false,
                                    )
                                {
                                    cwe_warnings.push(generate_cwe_warning_for_maybe_uninit_access(
                                        &def.tid, true, maybe_init,
                                    ))
                                }
                            }
                        } else {
                            println!("Load from {source_id} here @ {}, but its not tracked (possible UAF):(. TODO: Consider it as uninit?", def.tid)
                        }
                    }
                }
            }
            Def::Store { .. } => {
                if let Some(data_domain) = pir.eval_address_at_def(&def.tid) {
                    for target_id in data_domain.get_relative_values().keys() {
                        if let Some(mem_region) = value.tracked_objects.get_mut(target_id) {
                            // mem_region contains uninit within the interval of interest. Change it!
                            if mem_region.contains_uninit_within_interval(
                                data_domain.get_relative_values().get(target_id).unwrap(),
                                false,
                            ) {
                                mem_region.merge_interval(
                                    &InitializationStatus::Init {
                                        addresses: [def.tid.clone()].into(),
                                    },
                                    data_domain.get_relative_values().get(target_id).unwrap(),
                                );
                            }
                        } else {
                            println!("Store to {target_id} here @ {}, but object is not tracked (possible UAF) :( TODO: Add object?", def.tid);
                        }
                    }
                }
            }
            _ => (),
        }
    }
    cwe_warnings
}

fn extract_results<'a>(
    computation: Computation<GeneralizedContext<'a, Context<'a>>>,
) -> Vec<CweWarning> {
    let mut cwe_warnings = Vec::new();
    let graph = computation.get_graph();
    for node in graph.node_indices() {
        if let Node::BlkStart(_, _) | Node::BlkEnd(_, _) = graph[node] {
            if let Some(node_value) = computation.get_node_value(node) {
                //println!("\n{}", graph[node]);
                cwe_warnings.append(
                    find_uninit_access_in_blk(
                        &computation,
                        node_value.unwrap_value(),
                        &computation.get_graph()[node].get_block().term,
                    )
                    .as_mut(),
                );
            }
        }
    }
    cwe_warnings
}

pub fn check_cwe(
    analysis_results: &AnalysisResults,
    cwe_params: &serde_json::Value,
) -> (Vec<LogMessage>, Vec<CweWarning>) {
    let pointer_size = analysis_results.project.get_pointer_bytesize();
    let config: Config = serde_json::from_value(cwe_params.clone()).unwrap();
    let pir = analysis_results.pointer_inference.unwrap();

    let context = Context::new(analysis_results, config.extern_symbol_whitelist.clone());
    let allocation_target_nodes =
        get_allocation_return_sites(config.allocation_symbols, pir.get_graph(), analysis_results);

    print_graph(pir.get_graph());

    let computation = create_computation(context, None);
    let computation = init_stack_allocation(computation, pointer_size, pir);
    let mut computation =
        init_heap_allocation(computation, &allocation_target_nodes, pointer_size, pir);
    println!(
        "\n#################################\n START COMPUTING FIXPOINT\n#################################"
    );
    computation.compute_with_max_steps(100);
    println!(
        "\n#################################\n END COMPUTING FIXPOINT\n#################################"
    );

    if !computation.has_stabilized() {
        panic!("Fixpoint for expression propagation did not stabilize.");
    }

    let mut cwe_warnings = extract_results(computation);
    println!("\n###########\nFinal Results\n#########");
    cwe_warnings.dedup();

    (vec![], cwe_warnings)
}

fn print_graph(graph: &Graph) {
    for node in graph.node_indices() {
        if let Node::BlkStart(blk, sub) = graph[node] {
            println!("blk: {} @ {}", blk.tid, blk.tid.address);
            for def in &blk.term.defs {
                println!("\t{}: {}", def.tid, def.term)
            }
            println!()
        }
    }
}
