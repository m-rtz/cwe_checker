mod context;

use std::{
    collections::{HashMap},
};

use crate::{
    abstract_domain::{AbstractIdentifier, MemRegion},
    analysis::{
        self,
        fixpoint::Computation,
        forward_interprocedural_fixpoint::{create_computation, GeneralizedContext},
        graph::Edge,
        pointer_inference::{PointerInference, State},
        vsa_results::VsaResult,
    },
    intermediate_representation::*,
};
use petgraph::graph::NodeIndex;
use serde::{Deserialize, Serialize};

use self::context::Context;
use crate::checkers::cwe_908::context::InitializationStatus;
use crate::{
    analysis::graph::*,
    utils::{
        log::{CweWarning, LogMessage},
        symbol_utils::find_symbol,
    },
    AnalysisResults, CweModule,
};

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
    symbols: Vec<String>,
}

// Returns all Nodes where a malloc call returns to and tid of malloc call.
fn find_allocation_returnsites(
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
fn find_abstract_identifier(tid: &Tid, state: &State) -> Option<AbstractIdentifier> {
    for id in state.memory.get_all_object_ids() {
        if id.get_tid().address == tid.address {
            return Some(id);
        }
    }
    None
}

fn init_heap_allocation<'a>(
    mut computation: Computation<GeneralizedContext<'a, Context<'a>>>,
    alloc_calls: &Vec<(Tid, NodeIndex)>,
    address_bytesize: ByteSize,
    pir: &PointerInference,
) -> Computation<GeneralizedContext<'a, Context<'a>>> {
    for (call, node) in alloc_calls {
        if let Some(fp_node_value) = pir.get_node_value(*node) {
            if let Some(id) = find_abstract_identifier(call, fp_node_value.unwrap_value()) {
                println!("heap init id: {}", &id);
                let mem_region = MemRegion::new(address_bytesize);
                let value = HashMap::from([(id, mem_region)]);

                computation.set_node_value(
                    *node,
                    analysis::interprocedural_fixpoint_generic::NodeValue::Value(value),
                );
                computation.get_node_value(*node).unwrap().unwrap_value();
            }
        }
    }
    computation
}

fn init_stack_allocation<'a>(
    mut computation: Computation<GeneralizedContext<'a, Context<'a>>>,
    address_bytesize: ByteSize,
    pir: &PointerInference,
) -> Computation<GeneralizedContext<'a, Context<'a>>> {
    let graph = computation.get_graph().clone();
    let stack_pointer_register = &pir.get_context().project.stack_pointer_register;
    for node in graph.node_indices() {
        if let Node::BlkStart(_, _) = graph[node] {
            // OVERKILL: Iterating subs should be enough for init stack frames.
            for def in &graph[node].get_block().term.defs {
                if let Def::Assign { var, value } = &def.term {
                    if var == stack_pointer_register {
                        if let Expression::BinOp { op, lhs: _, rhs: _ } = value {
                            // Maybe also ensure that stack_pointer is part of expression
                            if op == &BinOpType::IntSub {
                                // Here we have a decreasing stack_pointer situation

                                //println!("stack init id: {:?}", pir.get_node_value(node).unwrap().unwrap_value().stack_id);

                                let stack_id = pir
                                    .get_node_value(node)
                                    .unwrap()
                                    .unwrap_value()
                                    .stack_id
                                    .clone();
                                let mut mem_region = MemRegion::new(address_bytesize);
                                mem_region.insert_at_byte_index(
                                    InitializationStatus::Init {
                                        addresses: [Tid::new("Return Address")].into(),
                                    },
                                    0,
                                );
                                let value = HashMap::from([(stack_id, mem_region)]);
                                computation.set_node_value(
                                    node,
                                    analysis::interprocedural_fixpoint_generic::NodeValue::Value(
                                        value,
                                    ),
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    computation
}

/// Generate the CWE warning for a detected instance of the CWE.
fn generate_cwe_warning(location: &Tid, is_stack_allocation: bool) -> CweWarning {
    CweWarning::new(
        CWE_MODULE.name,
        CWE_MODULE.version,
        format!(
            "Access of (potentially) uninitalized {} variable at 0x{}",
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

fn find_uninit_access_in_blk<'a>(
    computation: &Computation<GeneralizedContext<'a, Context<'a>>>,
    value: &HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>,
    blk: &Blk,
) -> Vec<CweWarning> {
    let pir = computation.get_context().get_context().pir;
    let mut value = value.clone();
    let mut cwe_warnings = Vec::new();

    for def in &blk.defs {
        println!("\t{}: {}", def.tid.address, def.term);
        match &def.term {
            Def::Load { .. } => {
                if let Some(data_domain) = pir.eval_address_at_def(&def.tid) {
                    for id in data_domain.get_relative_values().keys() {
                        if let Some(mem_region) = value.get(id) {
                            if id.to_string().contains("instr") {
                                // it is a heap object
                                if mem_region.contains_uninit_within_interval(
                                    data_domain.get_relative_values().get(id).unwrap(),
                                    false,
                                ) {
                                    cwe_warnings.push(generate_cwe_warning(&def.tid, false))
                                }
                            } else {
                                println!("\t\t{}", id);

                                println!("\t\t{:?}", mem_region);
                                println!(
                                    "\t\t{}",
                                    data_domain.get_relative_values().get(id).unwrap()
                                );
                                // it is a stack frame
                                if mem_region.contains_uninit_within_interval(
                                    data_domain.get_relative_values().get(id).unwrap(),
                                    true,
                                ) {
                                    cwe_warnings.push(generate_cwe_warning(&def.tid, true))
                                }
                            }
                        }
                    }
                }
            }
            Def::Store { .. } => {
                if let Some(data_domain) = pir.eval_address_at_def(&def.tid) {
                    for id in data_domain.get_relative_values().keys() {
                        if let Some(mem_region) = value.get_mut(id) {
                            // mem_region contains uninit within the interval of interest. Change it!
                            if mem_region.contains_uninit_within_interval(
                                data_domain.get_relative_values().get(id).unwrap(),
                                false,
                            ) {
                                mem_region.insert_interval(
                                    &InitializationStatus::Init {
                                        addresses: [def.tid.clone()].into(),
                                    },
                                    data_domain.get_relative_values().get(id).unwrap(),
                                );
                            }
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
                println!("\n{}", graph[node]);
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

    //let symbol_map = get_symbol_map(analysis_results.project, &config.symbols);

    let allocation_target_nodes =
        find_allocation_returnsites(config.symbols, pir.get_graph(), analysis_results);
    let context = Context::new(pir.get_graph(), pir);

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
