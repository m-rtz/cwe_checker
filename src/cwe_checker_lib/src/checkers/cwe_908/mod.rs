mod context;

use std::collections::{HashMap, HashSet};

use crate::{
    abstract_domain::AbstractIdentifier,
    analysis::{
        fixpoint::Computation,
        forward_interprocedural_fixpoint::{create_computation, GeneralizedContext},
        graph::Edge,
        interprocedural_fixpoint_generic::NodeValue,
        pointer_inference::{PointerInference, State},
        vsa_results::VsaResult,
    },
    intermediate_representation::*,
};
use itertools::Itertools;
use petgraph::graph::NodeIndex;
use serde::{Deserialize, Serialize};

use self::context::Context;
use crate::{
    analysis::graph::*,
    utils::{
        log::{CweWarning, LogMessage},
        symbol_utils::find_symbol,
    },
    AnalysisResults, CweModule,
};
use context::InitalizationStatus;

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
    let symbols: Vec<&Tid> = symbols
        .iter()
        .map(|x| {
            find_symbol(&analysis_results.project.program, x)
                .expect(&format!("Could not find symbol: {}", x))
                .0 // TODO: not fast fail
        })
        .collect();

    let mut return_nodes = vec![];

    for edge in graph.edge_indices() {
        if let Edge::ExternCallStub(jmp) = graph[edge] {
            if let Jmp::Call { target, .. } = &jmp.term {
                if symbols.contains(&target) {
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

fn compute<'a>(
    graph: &'a Graph,
    pir: &'a PointerInference<'a>,
    malloc_calls: Vec<(Tid, NodeIndex)>,
) -> Computation<GeneralizedContext<'a, Context<'a>>> {
    let context = Context::new(graph, pir);
    let mut computation = create_computation(context, None);

    for (tid, node) in malloc_calls {
        if let Some(fp_node_value) = pir.get_node_value(node) {
            // Some Nodes after malloc have no Value !?
            if let Some(abstract_id) = find_abstract_identifier(&tid, fp_node_value.unwrap_value())
            {
                computation.set_node_value(
                    node,
                    NodeValue::Value(HashMap::from([(abstract_id, InitalizationStatus::Uninit)])),
                );
            }
        }
    }
    computation.compute_with_max_steps(100);

    if !computation.has_stabilized() {
        panic!("Fixpoint for expression propagation did not stabilize.");
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
    value: &HashMap<AbstractIdentifier, InitalizationStatus>,
    blk: &Blk,
) -> Vec<CweWarning> {
    let pir = computation.get_context().get_context().pir;
    let mut value = value.clone();
    let mut cwe_warnings = Vec::new();

    for def in &blk.defs {
        match &def.term {
            Def::Load { var, address } => {
                if let Some(data_domain) = pir.eval_address_at_def(&def.tid) {
                    for id in data_domain.get_relative_values().keys() {
                        if let Some(i) = value.get(id) {
                            if i == &InitalizationStatus::Uninit {
                                dbg!(&data_domain.to_json_compact());
                                println!("Uninit Access!");

                                cwe_warnings.push(generate_cwe_warning(&def.tid, false))
                            }
                        }
                    }
                }
            }
            Def::Store { .. } => {
                if let Some(data_domain) = pir.eval_address_at_def(&def.tid) {
                    for id in data_domain.get_relative_values().keys() {
                        if let Some(i) = value.get(id) {
                            if i == &InitalizationStatus::Uninit {
                                value.insert(
                                    id.clone(),
                                    InitalizationStatus::Init {
                                        addresses: HashSet::from([def.tid.clone()]),
                                    },
                                );
                                println!("is Initalized here!")
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
        if let Some(node_value) = computation.get_node_value(node) {
            dbg!(&node);
            // only consider nodes with uninitalized memory
            if node_value
                .unwrap_value()
                .values()
                .contains(&InitalizationStatus::Uninit)
            {
                cwe_warnings.append(
                    find_uninit_access_in_blk(
                        &computation,
                        computation.get_node_value(node).unwrap().unwrap_value(),
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
    let config: Config = serde_json::from_value(cwe_params.clone()).unwrap();
    let results = analysis_results.pointer_inference.unwrap();

    let allocation_target_nodes =
        find_allocation_returnsites(config.symbols, results.get_graph(), analysis_results);

    let computation = compute(results.get_graph(), results, allocation_target_nodes);
    let mut cwe_warnings = extract_results(computation);
    cwe_warnings.dedup();

    (vec![], cwe_warnings)
}
