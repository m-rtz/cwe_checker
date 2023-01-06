use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::{
    abstract_domain::AbstractIdentifier,
    abstract_domain::{
        AbstractDomain, HasTop, IntervalDomain, MemRegion, SizedDomain, TryToInterval,
    },
    analysis::{graph::Graph, pointer_inference::PointerInference, vsa_results::VsaResult},
    intermediate_representation::*,
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum InitializationStatus {
    Init { addresses: HashSet<Tid> },
    MaybeInit { addresses: HashSet<Tid> },
    Uninit,
}

impl AbstractDomain for InitializationStatus {
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

            (InitializationStatus::Init { addresses }, InitializationStatus::Uninit) => {
                InitializationStatus::MaybeInit {
                    addresses: addresses.clone(),
                }
            }
            (
                InitializationStatus::MaybeInit { addresses },
                InitializationStatus::Init { addresses: a },
            )
            | (
                InitializationStatus::MaybeInit { addresses },
                InitializationStatus::MaybeInit { addresses: a },
            ) => InitializationStatus::MaybeInit {
                addresses: addresses.union(a).cloned().collect(),
            },
            (InitializationStatus::MaybeInit { addresses }, InitializationStatus::Uninit)
            | (InitializationStatus::Uninit, InitializationStatus::Init { addresses })
            | (InitializationStatus::Uninit, InitializationStatus::MaybeInit { addresses }) => {
                InitializationStatus::MaybeInit {
                    addresses: addresses.clone(),
                }
            }
            (
                InitializationStatus::Init { addresses },
                InitializationStatus::MaybeInit { addresses: a },
            ) => InitializationStatus::MaybeInit {
                addresses: addresses.union(a).cloned().collect(),
            },
        }
    }

    fn is_top(&self) -> bool {
        if let &InitializationStatus::MaybeInit { .. } = self {
            return true;
        }
        false
    }
}

impl SizedDomain for InitializationStatus {
    fn bytesize(&self) -> ByteSize {
        ByteSize::new(1)
    }

    fn new_top(bytesize: ByteSize) -> Self {
        InitializationStatus::MaybeInit {
            addresses: [].into(),
        }
    }
}

impl HasTop for InitializationStatus {
    fn top(&self) -> Self {
        InitializationStatus::MaybeInit {
            addresses: [].into(),
        }
    }
}

impl MemRegion<InitializationStatus> {
    pub fn contains_uninit(&self) -> bool {
        self.entry_map()
            .values()
            .contains(&InitializationStatus::Uninit)
    }
    pub fn get_init_status_at_byte_index(&self, index: i64) -> InitializationStatus {
        self.get(Bitvector::from_i64(index), ByteSize::new(1))
    }
    pub fn contains_uninit_within_interval(&self, interval: &IntervalDomain) -> bool {
        let (lower_bound, higher_bound) = interval.try_to_offset_interval().unwrap();
        for i in lower_bound..=higher_bound {
            if let InitializationStatus::Uninit = self.get_init_status_at_byte_index(i) {
                return true;
            }
        }
        false
    }

    pub fn insert_interval(&mut self, status: &InitializationStatus, interval: &IntervalDomain) {
        let (lower_bound, higher_bound) = interval.try_to_offset_interval().unwrap();
        for i in lower_bound..=higher_bound {
            if let Some(init_status) = self.entry_map().get(&i) {
                self.insert_at_byte_index(init_status.merge(status), i);
            } else {
                self.insert_at_byte_index(InitializationStatus::Uninit.merge(status), i);
            }
        }
    }
}

pub struct Context<'a> {
    graph: &'a Graph<'a>,
    pub pir: &'a PointerInference<'a>,
}

impl<'a> Context<'a> {
    /// Create a new context object for the given project and control flow graph.
    pub fn new(graph: &'a Graph, pir: &'a PointerInference<'a>) -> Context<'a> {
        Context { graph, pir }
    }
}

impl<'a> crate::analysis::forward_interprocedural_fixpoint::Context<'a> for Context<'a> {
    // init == true
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
        for (id, status) in value2.iter() {
            if merged.contains_key(id) {
                merged.insert(id.clone(), value2.get(id).unwrap().merge(status));
            } else {
                merged.insert(id.clone(), status.clone()).unwrap();
            }
        }

        merged
    }

    /// Changes the `InitalizationStatus` of an `Uninit` memory object to `Init`, if a `Store` instruction
    /// manipulates the memory object.
    fn update_def(
        &self,
        value: &Self::Value,
        def: &crate::intermediate_representation::Term<crate::intermediate_representation::Def>,
    ) -> Option<Self::Value> {
        if let Def::Store { .. } = &def.term {
            if let Some(data_domain) = self.pir.eval_address_at_def(&def.tid) {
                for (id, interval) in data_domain.get_relative_values().iter() {
                    if value.contains_key(id) {
                        // We track this mem object
                        let (offset_start, offset_end) = interval.try_to_offset_interval().unwrap();
                        let mut updated_value = value.clone();
                        for offset in offset_start..=offset_end {
                            updated_value.get(id).unwrap().clone().insert_at_byte_index(
                                InitializationStatus::Init {
                                    addresses: [].into(),
                                },
                                offset,
                            ); // TODO: reuse merge somehow
                        }
                        return Some(updated_value);
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
        Some(value.clone())
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
        value.cloned()
    }

    fn update_call_stub(
        &self,
        value: &Self::Value,
        call: &crate::intermediate_representation::Term<crate::intermediate_representation::Jmp>,
    ) -> Option<Self::Value> {
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
