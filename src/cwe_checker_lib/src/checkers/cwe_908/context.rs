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
        println!("{} @ {}", &def.term, &def.tid);
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
