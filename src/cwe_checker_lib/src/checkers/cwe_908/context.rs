use std::collections::{HashMap, HashSet};

use crate::{
    abstract_domain::AbstractIdentifier,
    analysis::{graph::Graph, pointer_inference::PointerInference, vsa_results::VsaResult},
    intermediate_representation::*,
};

#[derive(Clone, PartialEq, Eq)]
pub enum InitalizationStatus {
    Init { addresses: HashSet<Tid> },
    MaybeInit { addresses: HashSet<Tid> },
    Uninit,
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
    type Value = HashMap<AbstractIdentifier, InitalizationStatus>;

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
                if let (InitalizationStatus::Init { addresses }, InitalizationStatus::Uninit)
                | (InitalizationStatus::Uninit, InitalizationStatus::Init { addresses }) =
                    (merged.get(id).unwrap(), value2.get(id).unwrap())
                {
                    merged
                        .insert(
                            id.clone(),
                            InitalizationStatus::MaybeInit {
                                addresses: addresses.clone(),
                            },
                        )
                        .unwrap();
                } else {
                    merged.insert(id.clone(), status.clone()).unwrap();
                }
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
                    if let Some(InitalizationStatus::Uninit) = value.get(id) {
                        let mut updated_value = value.clone();
                        let mut hs = HashSet::new();
                        hs.insert(def.tid.clone());
                        updated_value
                            .insert(id.clone(), InitalizationStatus::Init { addresses: hs });
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
