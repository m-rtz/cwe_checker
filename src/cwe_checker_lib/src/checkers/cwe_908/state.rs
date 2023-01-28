use std::collections::HashMap;

use crate::abstract_domain::{AbstractIdentifier, MemRegion};

use super::init_status::InitializationStatus;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct State {
    pub tracked_objects: HashMap<AbstractIdentifier, MemRegion<InitializationStatus>>,
}

impl State {
    pub fn new() -> State {
        State {
            tracked_objects: HashMap::new(),
        }
    }
    pub fn insert_single_offset(
        mut self,
        id: &AbstractIdentifier,
        offset: i64,
        status: InitializationStatus,
    ) {
        if let Some(mem_region) = self.tracked_objects.get_mut(id) {
            mem_region.insert_at_byte_index(status, offset)
        }
    }
    pub fn intersects(&self, other: &State) -> bool {
        self.tracked_objects
            .keys()
            .any(|x| other.tracked_objects.contains_key(x))
    }
    pub fn get_intersecting_objects<'a>(
        &'a self,
        other: &'a State,
    ) -> Vec<(
        &AbstractIdentifier,
        (
            &MemRegion<InitializationStatus>,
            &MemRegion<InitializationStatus>,
        ),
    )> {
        let mut intersection = vec![];
        for (id, self_mem_region) in self.tracked_objects.iter() {
            if let Some(other_mem_region) = other.tracked_objects.get(id) {
                intersection.push((id, (self_mem_region, other_mem_region)))
            }
        }
        return intersection;
    }
}
