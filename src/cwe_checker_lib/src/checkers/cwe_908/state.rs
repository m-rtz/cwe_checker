use super::init_status::InitializationStatus;
use crate::{
    abstract_domain::{AbstractIdentifier, MemRegion},
    intermediate_representation::ByteSize,
};
use std::collections::HashMap;

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
    pub fn new_with_id(id: AbstractIdentifier, address_bytesize: ByteSize) -> State {
        let mut state = State::new();
        state
            .tracked_objects
            .insert(id, MemRegion::new(address_bytesize));
        state
    }
    /// Inserts `status` at specific offset in a **tracked** memory object.
    pub fn insert_single_offset(
        &mut self,
        id: &AbstractIdentifier,
        offset: i64,
        status: InitializationStatus,
    ) {
        if let Some(mem_region) = self.tracked_objects.get_mut(id) {
            mem_region.insert_at_byte_index(status, offset)
        }
    }
    pub fn merge_sigle_offset(
        &mut self,
        id: &AbstractIdentifier,
        offset: i64,
        status: &InitializationStatus,
    ) {
        if let Some(mem_region) = self.tracked_objects.get_mut(id) {
            mem_region.merge_at_byte_index(offset, status);
        }
    }

    pub fn merge_precise_single_offset(
        &mut self,
        id: &AbstractIdentifier,
        offset: i64,
        status: &InitializationStatus,
    ) {
        if let Some(mem_region) = self.tracked_objects.get_mut(id) {
            mem_region.merge_precise_at_byte_index(offset, status);
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
    ) -> Option<
        Vec<(
            &AbstractIdentifier,
            (
                &MemRegion<InitializationStatus>,
                &MemRegion<InitializationStatus>,
            ),
        )>,
    > {
        let mut intersection = vec![];
        for (id, self_mem_region) in self.tracked_objects.iter() {
            if let Some(other_mem_region) = other.tracked_objects.get(id) {
                intersection.push((id, (self_mem_region, other_mem_region)))
            }
        }
        if intersection.is_empty() {
            return None;
        }
        Some(intersection)
    }
}
