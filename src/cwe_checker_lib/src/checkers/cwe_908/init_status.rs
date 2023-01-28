use std::collections::HashSet;

use crate::abstract_domain::TryToInterval;
use crate::{
    abstract_domain::{AbstractDomain, HasTop, IntervalDomain, MemRegion, SizedDomain},
    intermediate_representation::{ByteSize, Tid},
};
use itertools::Itertools;

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