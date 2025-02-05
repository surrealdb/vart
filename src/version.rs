use std::sync::Arc;

#[cfg(feature = "btree_storage")]
use std::collections::{BTreeMap, BTreeSet};

// LeafValue implementations for both storage types
#[cfg(feature = "btree_storage")]
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub(crate) struct LeafValue<V: Clone> {
    pub(crate) value: V,
    pub(crate) ts: u64,
}

#[cfg(feature = "vector_storage")]
// Timestamp-Version Ordering Constraint Explanation:
// Given two internal keys associated with the same user key, represented as:
// (key, version1, ts1) and (key, version2, ts2),
// the following ordering constraints apply:
//      - If version1 < version2, then it must be that ts1 <= ts2.
//      - If ts1 < ts2, then it must be that version1 < version2.
// This ensures a consistent ordering of versions based on their timestamps.
//
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub(crate) struct LeafValue<V: Clone> {
    pub(crate) value: V,
    pub(crate) version: u64,
    pub(crate) ts: u64,
}

impl<V: Clone> LeafValue<V> {
    #[cfg(feature = "btree_storage")]
    pub(crate) fn new(value: V, ts: u64) -> Self {
        LeafValue { value, ts }
    }

    #[cfg(feature = "vector_storage")]
    pub(crate) fn new(value: V, version: u64, ts: u64) -> Self {
        LeafValue { value, version, ts }
    }
}

// Storage implementations
#[cfg(feature = "btree_storage")]
#[derive(Clone)]
pub(crate) struct BTreeStorage<V: Clone> {
    values: BTreeMap<u64, Arc<LeafValue<V>>>, // version -> (value, ts),
    ts_index: BTreeMap<u64, BTreeSet<u64>>,   // timestamp -> set of versions
}

#[cfg(feature = "vector_storage")]
#[derive(Clone)]
pub(crate) struct VecStorage<V: Clone> {
    values: Vec<Arc<LeafValue<V>>>,
}

// Storage trait to define common operations
pub(crate) trait Storage<V: Clone>: Clone {
    type LeafRef<'a>: Copy
    where
        Self: 'a,
        V: 'a;
    type Iterator<'a>: DoubleEndedIterator<Item = (u64, &'a Arc<LeafValue<V>>)>
    where
        Self: 'a,
        V: 'a;

    fn new() -> Self;
    fn insert_mut(&mut self, value: V, version: u64, ts: u64);
    fn insert_common(&mut self, value: V, version: u64, ts: u64);
    fn clear(&mut self);
    fn get_latest_leaf(&self) -> Self::LeafRef<'_>;
    fn get_leaf_by_version(&self, version: u64) -> Self::LeafRef<'_>;
    fn get_leaf_by_ts(&self, ts: u64) -> Self::LeafRef<'_>;
    fn last_less_than_ts(&self, ts: u64) -> Self::LeafRef<'_>;
    fn first_greater_than_ts(&self, ts: u64) -> Self::LeafRef<'_>;
    fn first_greater_or_equal_ts(&self, ts: u64) -> Self::LeafRef<'_>;
    fn get_all_versions(&self) -> Vec<(V, u64, u64)>;
    fn iter(&self) -> Self::Iterator<'_>;
}

#[cfg(feature = "btree_storage")]
impl<V: Clone> Storage<V> for BTreeStorage<V> {
    type LeafRef<'a>
        = Option<(u64, &'a Arc<LeafValue<V>>)>
    where
        V: 'a;
    type Iterator<'a>
        = BTreeStorageIterator<'a, V>
    where
        V: 'a;

    fn new() -> Self {
        BTreeStorage {
            values: BTreeMap::new(),
            ts_index: BTreeMap::new(),
        }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        self.insert_common(value, version, ts);
    }

    fn insert_common(&mut self, value: V, version: u64, ts: u64) {
        let new_leaf_value = Arc::new(LeafValue::new(value, ts));
        self.ts_index.entry(ts).or_default().insert(version);
        self.values.insert(version, new_leaf_value);
    }

    fn clear(&mut self) {
        self.values.clear();
        self.ts_index.clear();
    }

    fn get_latest_leaf(&self) -> Self::LeafRef<'_> {
        self.values.iter().next_back().map(|(k, v)| (*k, v))
    }

    fn get_leaf_by_version(&self, version: u64) -> Self::LeafRef<'_> {
        self.values
            .range(..=version)
            .next_back()
            .map(|(k, v)| (*k, v))
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Self::LeafRef<'_> {
        self.ts_index
            .range(..=ts)
            .next_back()
            .and_then(|(_, versions)| {
                versions
                    .iter()
                    .next_back()
                    .and_then(|version| self.values.get(version).map(|value| (*version, value)))
            })
    }

    fn last_less_than_ts(&self, ts: u64) -> Self::LeafRef<'_> {
        self.ts_index
            .range(..ts)
            .next_back()
            .and_then(|(_, versions)| {
                versions
                    .iter()
                    .next_back()
                    .and_then(|version| self.values.get(version).map(|value| (*version, value)))
            })
    }

    fn first_greater_than_ts(&self, ts: u64) -> Self::LeafRef<'_> {
        self.ts_index
            .range((ts + 1)..)
            .next()
            .and_then(|(_, versions)| {
                versions
                    .iter()
                    .next()
                    .and_then(|version| self.values.get(version).map(|value| (*version, value)))
            })
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Self::LeafRef<'_> {
        self.ts_index.range(ts..).next().and_then(|(_, versions)| {
            versions
                .iter()
                .next()
                .and_then(|version| self.values.get(version).map(|value| (*version, value)))
        })
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        self.values
            .iter()
            .map(|(version, leaf)| (leaf.value.clone(), *version, leaf.ts))
            .collect()
    }

    fn iter(&self) -> Self::Iterator<'_> {
        BTreeStorageIterator {
            iter: self.values.iter(),
        }
    }
}

#[cfg(feature = "vector_storage")]
impl<V: Clone> Storage<V> for VecStorage<V> {
    type LeafRef<'a>
        = Option<(u64, &'a Arc<LeafValue<V>>)>
    where
        V: 'a;
    type Iterator<'a>
        = VecStorageIterator<'a, V>
    where
        V: 'a;

    fn new() -> Self {
        VecStorage { values: Vec::new() }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        self.insert_common(value, version, ts);
    }

    fn insert_common(&mut self, value: V, version: u64, ts: u64) {
        let new_leaf_value = LeafValue::new(value, version, ts);
        match self.values.binary_search_by(|v| v.version.cmp(&version)) {
            Ok(index) => {
                if self.values[index].ts == ts {
                    self.values[index] = Arc::new(new_leaf_value);
                } else {
                    let mut insert_position = index;
                    if self.values[index].ts < ts {
                        insert_position += self.values[index..]
                            .iter()
                            .take_while(|v| v.ts <= ts)
                            .count();
                    } else {
                        insert_position -= self.values[..index]
                            .iter()
                            .rev()
                            .take_while(|v| v.ts >= ts)
                            .count();
                    }
                    self.values
                        .insert(insert_position, Arc::new(new_leaf_value));
                }
            }
            Err(index) => {
                self.values.insert(index, Arc::new(new_leaf_value));
            }
        }
    }

    fn clear(&mut self) {
        self.values.clear();
    }

    fn get_latest_leaf(&self) -> Self::LeafRef<'_> {
        self.values
            .iter()
            .max_by_key(|value| value.version)
            .map(|value| (value.version, value))
    }

    fn get_leaf_by_version(&self, version: u64) -> Self::LeafRef<'_> {
        self.values
            .iter()
            .filter(|value| value.version <= version)
            .max_by_key(|value| value.version)
            .map(|value| (value.version, value))
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Self::LeafRef<'_> {
        self.values
            .iter()
            .filter(|value| value.ts <= ts)
            .max_by_key(|value| value.ts)
            .map(|value| (value.version, value))
    }

    fn last_less_than_ts(&self, ts: u64) -> Self::LeafRef<'_> {
        self.values
            .iter()
            .filter(|value| value.ts < ts)
            .max_by_key(|value| value.ts)
            .map(|value| (value.version, value))
    }

    fn first_greater_than_ts(&self, ts: u64) -> Self::LeafRef<'_> {
        self.values
            .iter()
            .filter(|value| value.ts > ts)
            .min_by_key(|value| value.ts)
            .map(|value| (value.version, value))
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Self::LeafRef<'_> {
        self.values
            .iter()
            .filter(|value| value.ts >= ts)
            .min_by_key(|value| value.ts)
            .map(|value| (value.version, value))
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        self.values
            .iter()
            .map(|value| (value.value.clone(), value.version, value.ts))
            .collect()
    }

    fn iter(&self) -> Self::Iterator<'_> {
        VecStorageIterator {
            values: &self.values,
            position: 0,
        }
    }
}

// Iterator implementations
#[cfg(feature = "btree_storage")]
pub(crate) struct BTreeStorageIterator<'a, V: Clone> {
    iter: std::collections::btree_map::Iter<'a, u64, Arc<LeafValue<V>>>,
}

#[cfg(feature = "btree_storage")]
impl<'a, V: Clone> Iterator for BTreeStorageIterator<'a, V> {
    type Item = (u64, &'a Arc<LeafValue<V>>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (*k, v))
    }
}

#[cfg(feature = "btree_storage")]
impl<V: Clone> DoubleEndedIterator for BTreeStorageIterator<'_, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, v)| (*k, v))
    }
}

#[cfg(feature = "vector_storage")]
pub(crate) struct VecStorageIterator<'a, V: Clone> {
    values: &'a Vec<Arc<LeafValue<V>>>,
    position: usize,
}

#[cfg(feature = "vector_storage")]
impl<'a, V: Clone> Iterator for VecStorageIterator<'a, V> {
    type Item = (u64, &'a Arc<LeafValue<V>>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.values.len() {
            let value = &self.values[self.position];
            self.position += 1;
            Some((value.version, value))
        } else {
            None
        }
    }
}

#[cfg(feature = "vector_storage")]
impl<'a, V: Clone> DoubleEndedIterator for VecStorageIterator<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.position < self.values.len() {
            let value = &self.values[self.values.len() - 1 - self.position];
            self.position += 1;
            Some((value.version, value))
        } else {
            None
        }
    }
}
