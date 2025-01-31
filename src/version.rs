use std::sync::Arc;

#[derive(Clone)]
pub(crate) enum Leaves<V: Clone> {
    Vector(Vector<V>),
    Single(Single<V>),
}

#[derive(Clone, Copy, Debug)]
pub enum LeavesType {
    Vector,
    Single,
}

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

#[allow(unused)]
pub(crate) trait LeavesTrait<V: Clone>: Clone {
    type Iter<'a>: DoubleEndedIterator<Item = &'a Arc<LeafValue<V>>> + 'a
    where
        Self: 'a,
        V: 'a;

    fn new(storage_type: LeavesType) -> Self;
    fn insert_mut(&mut self, value: V, version: u64, ts: u64);
    fn clear(&mut self);
    fn get_latest_leaf(&self) -> Option<&Arc<LeafValue<V>>>;
    fn get_leaf_by_version(&self, version: u64) -> Option<&Arc<LeafValue<V>>>;
    fn get_leaf_by_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>>;
    fn last_less_than_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>>;
    fn first_greater_than_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>>;
    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>>;
    fn get_all_versions(&self) -> Vec<(V, u64, u64)>;
    fn iter(&self) -> Self::Iter<'_>;
}

impl<V: Clone> LeavesTrait<V> for Leaves<V> {
    type Iter<'a>
        = Box<dyn DoubleEndedIterator<Item = &'a Arc<LeafValue<V>>> + 'a>
    where
        Self: 'a;

    fn new(storage_type: LeavesType) -> Self {
        match storage_type {
            LeavesType::Vector => Leaves::Vector(Vector::new()),
            LeavesType::Single => Leaves::Single(Single::new()),
        }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        match self {
            Leaves::Vector(storage) => storage.insert_mut(value, version, ts),
            Leaves::Single(storage) => storage.insert_mut(value, version, ts),
        }
    }

    fn clear(&mut self) {
        match self {
            Leaves::Vector(storage) => storage.clear(),
            Leaves::Single(storage) => storage.clear(),
        }
    }

    fn get_latest_leaf(&self) -> Option<&Arc<LeafValue<V>>> {
        match self {
            Leaves::Vector(storage) => storage.get_latest_leaf(),
            Leaves::Single(storage) => storage.get_latest_leaf(),
        }
    }

    fn get_leaf_by_version(&self, version: u64) -> Option<&Arc<LeafValue<V>>> {
        match self {
            Leaves::Vector(storage) => storage.get_leaf_by_version(version),
            Leaves::Single(storage) => storage.get_leaf_by_version(version),
        }
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        match self {
            Leaves::Vector(storage) => storage.get_leaf_by_ts(ts),
            Leaves::Single(storage) => storage.get_leaf_by_ts(ts),
        }
    }

    fn last_less_than_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        match self {
            Leaves::Vector(storage) => storage.last_less_than_ts(ts),
            Leaves::Single(storage) => storage.last_less_than_ts(ts),
        }
    }

    fn first_greater_than_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        match self {
            Leaves::Vector(storage) => storage.first_greater_than_ts(ts),
            Leaves::Single(storage) => storage.first_greater_than_ts(ts),
        }
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        match self {
            Leaves::Vector(storage) => storage.first_greater_or_equal_ts(ts),
            Leaves::Single(storage) => storage.first_greater_or_equal_ts(ts),
        }
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        match self {
            Leaves::Vector(storage) => storage.get_all_versions(),
            Leaves::Single(storage) => storage.get_all_versions(),
        }
    }

    fn iter(&self) -> Self::Iter<'_> {
        match self {
            Leaves::Vector(storage) => Box::new(storage.iter()),
            Leaves::Single(storage) => Box::new(storage.iter()),
        }
    }
}

#[derive(Clone)]
pub(crate) struct Vector<V: Clone> {
    values: Vec<Arc<LeafValue<V>>>,
}

impl<V: Clone> Vector<V> {
    fn new() -> Self {
        Vector { values: Vec::new() }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        let leaf_value = Arc::new(LeafValue { value, version, ts });

        // Check if a LeafValue with the same version exists and update or insert accordingly
        match self.values.binary_search_by(|v| v.version.cmp(&version)) {
            Ok(index) => {
                // If an entry with the same version and timestamp exists, just put the same value
                if self.values[index].ts == ts {
                    self.values[index] = leaf_value;
                } else {
                    // If an entry with the same version and different timestamp exists, add a new entry
                    // Determine the direction to scan based on the comparison of timestamps

                    // Scan forward to find the first entry with a timestamp greater than the new entry's timestamp
                    let insert_position = if self.values[index].ts < ts {
                        index
                            + self.values[index..]
                                .iter()
                                .take_while(|v| v.ts <= ts)
                                .count()
                    } else {
                        // Scan backward to find the insertion point before the first entry with a timestamp less than the new entry's timestamp
                        index
                            - self.values[..index]
                                .iter()
                                .rev()
                                .take_while(|v| v.ts >= ts)
                                .count()
                    };
                    self.values.insert(insert_position, leaf_value);
                }
            }
            Err(index) => self.values.insert(index, leaf_value),
        }
    }

    #[allow(unused)]
    fn clear(&mut self) {
        self.values.clear();
    }

    fn get_latest_leaf(&self) -> Option<&Arc<LeafValue<V>>> {
        self.values.iter().max_by_key(|value| value.version)
    }

    fn get_leaf_by_version(&self, version: u64) -> Option<&Arc<LeafValue<V>>> {
        self.values
            .iter()
            .filter(|value| value.version <= version)
            .max_by_key(|value| value.version)
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        self.values
            .iter()
            .filter(|value| value.ts <= ts)
            .max_by_key(|value| value.ts)
    }

    fn last_less_than_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        self.values
            .iter()
            .filter(|value| value.ts < ts)
            .max_by_key(|value| value.ts)
    }

    fn first_greater_than_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        self.values
            .iter()
            .filter(|value| value.ts > ts)
            .min_by_key(|value| value.ts)
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        self.values
            .iter()
            .filter(|value| value.ts >= ts)
            .min_by_key(|value| value.ts)
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        self.values
            .iter()
            .map(|value| (value.value.clone(), value.version, value.ts))
            .collect()
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = &Arc<LeafValue<V>>> + '_ {
        self.values.iter()
    }
}

#[derive(Clone)]
pub(crate) struct Single<V: Clone> {
    value: Option<Arc<LeafValue<V>>>,
}

impl<V: Clone> Single<V> {
    fn new() -> Self {
        Single { value: None }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        // Only replace if the provided value is more recent than
        // the existing ones. This is important because this method
        // is used for loading the index in SurrealKV and thus must
        // be able to handle segments left by an unfinished compaction
        // where older versions can end up in more recent segments
        // after the newer versions.
        if version > self.value.as_ref().map_or(0, |v| v.version) {
            self.value = Some(Arc::new(LeafValue { value, version, ts }));
        }
    }

    #[allow(unused)]
    fn clear(&mut self) {
        self.value = None;
    }

    fn get_latest_leaf(&self) -> Option<&Arc<LeafValue<V>>> {
        self.value.as_ref()
    }

    fn get_leaf_by_version(&self, version: u64) -> Option<&Arc<LeafValue<V>>> {
        self.value
            .as_ref()
            .and_then(|v| if v.version <= version { Some(v) } else { None })
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        self.value
            .as_ref()
            .and_then(|v| if v.ts <= ts { Some(v) } else { None })
    }

    fn last_less_than_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        self.value
            .as_ref()
            .and_then(|v| if v.ts < ts { Some(v) } else { None })
    }

    fn first_greater_than_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        self.value
            .as_ref()
            .and_then(|v| if v.ts > ts { Some(v) } else { None })
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        self.value
            .as_ref()
            .and_then(|v| if v.ts >= ts { Some(v) } else { None })
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        self.value
            .as_ref()
            .map(|v| vec![(v.value.clone(), v.version, v.ts)])
            .unwrap_or_default()
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = &Arc<LeafValue<V>>> + '_ {
        self.value.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_storage_types() {
        let test_cases = vec![LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);

            // Test empty state
            assert!(storage.get_latest_leaf().is_none());

            // Test single insert
            storage.insert_mut(42, 1, 100);
            let leaf = storage.get_latest_leaf().unwrap();
            assert_eq!(leaf.value, 42);

            // Test version query
            assert!(storage.get_leaf_by_version(0).is_none());
            assert_eq!(storage.get_leaf_by_version(1).unwrap().value, 42);
            assert_eq!(storage.get_leaf_by_version(2).unwrap().value, 42);

            // Test timestamp query
            assert!(storage.get_leaf_by_ts(50).is_none());
            assert_eq!(storage.get_leaf_by_ts(100).unwrap().value, 42);
            assert_eq!(storage.get_leaf_by_ts(150).unwrap().value, 42);

            // Test range queries
            assert!(storage.last_less_than_ts(100).is_none());
            assert_eq!(storage.first_greater_than_ts(50).unwrap().value, 42);
            assert_eq!(storage.first_greater_or_equal_ts(100).unwrap().value, 42);

            // Test multiple inserts
            storage.insert_mut(43, 2, 200);
            let versions = storage.get_all_versions();
            match storage_type {
                LeavesType::Single => assert_eq!(versions.len(), 1),
                _ => assert_eq!(versions.len(), 2),
            }

            // Test clear
            storage.clear();
            assert!(storage.get_latest_leaf().is_none());
        }
    }

    #[test]
    fn test_single_storage_specific() {
        let mut storage: Leaves<i32> = Leaves::new(LeavesType::Single);

        // Test that single storage only keeps the latest value
        storage.insert_mut(1, 1, 100);
        storage.insert_mut(2, 2, 200);
        storage.insert_mut(3, 3, 300);

        let versions = storage.get_all_versions();
        assert_eq!(versions.len(), 1);
        assert_eq!(versions[0].0, 3);

        // Test that older versions are not accessible
        assert!(storage.get_leaf_by_version(1).is_none());
        assert!(storage.get_leaf_by_ts(100).is_none());
    }

    fn setup_test_data(storage: &mut Leaves<i32>) {
        // Insert test data with different versions and timestamps
        // version: 1, ts: 100 - First entry
        // version: 2, ts: 200 - Middle entry
        // version: 3, ts: 300 - Latest entry
        storage.insert_mut(1, 1, 100);
        storage.insert_mut(2, 2, 200);
        storage.insert_mut(3, 3, 300);
    }

    #[test]
    fn test_version_queries() {
        let test_cases = vec![LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);
            setup_test_data(&mut storage);

            // Test get_latest_leaf
            let latest = storage.get_latest_leaf().unwrap();
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(latest.value, 3);
                    assert_eq!(latest.version, 3);
                    assert_eq!(latest.ts, 300);
                }
                _ => {
                    assert_eq!(latest.value, 3);
                    assert_eq!(latest.version, 3);
                    assert_eq!(latest.ts, 300);
                }
            }

            // Test get_leaf_by_version
            match storage_type {
                LeavesType::Single => {
                    assert!(storage.get_leaf_by_version(1).is_none()); // Single only has latest
                    assert!(storage.get_leaf_by_version(2).is_none());
                    let leaf = storage.get_leaf_by_version(3).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                    let leaf = storage.get_leaf_by_version(4).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                }
                _ => {
                    let leaf = storage.get_leaf_by_version(1).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (1, 1, 100));
                    let leaf = storage.get_leaf_by_version(2).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (2, 2, 200));
                    let leaf = storage.get_leaf_by_version(3).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                    let leaf = storage.get_leaf_by_version(4).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                }
            }

            // Test non-existent version
            assert!(storage.get_leaf_by_version(0).is_none());
        }
    }

    #[test]
    fn test_timestamp_queries() {
        let test_cases = vec![LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);
            setup_test_data(&mut storage);

            // Test get_leaf_by_ts
            match storage_type {
                LeavesType::Single => {
                    assert!(storage.get_leaf_by_ts(100).is_none()); // Single only has latest
                    assert!(storage.get_leaf_by_ts(200).is_none());
                    let leaf = storage.get_leaf_by_ts(300).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                    let leaf = storage.get_leaf_by_ts(400).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                }
                _ => {
                    let leaf = storage.get_leaf_by_ts(100).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (1, 1, 100));
                    let leaf = storage.get_leaf_by_ts(200).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (2, 2, 200));
                    let leaf = storage.get_leaf_by_ts(300).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                    let leaf = storage.get_leaf_by_ts(400).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                }
            }

            // Test last_less_than_ts
            match storage_type {
                LeavesType::Single => {
                    assert!(storage.last_less_than_ts(300).is_none()); // Single only has latest
                    let leaf = storage.last_less_than_ts(400).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                }
                _ => {
                    assert!(storage.last_less_than_ts(100).is_none()); // Nothing before first entry
                    let leaf = storage.last_less_than_ts(200).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (1, 1, 100));
                    let leaf = storage.last_less_than_ts(300).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (2, 2, 200));
                    let leaf = storage.last_less_than_ts(400).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                }
            }

            // Test first_greater_than_ts
            match storage_type {
                LeavesType::Single => {
                    let leaf = storage.first_greater_than_ts(200).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                    assert!(storage.first_greater_than_ts(300).is_none()); // Nothing after latest
                }
                _ => {
                    let leaf = storage.first_greater_than_ts(0).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (1, 1, 100));
                    let leaf = storage.first_greater_than_ts(100).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (2, 2, 200));
                    let leaf = storage.first_greater_than_ts(200).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                    assert!(storage.first_greater_than_ts(300).is_none()); // Nothing after latest
                }
            }

            // Test first_greater_or_equal_ts
            match storage_type {
                LeavesType::Single => {
                    let leaf = storage.first_greater_or_equal_ts(300).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                    assert!(storage.first_greater_or_equal_ts(301).is_none()); // Nothing after latest
                }
                _ => {
                    let leaf = storage.first_greater_or_equal_ts(0).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (1, 1, 100));
                    let leaf = storage.first_greater_or_equal_ts(100).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (1, 1, 100));
                    let leaf = storage.first_greater_or_equal_ts(200).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (2, 2, 200));
                    let leaf = storage.first_greater_or_equal_ts(300).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                    assert!(storage.first_greater_or_equal_ts(301).is_none()); // Nothing after latest
                }
            }
        }
    }

    #[test]
    fn test_get_all_versions() {
        let test_cases = vec![LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);
            setup_test_data(&mut storage);

            let versions = storage.get_all_versions();
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(versions.len(), 1);
                    assert_eq!(versions[0], (3, 3, 300)); // Only latest version
                }
                _ => {
                    assert_eq!(versions.len(), 3);
                    assert_eq!(versions[0], (1, 1, 100));
                    assert_eq!(versions[1], (2, 2, 200));
                    assert_eq!(versions[2], (3, 3, 300));
                }
            }
        }
    }

    #[test]
    fn test_iter() {
        let test_cases = vec![LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);
            setup_test_data(&mut storage);

            let iter_vec: Vec<_> = storage.iter().collect();
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(iter_vec.len(), 1);
                    let leaf = iter_vec[0];
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                }
                _ => {
                    assert_eq!(iter_vec.len(), 3);
                    assert_eq!(
                        (iter_vec[0].value, iter_vec[0].version, iter_vec[0].ts),
                        (1, 1, 100)
                    );
                    assert_eq!(
                        (iter_vec[1].value, iter_vec[1].version, iter_vec[1].ts),
                        (2, 2, 200)
                    );
                    assert_eq!(
                        (iter_vec[2].value, iter_vec[2].version, iter_vec[2].ts),
                        (3, 3, 300)
                    );
                }
            }

            // Test reverse iteration
            let rev_iter_vec: Vec<_> = storage.iter().rev().collect();
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(rev_iter_vec.len(), 1);
                    let leaf = rev_iter_vec[0];
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 300));
                }
                _ => {
                    assert_eq!(rev_iter_vec.len(), 3);
                    assert_eq!(
                        (
                            rev_iter_vec[0].value,
                            rev_iter_vec[0].version,
                            rev_iter_vec[0].ts
                        ),
                        (3, 3, 300)
                    );
                    assert_eq!(
                        (
                            rev_iter_vec[1].value,
                            rev_iter_vec[1].version,
                            rev_iter_vec[1].ts
                        ),
                        (2, 2, 200)
                    );
                    assert_eq!(
                        (
                            rev_iter_vec[2].value,
                            rev_iter_vec[2].version,
                            rev_iter_vec[2].ts
                        ),
                        (1, 1, 100)
                    );
                }
            }
        }
    }

    #[test]
    fn test_edge_cases() {
        let test_cases = vec![LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);

            // Test empty storage
            assert!(storage.get_latest_leaf().is_none());
            assert!(storage.get_leaf_by_version(1).is_none());
            assert!(storage.get_leaf_by_ts(100).is_none());
            assert!(storage.last_less_than_ts(100).is_none());
            assert!(storage.first_greater_than_ts(100).is_none());
            assert!(storage.first_greater_or_equal_ts(100).is_none());
            assert_eq!(storage.get_all_versions().len(), 0);
            assert_eq!(storage.iter().count(), 0);

            // Test single value
            storage.insert_mut(42, 1, 100);
            let leaf = storage.get_latest_leaf().unwrap();
            assert_eq!((leaf.value, leaf.version, leaf.ts), (42, 1, 100));
            let leaf = storage.get_leaf_by_version(1).unwrap();
            assert_eq!((leaf.value, leaf.version, leaf.ts), (42, 1, 100));
            let leaf = storage.get_leaf_by_ts(100).unwrap();
            assert_eq!((leaf.value, leaf.version, leaf.ts), (42, 1, 100));
            assert!(storage.last_less_than_ts(100).is_none());
            assert!(storage.first_greater_than_ts(100).is_none());
            let leaf = storage.first_greater_or_equal_ts(100).unwrap();
            assert_eq!((leaf.value, leaf.version, leaf.ts), (42, 1, 100));

            // Test clear
            storage.clear();
            assert!(storage.get_latest_leaf().is_none());
            assert_eq!(storage.get_all_versions().len(), 0);
        }
    }

    #[test]
    fn test_large_dataset() {
        let test_cases = vec![LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);

            // Insert 1000 versions with increasing timestamps
            for i in 0..1000 {
                storage.insert_mut(i, i as u64, i as u64 * 100);
            }

            match storage_type {
                LeavesType::Single => {
                    // Single storage should only have the latest value
                    assert_eq!(storage.get_all_versions().len(), 1);
                    let leaf = storage.get_latest_leaf().unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (999, 999, 99900));

                    // Only latest version should be accessible
                    assert!(storage.get_leaf_by_version(500).is_none());
                    let leaf = storage.get_leaf_by_version(999).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (999, 999, 99900));

                    // Only latest timestamp should be accessible
                    assert!(storage.get_leaf_by_ts(50000).is_none());
                    let leaf = storage.get_leaf_by_ts(99900).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (999, 999, 99900));
                }
                _ => {
                    // Test version queries
                    let leaf = storage.get_latest_leaf().unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (999, 999, 99900));
                    let leaf = storage.get_leaf_by_version(500).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (500, 500, 50000));
                    let leaf = storage.get_leaf_by_version(999).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (999, 999, 99900));

                    // Test timestamp queries
                    let leaf = storage.get_leaf_by_ts(50000).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (500, 500, 50000));
                    let leaf = storage.get_leaf_by_ts(99900).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (999, 999, 99900));

                    // Test range queries
                    let leaf = storage.last_less_than_ts(50000).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (499, 499, 49900));
                    let leaf = storage.first_greater_than_ts(50000).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (501, 501, 50100));
                    let leaf = storage.first_greater_or_equal_ts(50000).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (500, 500, 50000));

                    // Test iterator
                    let all_versions = storage.get_all_versions();
                    assert_eq!(all_versions.len(), 1000);
                    assert_eq!(all_versions[0], (0, 0, 0));
                    assert_eq!(all_versions[499], (499, 499, 49900));
                    assert_eq!(all_versions[999], (999, 999, 99900));

                    // Test reverse iteration
                    let rev_iter: Vec<_> = storage.iter().rev().collect();
                    assert_eq!(
                        (rev_iter[0].value, rev_iter[0].version, rev_iter[0].ts),
                        (999, 999, 99900)
                    );
                    assert_eq!(
                        (rev_iter[499].value, rev_iter[499].version, rev_iter[499].ts),
                        (500, 500, 50000)
                    );
                    assert_eq!(
                        (rev_iter[999].value, rev_iter[999].version, rev_iter[999].ts),
                        (0, 0, 0)
                    );
                }
            }
        }
    }

    #[test]
    fn test_non_monotonic_inserts() {
        // LeavesType::Single does not support non-monotonic inserts
        let test_cases = vec![LeavesType::Vector];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);

            // Insert values in non-monotonic order
            storage.insert_mut(3, 3, 300);
            storage.insert_mut(1, 1, 100);
            storage.insert_mut(2, 2, 200);

            match storage_type {
                LeavesType::Single => {
                    let leaf = storage.get_latest_leaf().unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (2, 2, 200));
                    assert_eq!(storage.get_all_versions().len(), 1);
                }
                _ => {
                    // Verify correct ordering
                    let versions = storage.get_all_versions();
                    assert_eq!(versions.len(), 3);
                    assert_eq!(versions[0], (1, 1, 100));
                    assert_eq!(versions[1], (2, 2, 200));
                    assert_eq!(versions[2], (3, 3, 300));
                }
            }
        }
    }

    #[test]
    fn test_with_duplicates() {
        // LeavesType::Single does not support non-monotonic or duplicate inserts
        let test_cases = vec![LeavesType::Vector];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);

            // Test duplicate timestamps with different versions
            storage.insert_mut(1, 1, 100);
            storage.insert_mut(2, 2, 100); // Same timestamp
            storage.insert_mut(3, 3, 100); // Same timestamp

            match storage_type {
                LeavesType::Single => {
                    let leaf = storage.get_leaf_by_ts(100).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 100));
                }
                _ => {
                    let versions_at_ts = storage
                        .get_all_versions()
                        .iter()
                        .filter(|(_, _, ts)| *ts == 100)
                        .count();
                    assert_eq!(versions_at_ts, 3);
                }
            }

            storage.clear();

            // Test duplicate versions with different timestamps
            storage.insert_mut(1, 5, 100);
            storage.insert_mut(2, 5, 200); // Same version
            storage.insert_mut(3, 5, 300); // Same version

            match storage_type {
                LeavesType::Single => {
                    let leaf = storage.get_leaf_by_version(5).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 5, 300));
                }
                _ => {
                    let leaf = storage.get_leaf_by_version(5).unwrap();
                    assert_eq!(leaf.value, 3); // Should get latest by timestamp
                }
            }

            storage.clear();

            // Test large gaps
            storage.insert_mut(1, 1, 100);
            storage.insert_mut(2, 1_000_000, u64::MAX / 2); // Large version gap
            storage.insert_mut(3, 1_000_001, u64::MAX); // Large timestamp gap

            match storage_type {
                LeavesType::Single => {
                    let leaf = storage.get_latest_leaf().unwrap();
                    assert_eq!(
                        (leaf.value, leaf.version, leaf.ts),
                        (3, 1_000_001, u64::MAX)
                    );
                }
                _ => {
                    let leaf = storage.get_leaf_by_version(500_000).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (1, 1, 100));
                    let leaf = storage.get_leaf_by_ts(u64::MAX / 4).unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (1, 1, 100));
                }
            }

            storage.clear();

            // Test maximum u64 values
            storage.insert_mut(1, u64::MAX - 2, 100);
            storage.insert_mut(2, u64::MAX - 1, u64::MAX - 1);
            storage.insert_mut(3, u64::MAX, u64::MAX);

            match storage_type {
                LeavesType::Single => {
                    let leaf = storage.get_latest_leaf().unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, u64::MAX, u64::MAX));
                }
                _ => {
                    let leaf = storage.get_latest_leaf().unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, u64::MAX, u64::MAX));
                    let leaf = storage.get_leaf_by_version(u64::MAX - 1).unwrap();
                    assert_eq!(
                        (leaf.value, leaf.version, leaf.ts),
                        (2, u64::MAX - 1, u64::MAX - 1)
                    );
                }
            }

            storage.clear();

            // Test non-sequential timestamp ordering with same versions
            storage.insert_mut(1, 1, 300); // Higher timestamp first
            storage.insert_mut(2, 2, 200); // Middle timestamp second
            storage.insert_mut(3, 3, 100); // Lowest timestamp last

            match storage_type {
                LeavesType::Single => {
                    let leaf = storage.get_latest_leaf().unwrap();
                    assert_eq!((leaf.value, leaf.version, leaf.ts), (3, 3, 100));
                }
                _ => {
                    let versions = storage.get_all_versions();
                    assert_eq!(versions.len(), 3);
                    // Should be ordered by version
                    assert_eq!(versions[0], (1, 1, 300));
                    assert_eq!(versions[1], (2, 2, 200));
                    assert_eq!(versions[2], (3, 3, 100));
                }
            }
        }
    }
}
