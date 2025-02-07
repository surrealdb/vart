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

        let version = leaf_value.version;
        // Find the start and end of the version group
        let start = self.values.partition_point(|v| v.version < version);
        let end = self.values.partition_point(|v| v.version <= version);

        if start == end {
            // No existing entries with this version; insert at the correct position
            self.values.insert(start, leaf_value);
        } else {
            // Within the version group, find the position based on ts
            let ts = leaf_value.ts;
            let version_group = &self.values[start..end];
            match version_group.binary_search_by(|v| v.ts.cmp(&ts)) {
                Ok(pos) => {
                    // Replace existing entry with the same version and ts
                    self.values[start + pos] = leaf_value;
                }
                Err(pos) => {
                    // Insert the new entry at the correct position to maintain order
                    self.values.insert(start + pos, leaf_value);
                }
            }
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

    #[test]
    fn test_version_ordering() {
        let mut vec = Vector::new();

        // Insert out of order versions
        vec.insert_mut(1, 2, 100);
        vec.insert_mut(2, 1, 100);
        vec.insert_mut(3, 3, 100);

        // Verify versions are ordered
        let versions: Vec<_> = vec.values.iter().map(|v| v.version).collect();
        assert_eq!(versions, vec![1, 2, 3]);
    }

    #[test]
    fn test_timestamp_ordering_within_version() {
        let mut vec = Vector::new();

        // Insert same version with different timestamps out of order
        vec.insert_mut(1, 1, 200);
        vec.insert_mut(2, 1, 100);
        vec.insert_mut(3, 1, 150);

        // Check values are ordered by timestamp within version 1
        let timestamps: Vec<_> = vec.values.iter().map(|v| v.ts).collect();
        assert_eq!(timestamps, vec![100, 150, 200]);
    }

    #[test]
    fn test_mixed_ordering() {
        let mut vec = Vector::new();

        // Mix of versions and timestamps
        vec.insert_mut(1, 1, 200); // version 1, late ts
        vec.insert_mut(2, 2, 100); // version 2, early ts
        vec.insert_mut(3, 1, 100); // version 1, early ts

        let values: Vec<_> = vec.values.iter().map(|v| v.value).collect();
        assert_eq!(values, vec![3, 1, 2]); // Ordered by version first, then ts
    }

    #[test]
    fn test_replace_exact_match() {
        let mut vec = Vector::new();

        // Insert initial value
        vec.insert_mut(1, 1, 100);
        // Replace with same version and timestamp
        vec.insert_mut(2, 1, 100);

        assert_eq!(vec.values.len(), 1);
        assert_eq!(vec.values[0].value, 2);
    }

    #[test]
    fn test_multiple_versions() {
        let mut vec = Vector::new();

        // Insert multiple entries for each version
        vec.insert_mut(1, 1, 100);
        vec.insert_mut(2, 1, 200);
        vec.insert_mut(3, 2, 150);
        vec.insert_mut(4, 2, 250);

        let version_groups: Vec<_> = vec.values.iter().map(|v| (v.version, v.ts)).collect();

        assert_eq!(version_groups, vec![(1, 100), (1, 200), (2, 150), (2, 250)]);
    }

    #[test]
    fn test_insert_between_existing() {
        let mut vec = Vector::new();

        vec.insert_mut(1, 1, 100);
        vec.insert_mut(2, 1, 300);
        vec.insert_mut(3, 1, 200); // Should insert between the two

        let timestamps: Vec<_> = vec.values.iter().map(|v| v.ts).collect();
        assert_eq!(timestamps, vec![100, 200, 300]);
    }

    #[test]
    fn test_edge_case_orderings() {
        let mut vec = Vector::new();

        // Test edge cases:
        // 1. Multiple entries with same version, increasing timestamps
        vec.insert_mut(1, 1, 100);
        vec.insert_mut(2, 1, 101);
        vec.insert_mut(3, 1, 102);

        // 2. Multiple entries with same version, decreasing timestamps
        vec.insert_mut(4, 2, 103);
        vec.insert_mut(5, 2, 102);
        vec.insert_mut(6, 2, 101);

        // 3. Same timestamp, different versions
        vec.insert_mut(7, 3, 100);
        vec.insert_mut(8, 4, 100);
        vec.insert_mut(9, 5, 100);

        // 4. Interleaved versions and timestamps
        vec.insert_mut(10, 6, 102);
        vec.insert_mut(11, 6, 101);
        vec.insert_mut(12, 7, 101);
        vec.insert_mut(13, 7, 102);

        // Verify the final ordering
        let entries: Vec<_> = vec
            .values
            .iter()
            .map(|v| (v.version, v.ts, v.value))
            .collect();

        assert_eq!(
            entries,
            vec![
                (1, 100, 1),
                (1, 101, 2),
                (1, 102, 3),
                (2, 101, 6),
                (2, 102, 5),
                (2, 103, 4),
                (3, 100, 7),
                (4, 100, 8),
                (5, 100, 9),
                (6, 101, 11),
                (6, 102, 10),
                (7, 101, 12),
                (7, 102, 13),
            ]
        );
    }

    #[test]
    fn test_boundary_value_ordering() {
        let mut vec = Vector::new();

        // Test boundary values for timestamps and versions
        vec.insert_mut(1, 0, 0); // Minimum values
        vec.insert_mut(2, u64::MAX, 0); // Max version, min ts
        vec.insert_mut(3, 0, u64::MAX); // Min version, max ts
        vec.insert_mut(4, u64::MAX, u64::MAX); // Maximum values

        let entries: Vec<_> = vec.values.iter().map(|v| (v.version, v.ts)).collect();

        assert_eq!(
            entries,
            vec![(0, 0), (0, u64::MAX), (u64::MAX, 0), (u64::MAX, u64::MAX),]
        );
    }

    #[test]
    fn test_sparse_dense_ordering() {
        let mut vec = Vector::new();

        // Test sparse vs dense version numbers
        vec.insert_mut(1, 1, 100);
        vec.insert_mut(2, 1000, 100); // Sparse
        vec.insert_mut(3, 1001, 100); // Dense after sparse
        vec.insert_mut(4, 2, 100); // Dense after initial
        vec.insert_mut(5, 999, 100); // Fill gap

        let versions: Vec<_> = vec.values.iter().map(|v| v.version).collect();

        assert_eq!(versions, vec![1, 2, 999, 1000, 1001]);
    }

    #[test]
    fn test_duplicate_handling() {
        let mut vec = Vector::new();

        // Insert same version+ts multiple times
        vec.insert_mut(1, 1, 100);
        vec.insert_mut(2, 1, 100); // Should replace
        vec.insert_mut(3, 1, 100); // Should replace again

        assert_eq!(vec.values.len(), 1);
        assert_eq!(vec.values[0].value, 3);

        // Verify ordering isn't affected by duplicates
        vec.insert_mut(4, 1, 99);
        vec.insert_mut(5, 1, 101);

        let entries: Vec<_> = vec.values.iter().map(|v| (v.ts, v.value)).collect();

        assert_eq!(entries, vec![(99, 4), (100, 3), (101, 5),]);
    }
}
