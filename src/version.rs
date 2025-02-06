use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// Represents a leaf value tuple containing (version, timestamp, value reference)
pub(crate) type LeafTuple<'a, V> = (u64, u64, &'a V);

#[derive(Clone)]
pub(crate) enum Leaves<V: Clone> {
    BTree(BTree<V>),
    Vector(Vector<V>),
    Single(Single<V>),
}

#[derive(Clone, Copy, Debug)]
pub enum LeavesType {
    BTree,
    Vector,
    Single,
}

#[derive(Clone, Debug)]
enum InternalLeafValue<V: Clone> {
    BTree { value: V, ts: u64 },
    Vector { value: V, version: u64, ts: u64 },
    Single { value: V, version: u64, ts: u64 },
}

impl<V: Clone> InternalLeafValue<V> {
    fn get_value(&self) -> &V {
        match self {
            InternalLeafValue::BTree { value, .. } => value,
            InternalLeafValue::Vector { value, .. } => value,
            InternalLeafValue::Single { value, .. } => value,
        }
    }

    fn get_ts(&self) -> u64 {
        match self {
            InternalLeafValue::BTree { ts, .. } => *ts,
            InternalLeafValue::Vector { ts, .. } => *ts,
            InternalLeafValue::Single { ts, .. } => *ts,
        }
    }

    fn get_version(&self) -> u64 {
        match self {
            InternalLeafValue::BTree { ts, .. } => *ts,
            InternalLeafValue::Vector { version, .. } => *version,
            InternalLeafValue::Single { version, .. } => *version,
        }
    }
}

pub(crate) trait LeavesTrait<V: Clone>: Clone {
    fn new(storage_type: LeavesType) -> Self;
    fn insert_mut(&mut self, value: V, version: u64, ts: u64);
    fn clear(&mut self);
    fn get_latest_leaf(&self) -> Option<LeafTuple<'_, V>>;
    fn get_leaf_by_version(&self, version: u64) -> Option<LeafTuple<'_, V>>;
    fn get_leaf_by_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>>;
    fn last_less_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>>;
    fn first_greater_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>>;
    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>>;
    fn get_all_versions(&self) -> Vec<(V, u64, u64)>;
    fn iter(&self) -> Box<dyn DoubleEndedIterator<Item = LeafTuple<'_, V>> + '_>;
}

impl<V: Clone> LeavesTrait<V> for Leaves<V> {
    fn new(storage_type: LeavesType) -> Self {
        match storage_type {
            LeavesType::BTree => Leaves::BTree(BTree::new()),
            LeavesType::Vector => Leaves::Vector(Vector::new()),
            LeavesType::Single => Leaves::Single(Single::new()),
        }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        match self {
            Leaves::BTree(storage) => storage.insert_mut(value, version, ts),
            Leaves::Vector(storage) => storage.insert_mut(value, version, ts),
            Leaves::Single(storage) => storage.insert_mut(value, version, ts),
        }
    }

    fn clear(&mut self) {
        match self {
            Leaves::BTree(storage) => storage.clear(),
            Leaves::Vector(storage) => storage.clear(),
            Leaves::Single(storage) => storage.clear(),
        }
    }

    fn get_latest_leaf(&self) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.get_latest_leaf(),
            Leaves::Vector(storage) => storage.get_latest_leaf(),
            Leaves::Single(storage) => storage.get_latest_leaf(),
        }
    }

    fn get_leaf_by_version(&self, version: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.get_leaf_by_version(version),
            Leaves::Vector(storage) => storage.get_leaf_by_version(version),
            Leaves::Single(storage) => storage.get_leaf_by_version(version),
        }
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.get_leaf_by_ts(ts),
            Leaves::Vector(storage) => storage.get_leaf_by_ts(ts),
            Leaves::Single(storage) => storage.get_leaf_by_ts(ts),
        }
    }

    fn last_less_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.last_less_than_ts(ts),
            Leaves::Vector(storage) => storage.last_less_than_ts(ts),
            Leaves::Single(storage) => storage.last_less_than_ts(ts),
        }
    }

    fn first_greater_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.first_greater_than_ts(ts),
            Leaves::Vector(storage) => storage.first_greater_than_ts(ts),
            Leaves::Single(storage) => storage.first_greater_than_ts(ts),
        }
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.first_greater_or_equal_ts(ts),
            Leaves::Vector(storage) => storage.first_greater_or_equal_ts(ts),
            Leaves::Single(storage) => storage.first_greater_or_equal_ts(ts),
        }
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        match self {
            Leaves::BTree(storage) => storage.get_all_versions(),
            Leaves::Vector(storage) => storage.get_all_versions(),
            Leaves::Single(storage) => storage.get_all_versions(),
        }
    }

    fn iter(&self) -> Box<dyn DoubleEndedIterator<Item = LeafTuple<'_, V>> + '_> {
        match self {
            Leaves::BTree(storage) => Box::new(storage.iter()),
            Leaves::Vector(storage) => Box::new(storage.iter()),
            Leaves::Single(storage) => Box::new(storage.iter()),
        }
    }
}

#[derive(Clone)]
pub(crate) struct BTree<V: Clone> {
    values: BTreeMap<u64, Arc<InternalLeafValue<V>>>,
    ts_index: BTreeMap<u64, BTreeSet<u64>>,
}

impl<V: Clone> BTree<V> {
    fn new() -> Self {
        BTree {
            values: BTreeMap::new(),
            ts_index: BTreeMap::new(),
        }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        let leaf_value = Arc::new(InternalLeafValue::BTree { value, ts });
        self.ts_index.entry(ts).or_default().insert(version);
        self.values.insert(version, leaf_value);
    }

    fn clear(&mut self) {
        self.values.clear();
        self.ts_index.clear();
    }

    fn get_latest_leaf(&self) -> Option<LeafTuple<'_, V>> {
        self.values
            .iter()
            .next_back()
            .map(|(version, v)| (*version, v.get_ts(), v.get_value()))
    }

    fn get_leaf_by_version(&self, version: u64) -> Option<LeafTuple<'_, V>> {
        self.values
            .range(..=version)
            .next_back()
            .map(|(version, v)| (*version, v.get_ts(), v.get_value()))
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.ts_index
            .range(..=ts)
            .next_back()
            .and_then(|(_, versions)| {
                versions
                    .iter()
                    .next_back()
                    .and_then(|version| Some((*version, self.values.get(version)?)))
                    .map(|(version, v)| (version, v.get_ts(), v.get_value()))
            })
    }

    fn last_less_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.ts_index
            .range(..ts)
            .next_back()
            .and_then(|(_, versions)| {
                versions
                    .iter()
                    .next_back()
                    .and_then(|version| Some((*version, self.values.get(version)?)))
                    .map(|(version, v)| (version, v.get_ts(), v.get_value()))
            })
    }

    fn first_greater_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.ts_index
            .range((ts + 1)..)
            .next()
            .and_then(|(_, versions)| {
                versions
                    .iter()
                    .next()
                    .and_then(|version| Some((*version, self.values.get(version)?)))
                    .map(|(version, v)| (version, v.get_ts(), v.get_value()))
            })
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.ts_index.range(ts..).next().and_then(|(_, versions)| {
            versions
                .iter()
                .next()
                .and_then(|version| Some((*version, self.values.get(version)?)))
                .map(|(version, v)| (version, v.get_ts(), v.get_value()))
        })
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        self.values
            .iter()
            .map(|(version, leaf)| match &**leaf {
                InternalLeafValue::BTree { value, ts } => (value.clone(), *version, *ts),
                _ => unreachable!(),
            })
            .collect()
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = LeafTuple<'_, V>> + '_ {
        self.values
            .iter()
            .map(|(version, v)| (*version, v.get_ts(), v.get_value()))
    }
}

#[derive(Clone)]
pub(crate) struct Vector<V: Clone> {
    values: Vec<Arc<InternalLeafValue<V>>>,
}

impl<V: Clone> Vector<V> {
    fn new() -> Self {
        Vector { values: Vec::new() }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        let leaf_value = Arc::new(InternalLeafValue::Vector { value, version, ts });
        match self
            .values
            .binary_search_by(|v| v.get_version().cmp(&version))
        {
            Ok(index) => {
                if self.values[index].get_ts() == ts {
                    self.values[index] = leaf_value;
                } else {
                    let insert_position = if self.values[index].get_ts() < ts {
                        index
                            + self.values[index..]
                                .iter()
                                .take_while(|v| v.get_ts() <= ts)
                                .count()
                    } else {
                        index
                            - self.values[..index]
                                .iter()
                                .rev()
                                .take_while(|v| v.get_ts() >= ts)
                                .count()
                    };
                    self.values.insert(insert_position, leaf_value);
                }
            }
            Err(index) => self.values.insert(index, leaf_value),
        }
    }

    fn clear(&mut self) {
        self.values.clear();
    }

    fn get_latest_leaf(&self) -> Option<LeafTuple<'_, V>> {
        self.values
            .iter()
            .max_by_key(|value| value.get_version())
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }

    fn get_leaf_by_version(&self, version: u64) -> Option<LeafTuple<'_, V>> {
        self.values
            .iter()
            .filter(|value| value.get_version() <= version)
            .max_by_key(|value| value.get_version())
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.values
            .iter()
            .filter(|value| value.get_ts() <= ts)
            .max_by_key(|value| value.get_ts())
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }

    fn last_less_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.values
            .iter()
            .filter(|value| value.get_ts() < ts)
            .max_by_key(|value| value.get_ts())
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }

    fn first_greater_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.values
            .iter()
            .filter(|value| value.get_ts() > ts)
            .min_by_key(|value| value.get_ts())
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.values
            .iter()
            .filter(|value| value.get_ts() >= ts)
            .min_by_key(|value| value.get_ts())
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        self.values
            .iter()
            .map(|value| match &**value {
                InternalLeafValue::Vector { value, version, ts } => (value.clone(), *version, *ts),
                _ => unreachable!(),
            })
            .collect()
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = (u64, u64, &V)> + '_ {
        self.values
            .iter()
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }
}

#[derive(Clone)]
pub(crate) struct Single<V: Clone> {
    value: Option<Arc<InternalLeafValue<V>>>,
}

impl<V: Clone> Single<V> {
    fn new() -> Self {
        Single { value: None }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        self.value = Some(Arc::new(InternalLeafValue::Single { value, version, ts }));
    }

    fn clear(&mut self) {
        self.value = None;
    }

    fn get_latest_leaf(&self) -> Option<LeafTuple<'_, V>> {
        self.value
            .as_ref()
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }

    fn get_leaf_by_version(&self, version: u64) -> Option<LeafTuple<'_, V>> {
        self.value.as_ref().and_then(|v| {
            if v.get_version() <= version {
                Some((v.get_version(), v.get_ts(), v.get_value()))
            } else {
                None
            }
        })
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.value.as_ref().and_then(|v| {
            if v.get_ts() <= ts {
                Some((v.get_version(), v.get_ts(), v.get_value()))
            } else {
                None
            }
        })
    }

    fn last_less_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.value.as_ref().and_then(|v| {
            if v.get_ts() < ts {
                Some((v.get_version(), v.get_ts(), v.get_value()))
            } else {
                None
            }
        })
    }

    fn first_greater_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.value.as_ref().and_then(|v| {
            if v.get_ts() > ts {
                Some((v.get_version(), v.get_ts(), v.get_value()))
            } else {
                None
            }
        })
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.value.as_ref().and_then(|v| {
            if v.get_ts() >= ts {
                Some((v.get_version(), v.get_ts(), v.get_value()))
            } else {
                None
            }
        })
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        self.value
            .as_ref()
            .map(|v| match &**v {
                InternalLeafValue::Single { value, version, ts } => {
                    vec![(value.clone(), *version, *ts)]
                }
                _ => unreachable!(),
            })
            .unwrap_or_default()
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = LeafTuple<'_, V>> + '_ {
        self.value
            .iter()
            .map(|v| (v.get_version(), v.get_ts(), v.get_value()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_storage_types() {
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);

            // Test empty state
            assert!(storage.get_latest_leaf().is_none());

            // Test single insert
            storage.insert_mut(42, 1, 100);
            let leaf = storage.get_latest_leaf().unwrap();
            assert_eq!(leaf.2, &42);

            // Test version query
            assert!(storage.get_leaf_by_version(0).is_none());
            assert_eq!(storage.get_leaf_by_version(1).unwrap().2, &42);
            assert_eq!(storage.get_leaf_by_version(2).unwrap().2, &42);

            // Test timestamp query
            assert!(storage.get_leaf_by_ts(50).is_none());
            assert_eq!(storage.get_leaf_by_ts(100).unwrap().2, &42);
            assert_eq!(storage.get_leaf_by_ts(150).unwrap().2, &42);

            // Test range queries
            assert!(storage.last_less_than_ts(100).is_none());
            assert_eq!(storage.first_greater_than_ts(50).unwrap().2, &42);
            assert_eq!(storage.first_greater_or_equal_ts(100).unwrap().2, &42);

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
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);
            setup_test_data(&mut storage);

            // Test get_latest_leaf
            let latest = storage.get_latest_leaf().unwrap();
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(latest, (3, 300, &3)); // Single keeps only latest
                }
                _ => {
                    assert_eq!(latest, (3, 300, &3));
                }
            }

            // Test get_leaf_by_version
            match storage_type {
                LeavesType::Single => {
                    assert!(storage.get_leaf_by_version(1).is_none()); // Single only has latest
                    assert!(storage.get_leaf_by_version(2).is_none());
                    assert_eq!(storage.get_leaf_by_version(3).unwrap(), (3, 300, &3));
                    assert_eq!(storage.get_leaf_by_version(4).unwrap(), (3, 300, &3));
                    // Future version returns latest
                }
                _ => {
                    assert_eq!(storage.get_leaf_by_version(1).unwrap(), (1, 100, &1));
                    assert_eq!(storage.get_leaf_by_version(2).unwrap(), (2, 200, &2));
                    assert_eq!(storage.get_leaf_by_version(3).unwrap(), (3, 300, &3));
                    assert_eq!(storage.get_leaf_by_version(4).unwrap(), (3, 300, &3));
                    // Future version returns latest
                }
            }

            // Test non-existent version
            assert!(storage.get_leaf_by_version(0).is_none());
        }
    }

    #[test]
    fn test_timestamp_queries() {
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);
            setup_test_data(&mut storage);

            // Test get_leaf_by_ts
            match storage_type {
                LeavesType::Single => {
                    assert!(storage.get_leaf_by_ts(100).is_none()); // Single only has latest
                    assert!(storage.get_leaf_by_ts(200).is_none());
                    assert_eq!(storage.get_leaf_by_ts(300).unwrap(), (3, 300, &3));
                    assert_eq!(storage.get_leaf_by_ts(400).unwrap(), (3, 300, &3));
                    // Future ts returns latest
                }
                _ => {
                    assert_eq!(storage.get_leaf_by_ts(100).unwrap(), (1, 100, &1));
                    assert_eq!(storage.get_leaf_by_ts(200).unwrap(), (2, 200, &2));
                    assert_eq!(storage.get_leaf_by_ts(300).unwrap(), (3, 300, &3));
                    assert_eq!(storage.get_leaf_by_ts(400).unwrap(), (3, 300, &3));
                    // Future ts returns latest
                }
            }

            // Test last_less_than_ts
            match storage_type {
                LeavesType::Single => {
                    assert!(storage.last_less_than_ts(300).is_none()); // Single only has latest
                    assert!(storage.last_less_than_ts(400).unwrap() == (3, 300, &3));
                }
                _ => {
                    assert!(storage.last_less_than_ts(100).is_none()); // Nothing before first entry
                    assert_eq!(storage.last_less_than_ts(200).unwrap(), (1, 100, &1));
                    assert_eq!(storage.last_less_than_ts(300).unwrap(), (2, 200, &2));
                    assert_eq!(storage.last_less_than_ts(400).unwrap(), (3, 300, &3));
                }
            }

            // Test first_greater_than_ts
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(storage.first_greater_than_ts(200).unwrap(), (3, 300, &3));
                    assert!(storage.first_greater_than_ts(300).is_none()); // Nothing after latest
                }
                _ => {
                    assert_eq!(storage.first_greater_than_ts(0).unwrap(), (1, 100, &1));
                    assert_eq!(storage.first_greater_than_ts(100).unwrap(), (2, 200, &2));
                    assert_eq!(storage.first_greater_than_ts(200).unwrap(), (3, 300, &3));
                    assert!(storage.first_greater_than_ts(300).is_none()); // Nothing after latest
                }
            }

            // Test first_greater_or_equal_ts
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(
                        storage.first_greater_or_equal_ts(300).unwrap(),
                        (3, 300, &3)
                    );
                    assert!(storage.first_greater_or_equal_ts(301).is_none()); // Nothing after latest
                }
                _ => {
                    assert_eq!(storage.first_greater_or_equal_ts(0).unwrap(), (1, 100, &1));
                    assert_eq!(
                        storage.first_greater_or_equal_ts(100).unwrap(),
                        (1, 100, &1)
                    );
                    assert_eq!(
                        storage.first_greater_or_equal_ts(200).unwrap(),
                        (2, 200, &2)
                    );
                    assert_eq!(
                        storage.first_greater_or_equal_ts(300).unwrap(),
                        (3, 300, &3)
                    );
                    assert!(storage.first_greater_or_equal_ts(301).is_none()); // Nothing after latest
                }
            }
        }
    }

    #[test]
    fn test_get_all_versions() {
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

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
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);
            setup_test_data(&mut storage);

            let iter_vec: Vec<_> = storage.iter().collect();
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(iter_vec.len(), 1);
                    assert_eq!(iter_vec[0], (3, 300, &3)); // Only latest version
                }
                _ => {
                    assert_eq!(iter_vec.len(), 3);
                    assert_eq!(iter_vec[0], (1, 100, &1));
                    assert_eq!(iter_vec[1], (2, 200, &2));
                    assert_eq!(iter_vec[2], (3, 300, &3));
                }
            }

            // Test reverse iteration
            let rev_iter_vec: Vec<_> = storage.iter().rev().collect();
            match storage_type {
                LeavesType::Single => {
                    assert_eq!(rev_iter_vec.len(), 1);
                    assert_eq!(rev_iter_vec[0], (3, 300, &3)); // Only latest version
                }
                _ => {
                    assert_eq!(rev_iter_vec.len(), 3);
                    assert_eq!(rev_iter_vec[0], (3, 300, &3));
                    assert_eq!(rev_iter_vec[1], (2, 200, &2));
                    assert_eq!(rev_iter_vec[2], (1, 100, &1));
                }
            }
        }
    }

    #[test]
    fn test_edge_cases() {
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

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
            assert_eq!(storage.get_latest_leaf().unwrap(), (1, 100, &42));
            assert_eq!(storage.get_leaf_by_version(1).unwrap(), (1, 100, &42));
            assert_eq!(storage.get_leaf_by_ts(100).unwrap(), (1, 100, &42));
            assert!(storage.last_less_than_ts(100).is_none());
            assert!(storage.first_greater_than_ts(100).is_none());
            assert_eq!(
                storage.first_greater_or_equal_ts(100).unwrap(),
                (1, 100, &42)
            );

            // Test clear
            storage.clear();
            assert!(storage.get_latest_leaf().is_none());
            assert_eq!(storage.get_all_versions().len(), 0);
        }
    }

    #[test]
    fn test_large_dataset() {
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

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
                    assert_eq!(storage.get_latest_leaf().unwrap(), (999, 99900, &999));

                    // Only latest version should be accessible
                    assert!(storage.get_leaf_by_version(500).is_none());
                    assert_eq!(
                        storage.get_leaf_by_version(999).unwrap(),
                        (999, 99900, &999)
                    );

                    // Only latest timestamp should be accessible
                    assert!(storage.get_leaf_by_ts(50000).is_none());
                    assert_eq!(storage.get_leaf_by_ts(99900).unwrap(), (999, 99900, &999));
                }
                _ => {
                    // Test version queries
                    assert_eq!(storage.get_latest_leaf().unwrap(), (999, 99900, &999));
                    assert_eq!(
                        storage.get_leaf_by_version(500).unwrap(),
                        (500, 50000, &500)
                    );
                    assert_eq!(
                        storage.get_leaf_by_version(999).unwrap(),
                        (999, 99900, &999)
                    );

                    // Test timestamp queries
                    assert_eq!(storage.get_leaf_by_ts(50000).unwrap(), (500, 50000, &500));
                    assert_eq!(storage.get_leaf_by_ts(99900).unwrap(), (999, 99900, &999));

                    // Test range queries
                    assert_eq!(
                        storage.last_less_than_ts(50000).unwrap(),
                        (499, 49900, &499)
                    );
                    assert_eq!(
                        storage.first_greater_than_ts(50000).unwrap(),
                        (501, 50100, &501)
                    );
                    assert_eq!(
                        storage.first_greater_or_equal_ts(50000).unwrap(),
                        (500, 50000, &500)
                    );

                    // Test iterator
                    let all_versions = storage.get_all_versions();
                    assert_eq!(all_versions.len(), 1000);
                    assert_eq!(all_versions[0], (0, 0, 0));
                    assert_eq!(all_versions[499], (499, 499, 49900));
                    assert_eq!(all_versions[999], (999, 999, 99900));

                    // Test reverse iteration
                    let rev_iter: Vec<_> = storage.iter().rev().collect();
                    assert_eq!(rev_iter[0], (999, 99900, &999));
                    assert_eq!(rev_iter[499], (500, 50000, &500));
                    assert_eq!(rev_iter[999], (0, 0, &0));
                }
            }
        }
    }

    #[test]
    fn test_non_monotonic_inserts() {
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);

            // Insert values in non-monotonic order
            storage.insert_mut(3, 3, 300);
            storage.insert_mut(1, 1, 100);
            storage.insert_mut(2, 2, 200);

            match storage_type {
                LeavesType::Single => {
                    assert_eq!(storage.get_latest_leaf().unwrap(), (2, 200, &2));
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
        let test_cases = vec![LeavesType::BTree, LeavesType::Vector, LeavesType::Single];

        for storage_type in test_cases {
            let mut storage: Leaves<i32> = Leaves::new(storage_type);

            // Test duplicate timestamps with different versions
            storage.insert_mut(1, 1, 100);
            storage.insert_mut(2, 2, 100); // Same timestamp
            storage.insert_mut(3, 3, 100); // Same timestamp

            match storage_type {
                LeavesType::Single => {
                    assert_eq!(storage.get_leaf_by_ts(100).unwrap(), (3, 100, &3));
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
                    assert_eq!(storage.get_leaf_by_version(5).unwrap(), (5, 300, &3));
                }
                _ => {
                    let leaf = storage.get_leaf_by_version(5).unwrap();
                    assert_eq!(leaf.2, &3); // Should get latest by timestamp
                }
            }

            storage.clear();

            // Test large gaps
            storage.insert_mut(1, 1, 100);
            storage.insert_mut(2, 1_000_000, u64::MAX / 2); // Large version gap
            storage.insert_mut(3, 1_000_001, u64::MAX); // Large timestamp gap

            match storage_type {
                LeavesType::Single => {
                    assert_eq!(
                        storage.get_latest_leaf().unwrap(),
                        (1_000_001, u64::MAX, &3)
                    );
                }
                _ => {
                    assert_eq!(storage.get_leaf_by_version(500_000).unwrap(), (1, 100, &1));
                    assert_eq!(storage.get_leaf_by_ts(u64::MAX / 4).unwrap(), (1, 100, &1));
                }
            }

            storage.clear();

            // Test maximum u64 values
            storage.insert_mut(1, u64::MAX - 2, 100);
            storage.insert_mut(2, u64::MAX - 1, u64::MAX - 1);
            storage.insert_mut(3, u64::MAX, u64::MAX);

            match storage_type {
                LeavesType::Single => {
                    assert_eq!(storage.get_latest_leaf().unwrap(), (u64::MAX, u64::MAX, &3));
                }
                _ => {
                    assert_eq!(storage.get_latest_leaf().unwrap(), (u64::MAX, u64::MAX, &3));
                    assert_eq!(
                        storage.get_leaf_by_version(u64::MAX - 1).unwrap(),
                        (u64::MAX - 1, u64::MAX - 1, &2)
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
                    assert_eq!(storage.get_latest_leaf().unwrap(), (3, 100, &3));
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
