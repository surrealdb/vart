use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// Represents a leaf value tuple containing (version, timestamp, value reference)
pub(crate) type LeafTuple<'a, V> = (u64, u64, &'a V);

#[derive(Clone, Copy, Debug)]
pub enum LeavesType {
    BTree,
    Vector,
}

#[derive(Clone, Debug)]
enum InternalLeafValue<V: Clone> {
    BTree { value: V, ts: u64 },
    Vector { value: V, version: u64, ts: u64 },
}

impl<V: Clone> InternalLeafValue<V> {
    fn get_value(&self) -> &V {
        match self {
            InternalLeafValue::BTree { value, .. } => value,
            InternalLeafValue::Vector { value, .. } => value,
        }
    }

    fn get_ts(&self) -> u64 {
        match self {
            InternalLeafValue::BTree { ts, .. } => *ts,
            InternalLeafValue::Vector { ts, .. } => *ts,
        }
    }

    fn get_version(&self) -> u64 {
        match self {
            InternalLeafValue::BTree { ts, .. } => *ts,
            InternalLeafValue::Vector { version, .. } => *version,
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
        }
    }

    fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        match self {
            Leaves::BTree(storage) => storage.insert_mut(value, version, ts),
            Leaves::Vector(storage) => storage.insert_mut(value, version, ts),
        }
    }

    fn clear(&mut self) {
        match self {
            Leaves::BTree(storage) => storage.clear(),
            Leaves::Vector(storage) => storage.clear(),
        }
    }

    fn get_latest_leaf(&self) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.get_latest_leaf(),
            Leaves::Vector(storage) => storage.get_latest_leaf(),
        }
    }

    fn get_leaf_by_version(&self, version: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.get_leaf_by_version(version),
            Leaves::Vector(storage) => storage.get_leaf_by_version(version),
        }
    }

    fn get_leaf_by_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.get_leaf_by_ts(ts),
            Leaves::Vector(storage) => storage.get_leaf_by_ts(ts),
        }
    }

    fn last_less_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.last_less_than_ts(ts),
            Leaves::Vector(storage) => storage.last_less_than_ts(ts),
        }
    }

    fn first_greater_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.first_greater_than_ts(ts),
            Leaves::Vector(storage) => storage.first_greater_than_ts(ts),
        }
    }

    fn first_greater_or_equal_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        match self {
            Leaves::BTree(storage) => storage.first_greater_or_equal_ts(ts),
            Leaves::Vector(storage) => storage.first_greater_or_equal_ts(ts),
        }
    }

    fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        match self {
            Leaves::BTree(storage) => storage.get_all_versions(),
            Leaves::Vector(storage) => storage.get_all_versions(),
        }
    }

    fn iter(&self) -> Box<dyn DoubleEndedIterator<Item = LeafTuple<'_, V>> + '_> {
        match self {
            Leaves::BTree(storage) => Box::new(storage.iter()),
            Leaves::Vector(storage) => Box::new(storage.iter()),
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
pub(crate) enum Leaves<V: Clone> {
    BTree(BTree<V>),
    Vector(Vector<V>),
}
