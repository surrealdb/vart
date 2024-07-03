use std::collections::{Bound, VecDeque};
use std::ops::RangeBounds;
use std::sync::Arc;

use crate::art::{Node, NodeType, QueryType};
use crate::KeyTrait;

type NodeIterator<'a, P, V> = Box<dyn Iterator<Item = (u8, &'a Arc<Node<P, V>>)> + 'a>;

/// An iterator over the nodes in the Trie.
struct NodeIter<'a, P: KeyTrait, V: Clone> {
    node: NodeIterator<'a, P, V>,
}

impl<'a, P: KeyTrait, V: Clone> NodeIter<'a, P, V> {
    /// Creates a new NodeIter instance.
    ///
    /// # Arguments
    ///
    /// * `iter` - An iterator over node items.
    ///
    fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = (u8, &'a Arc<Node<P, V>>)> + 'a,
    {
        Self {
            node: Box::new(iter),
        }
    }
}

impl<'a, P: KeyTrait, V: Clone> Iterator for NodeIter<'a, P, V> {
    type Item = (u8, &'a Arc<Node<P, V>>);

    fn next(&mut self) -> Option<Self::Item> {
        self.node.next()
    }
}

/// An iterator over key-value pairs in the Trie.
pub struct Iter<'a, P: KeyTrait + 'a, V: Clone> {
    inner: Box<dyn Iterator<Item = (Vec<u8>, &'a V, &'a u64, &'a u64)> + 'a>,
    _marker: std::marker::PhantomData<P>,
}

impl<'a, P: KeyTrait + 'a, V: Clone> Iter<'a, P, V> {
    /// Creates a new Iter instance.
    ///
    /// # Arguments
    ///
    /// * `node` - An optional reference to the root node of the Trie.
    ///
    pub(crate) fn new(node: Option<&'a Arc<Node<P, V>>>) -> Self {
        match node {
            Some(node) => Self {
                inner: Box::new(IterState::new(node, false)),
                _marker: Default::default(),
            },
            None => Self {
                inner: Box::new(std::iter::empty()),
                _marker: Default::default(),
            },
        }
    }
}

impl<'a, P: KeyTrait + 'a, V: Clone> Iterator for Iter<'a, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

/// An internal state for the Iter iterator.
struct IterState<'a, P: KeyTrait + 'a, V: Clone> {
    iters: Vec<NodeIter<'a, P, V>>,
    leafs: VecDeque<(&'a P, &'a V, &'a u64, &'a u64)>,
    is_versioned: bool,
}

impl<'a, P: KeyTrait + 'a, V: Clone> IterState<'a, P, V> {
    /// Creates a new IterState instance.
    ///
    /// # Arguments
    ///
    /// * `node` - A reference to the root node of the Trie.
    ///
    pub fn new(node: &'a Node<P, V>, is_versioned: bool) -> Self {
        let mut iters = Vec::new();
        let mut leafs = VecDeque::new();

        if let NodeType::Twig(twig) = &node.node_type {
            if is_versioned {
                for leaf in twig.iter() {
                    leafs.push_back((&twig.key, &leaf.value, &leaf.version, &leaf.ts));
                }
            } else if let Some(v) = twig.get_latest_leaf() {
                leafs.push_back((&twig.key, &v.value, &v.version, &v.ts));
            }
        } else {
            iters.push(NodeIter::new(node.iter()));
        }

        Self {
            iters,
            leafs,
            is_versioned,
        }
    }

    pub fn empty() -> Self {
        Self {
            iters: Vec::new(),
            leafs: VecDeque::new(),
            is_versioned: false,
        }
    }

    fn forward_scan<R>(node: &'a Node<P, V>, range: &R, is_versioned: bool) -> Self
    where
        R: RangeBounds<P>,
    {
        let mut leafs = VecDeque::new();
        let mut iters = Vec::new();
        if let NodeType::Twig(twig) = &node.node_type {
            if range.contains(&twig.key) {
                if is_versioned {
                    for leaf in twig.iter() {
                        leafs.push_back((&twig.key, &leaf.value, &leaf.version, &leaf.ts));
                    }
                } else if let Some(v) = twig.get_latest_leaf() {
                    leafs.push_back((&twig.key, &v.value, &v.version, &v.ts));
                }
            }
        } else {
            iters.push(NodeIter::new(node.iter()));
        }

        Self {
            iters,
            leafs,
            is_versioned,
        }
    }

    fn scan_at<R>(node: &'a Node<P, V>, range: &R, query_type: QueryType) -> Self
    where
        R: RangeBounds<P>,
    {
        let mut leafs = VecDeque::new();
        let mut iters = Vec::new();
        if let NodeType::Twig(twig) = &node.node_type {
            if range.contains(&twig.key) {
                if let Some(v) = twig.get_leaf_by_query_ref(query_type) {
                    leafs.push_back((&twig.key, &v.value, &v.version, &v.ts));
                }
            }
        } else {
            iters.push(NodeIter::new(node.iter()));
        }

        Self {
            iters,
            leafs,
            is_versioned: false,
        }
    }
}

impl<'a, P: KeyTrait + 'a, V: Clone> Iterator for IterState<'a, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.iters.last_mut() {
            let e = node.next();
            match e {
                None => {
                    self.iters.pop();
                }
                Some(other) => {
                    if let NodeType::Twig(twig) = &other.1.node_type {
                        if self.is_versioned {
                            for leaf in twig.iter() {
                                self.leafs.push_back((
                                    &twig.key,
                                    &leaf.value,
                                    &leaf.version,
                                    &leaf.ts,
                                ));
                            }
                        } else if let Some(v) = twig.get_latest_leaf() {
                            self.leafs
                                .push_back((&twig.key, &v.value, &v.version, &v.ts));
                        }
                        break;
                    } else {
                        self.iters.push(NodeIter::new(other.1.iter()));
                    }
                }
            }
        }

        self.leafs
            .pop_front()
            .map(|leaf| (leaf.0.as_slice().to_vec(), leaf.1, leaf.2, leaf.3))
    }
}

pub struct Range<'a, K: KeyTrait, V: Clone, R> {
    forward: IterState<'a, K, V>,
    range: R,
    is_versioned: bool,
}

impl<'a, K: KeyTrait, V: Clone, R> Range<'a, K, V, R>
where
    K: Ord,
    R: RangeBounds<K>,
{
    pub(crate) fn empty(range: R) -> Self {
        Self {
            forward: IterState::empty(),
            range,
            is_versioned: false,
        }
    }

    pub(crate) fn new(node: Option<&'a Arc<Node<K, V>>>, range: R) -> Self
    where
        R: RangeBounds<K>,
    {
        Self {
            forward: node.map_or_else(IterState::empty, |n| {
                IterState::forward_scan(n, &range, false)
            }),
            range,
            is_versioned: false,
        }
    }

    pub(crate) fn new_versioned(node: Option<&'a Arc<Node<K, V>>>, range: R) -> Self
    where
        R: RangeBounds<K>,
    {
        Self {
            forward: node.map_or_else(IterState::empty, |n| {
                IterState::forward_scan(n, &range, true)
            }),
            range,
            is_versioned: true,
        }
    }
}

impl<'a, K: 'a + KeyTrait, V: Clone, R: RangeBounds<K>> Iterator for Range<'a, K, V, R> {
    type Item = (Vec<u8>, &'a V, &'a u64, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.forward.iters.last_mut() {
            let e = node.next();
            match e {
                Some(other) => {
                    if let NodeType::Twig(twig) = &other.1.node_type {
                        if self.range.contains(&twig.key) {
                            // If the query is versioned, iterate over all versions of the key
                            // and add them to the leafs queue. Otherwise, add the latest version.
                            if self.is_versioned {
                                for leaf in twig.iter() {
                                    self.forward.leafs.push_back((
                                        &twig.key,
                                        &leaf.value,
                                        &leaf.version,
                                        &leaf.ts,
                                    ));
                                }
                            } else if let Some(v) = twig.get_latest_leaf() {
                                self.forward
                                    .leafs
                                    .push_back((&twig.key, &v.value, &v.version, &v.ts));
                            }
                            break;
                        } else {
                            match self.range.end_bound() {
                                Bound::Included(k) if &twig.key > k => self.forward.iters.clear(),
                                Bound::Excluded(k) if &twig.key >= k => self.forward.iters.clear(),
                                _ => {}
                            }
                        }
                    } else {
                        self.forward.iters.push(NodeIter::new(other.1.iter()));
                    }
                }
                None => {
                    self.forward.iters.pop();
                }
            }
        }

        self.forward
            .leafs
            .pop_front()
            .map(|leaf| (leaf.0.as_slice().to_vec(), leaf.1, leaf.2, leaf.3))
    }
}

pub struct VersionedIter<'a, P: KeyTrait + 'a, V: Clone> {
    inner: Box<dyn Iterator<Item = (Vec<u8>, &'a V, &'a u64, &'a u64)> + 'a>,
    _marker: std::marker::PhantomData<P>,
}

impl<'a, P: KeyTrait + 'a, V: Clone> VersionedIter<'a, P, V> {
    pub(crate) fn new(node: Option<&'a Arc<Node<P, V>>>) -> Self {
        match node {
            Some(node) => Self {
                inner: Box::new(IterState::new(node, true)),
                _marker: Default::default(),
            },
            None => Self {
                inner: Box::new(std::iter::empty()),
                _marker: Default::default(),
            },
        }
    }
}

impl<'a, P: KeyTrait + 'a, V: Clone> Iterator for VersionedIter<'a, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

pub(crate) fn scan_node<K, V, R>(
    node: Option<&Arc<Node<K, V>>>,
    range: R,
    query_type: QueryType,
) -> Vec<(Vec<u8>, V)>
where
    K: KeyTrait,
    V: Clone,
    R: RangeBounds<K>,
{
    iterate(node, range, query_type, true)
        .into_iter()
        .filter_map(|(k, v_opt)| v_opt.map(|v| (k, v)))
        .collect()
}

pub(crate) fn query_keys_at_node<K, V, R>(
    node: Option<&Arc<Node<K, V>>>,
    range: R,
    query_type: QueryType,
) -> Vec<Vec<u8>>
where
    K: KeyTrait + Ord,
    V: Clone,
    R: RangeBounds<K>,
{
    iterate(node, range, query_type, false)
        .into_iter()
        .map(|(k, _)| k)
        .collect()
}

fn iterate<K, V, R>(
    node: Option<&Arc<Node<K, V>>>,
    range: R,
    query_type: QueryType,
    include_values: bool,
) -> Vec<(Vec<u8>, Option<V>)>
where
    K: KeyTrait,
    V: Clone,
    R: RangeBounds<K>,
{
    let mut results = Vec::new();
    let mut forward = node.map_or_else(IterState::empty, |n| {
        IterState::scan_at(n, &range, query_type)
    });

    while let Some(node) = forward.iters.last_mut() {
        if let Some((_, res)) = node.next() {
            if let NodeType::Twig(twig) = &res.node_type {
                if range.contains(&twig.key) {
                    // Iterate through leaves of the twig
                    if let Some(leaf) = twig.get_leaf_by_query(query_type) {
                        let key = twig.key.as_slice().to_vec();
                        if include_values {
                            results.push((key, Some(leaf.value.clone())));
                        } else {
                            results.push((key, None));
                        }
                    }
                } else {
                    // stop iteration if the range end is exceeded
                    match range.end_bound() {
                        Bound::Included(k) if &twig.key > k => break,
                        Bound::Excluded(k) if &twig.key >= k => break,
                        _ => {}
                    }
                }
            }
        } else {
            // Pop the iterator if no more elements
            forward.iters.pop();
        }
    }

    results
}

#[cfg(test)]
mod tests {
    use hashbrown::HashMap;

    use crate::art::Tree;
    use crate::{FixedSizeKey, Key};

    fn from_be_bytes_key(k: &[u8]) -> u64 {
        let padded_k = if k.len() < 8 {
            let mut new_k = vec![0; 8];
            new_k[8 - k.len()..].copy_from_slice(k);
            new_k
        } else {
            k.to_vec()
        };

        let k_slice = &padded_k[..8];
        u64::from_be_bytes(k_slice.try_into().unwrap())
    }

    #[test]
    fn iter_with_versions_reads_all_versions() {
        let mut tree = Tree::<FixedSizeKey<16>, u16>::new();

        // Insert multiple versions for a few keys
        let num_keys = 10;
        let versions_per_key = 5;
        for i in 0..num_keys {
            let key: FixedSizeKey<16> = i.into();
            for version in 1..versions_per_key + 1 {
                tree.insert_unchecked(&key, i, version, 0_u64).unwrap();
            }
        }

        // Use the versioned iterator to iterate through the tree
        let iter_with_versions = tree.iter_with_versions();
        let mut versions_map = HashMap::new();
        for (key, value, version, _timestamp) in iter_with_versions {
            let key_num = from_be_bytes_key(&key);
            // Check if the key is correct (matches the value)
            assert_eq!(
                key_num, *value as u64,
                "Key does not match the expected value"
            );

            versions_map
                .entry(key_num)
                .or_insert_with(Vec::new)
                .push(*version);
        }

        // Verify that each key has the correct number of versions and they are sequential
        for (_, versions) in &versions_map {
            assert_eq!(versions.len() as u64, versions_per_key);

            let mut expected_version = 1;
            for version in versions {
                assert_eq!(*version, expected_version);
                expected_version += 1;
            }
        }

        // Verify that the total count matches the expected number of entries
        let expected_count = num_keys as u64 * versions_per_key;
        assert_eq!(
            versions_map
                .iter()
                .map(|(_key, versions)| versions.len())
                .sum::<usize>(),
            expected_count as usize,
            "Total count of versions does not match the expected count"
        );
    }

    #[test]
    fn iter_with_versions_reads_versions_in_decreasing_order() {
        let mut tree = Tree::<FixedSizeKey<16>, u16>::new();

        // Insert multiple versions for a few keys in decreasing order
        let num_keys = 10;
        let versions_per_key = 5;
        for i in 0..num_keys {
            let key: FixedSizeKey<16> = i.into();
            for version in (1..=versions_per_key).rev() {
                tree.insert_unchecked(&key, i, version, 0_u64).unwrap();
            }
        }

        // Use the versioned iterator to iterate through the tree
        let iter_with_versions = tree.iter_with_versions();
        let mut versions_map = HashMap::new();
        for (key, value, version, _timestamp) in iter_with_versions {
            let key_num = from_be_bytes_key(&key);
            // Check if the key is correct (matches the value)
            assert_eq!(
                key_num, *value as u64,
                "Key does not match the expected value"
            );

            versions_map
                .entry(key_num)
                .or_insert_with(Vec::new)
                .push(*version);
        }

        // Verify that each key has the correct number of versions and they are in decreasing order
        for (_, versions) in &versions_map {
            assert_eq!(
                versions.len() as u64,
                versions_per_key,
                "Incorrect number of versions"
            );

            // Check if versions are in decreasing order
            let mut expected_version = 1;
            for version in versions {
                assert_eq!(*version, expected_version, "Version order mismatch");
                expected_version += 1;
            }
        }

        // Verify that the total count matches the expected number of entries
        let expected_count = num_keys as u64 * versions_per_key;
        assert_eq!(
            versions_map
                .iter()
                .map(|(_key, versions)| versions.len())
                .sum::<usize>(),
            expected_count as usize,
            "Total count of versions does not match the expected count"
        );
    }

    #[test]
    fn range_query_iterator_verifies_keys_and_versions_within_range() {
        let mut tree = Tree::<FixedSizeKey<16>, u16>::new();

        // Define the range for the query
        let query_range_start: FixedSizeKey<16> = 3u16.into();
        let query_range_end: FixedSizeKey<16> = 7u16.into(); // Exclusive
        let versions_per_key = 5;

        // Insert multiple versions for multiple keys, some of which fall within the query range
        let num_keys: u16 = 10;
        for i in 0..num_keys {
            let key: FixedSizeKey<16> = i.into();
            for version in 1..=versions_per_key {
                tree.insert_unchecked(&key, i, version, 0_u64).unwrap();
            }
        }

        // Use the range query iterator to iterate through the tree for keys within the specified range

        let range_query_iter =
            tree.range_with_versions(query_range_start.clone()..=query_range_end.clone());
        let mut versions_map = HashMap::new();

        let query_range_start = from_be_bytes_key(query_range_start.as_slice());
        let query_range_end = from_be_bytes_key(query_range_end.as_slice());

        for (key, _value, version, _timestamp) in range_query_iter {
            let key_num = from_be_bytes_key(&key);
            assert!(
                key_num >= query_range_start && key_num <= query_range_end,
                "Key {:?} is outside the query range",
                key_num
            );

            versions_map
                .entry(key_num)
                .or_insert_with(Vec::new)
                .push(*version);
        }

        // Verify that each key within the range has the correct number of versions and they are sequential
        for key in query_range_start..=query_range_end {
            if let Some(versions) = versions_map.get(&key) {
                assert_eq!(
                    versions.len(),
                    versions_per_key as usize,
                    "Incorrect number of versions for key {}",
                    key
                );

                let mut expected_version = 1;
                for version in versions {
                    assert_eq!(
                        *version, expected_version,
                        "Version sequence mismatch for key {}",
                        key
                    );
                    expected_version += 1;
                }
            } else {
                panic!(
                    "Key {} within the query range was not found in the results",
                    key
                );
            }
        }

        // Optionally, verify that no keys outside the range are present in the results
        assert!(
            versions_map
                .keys()
                .all(|&k| k >= query_range_start && k <= query_range_end),
            "Found keys outside the query range"
        );

        // Verify that the total count matches the expected number of entries
        let expected_count = 25;
        assert_eq!(
            versions_map
                .iter()
                .map(|(_key, versions)| versions.len())
                .sum::<usize>(),
            expected_count as usize,
            "Total count of versions does not match the expected count"
        );
    }

    #[test]
    fn test_iter_with_versions_with_two_versions_of_same_key() {
        // This tests verifies when the root is twig node, if versioned iter works correctly
        let mut tree = Tree::<FixedSizeKey<16>, u16>::new();

        // Insert two versions for the same key
        let key: FixedSizeKey<16> = 1u16.into();
        let versions = [1, 2];
        for &version in &versions {
            tree.insert_unchecked(&key, 1, version, 0_u64).unwrap();
        }

        // Use iterator to iterate through the tree
        let iter = tree.iter_with_versions();
        let mut found_versions = Vec::new();
        for (iter_key, iter_value, iter_version, _timestamp) in iter {
            // Check if the key and value are as expected
            assert_eq!(
                from_be_bytes_key(&iter_key),
                1,
                "Key does not match the expected value"
            );
            assert_eq!(*iter_value, 1, "Value does not match the expected value");

            // Collect found versions
            found_versions.push(*iter_version);
        }

        // Verify that both versions of the key are found
        assert_eq!(
            found_versions.len(),
            2,
            "Did not find both versions of the key"
        );
        for &version in &versions {
            assert!(
                found_versions.contains(&version),
                "Missing version {}",
                version
            );
        }
    }

    #[test]
    fn test_range_with_versions_query_with_two_versions_of_same_key() {
        // This tests verifies when the root is twig node, if versioned iter works correctly
        let mut tree = Tree::<FixedSizeKey<16>, u16>::new();

        // Insert two versions for the same key
        let key: FixedSizeKey<16> = 1u16.into();
        let versions = [1, 2];
        for &version in &versions {
            tree.insert_unchecked(&key, 1, version, 0_u64).unwrap();
        }

        // Define start and end keys for the range query
        let start_key: FixedSizeKey<16> = 0u16.into(); // Start from a key before the inserted key
        let end_key: FixedSizeKey<16> = 2u16.into(); // End at a key after the inserted key

        // Use range query to iterate through the tree
        let range_iter = tree.range_with_versions(start_key..=end_key);
        let mut found_versions = Vec::new();
        for (iter_key, iter_value, iter_version, _timestamp) in range_iter {
            // Check if the key and value are as expected
            assert_eq!(
                from_be_bytes_key(&iter_key),
                1,
                "Key does not match the expected value"
            );
            assert_eq!(*iter_value, 1, "Value does not match the expected value");

            // Collect found versions
            found_versions.push(*iter_version);
        }

        // Verify that both versions of the key are found in the range query
        assert_eq!(
            found_versions.len(),
            2,
            "Did not find both versions of the key in the range query"
        );
        for &version in &versions {
            assert!(
                found_versions.contains(&version),
                "Missing version {} in range query",
                version
            );
        }
    }
}
