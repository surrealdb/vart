use std::collections::{Bound, VecDeque};
use std::ops::RangeBounds;
use std::sync::Arc;

use crate::art::{Node, NodeType};
use crate::KeyTrait;

// TODO: need to add more tests for snapshot readers
/// A structure representing a pointer for iterating over the Trie's key-value pairs.
pub struct IterationPointer<P: KeyTrait, V: Clone> {
    root: Arc<Node<P, V>>,
}

impl<P: KeyTrait, V: Clone> IterationPointer<P, V> {
    /// Creates a new IterationPointer instance.
    ///
    /// # Arguments
    ///
    /// * `root` - The root node of the Trie.
    ///
    pub fn new(root: Arc<Node<P, V>>) -> IterationPointer<P, V> {
        IterationPointer { root }
    }

    /// Returns an iterator over the key-value pairs within the Trie.
    ///
    /// # Returns
    ///
    /// Returns an Iter iterator instance.
    ///
    pub fn iter(&self) -> Iter<P, V> {
        Iter::new(Some(&self.root))
    }

    /// Returns an iterator over all
    pub fn versioned_iter(&self) -> VersionedIter<P, V> {
        VersionedIter::new(Some(&self.root))
    }

    /// Returns a range query iterator over the Trie.
    pub fn range<'a, R>(
        &'a self,
        range: R,
    ) -> impl Iterator<Item = (Vec<u8>, &'a V, &'a u64, &'a u64)>
    where
        R: RangeBounds<P> + 'a,
    {
        Range::new(Some(&self.root), range)
    }

    /// Returns a versioned range query iterator over the Trie.
    pub fn versioned_range<'a, R>(
        &'a self,
        range: R,
    ) -> impl Iterator<Item = (Vec<u8>, &'a V, &'a u64, &'a u64)>
    where
        R: RangeBounds<P> + 'a,
    {
        Range::new_versioned(Some(&self.root), range)
    }
}

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
            let val = twig.get_latest_leaf();
            if let Some(v) = val {
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
                let val = twig.get_latest_leaf();
                if let Some(v) = val {
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
        if let Some(node) = node {
            Self {
                forward: IterState::forward_scan(node, &range, false),
                range,
                is_versioned: false,
            }
        } else {
            Self {
                forward: IterState::empty(),
                range,
                is_versioned: false,
            }
        }
    }

    pub(crate) fn new_versioned(node: Option<&'a Arc<Node<K, V>>>, range: R) -> Self
    where
        R: RangeBounds<K>,
    {
        if let Some(node) = node {
            Self {
                forward: IterState::forward_scan(node, &range, false),
                range,
                is_versioned: true,
            }
        } else {
            Self {
                forward: IterState::empty(),
                range,
                is_versioned: true,
            }
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
    fn versioned_iter_reads_all_versions() {
        let mut tree = Tree::<FixedSizeKey<16>, u16>::new();

        // Insert multiple versions for a few keys
        let num_keys = 10;
        let versions_per_key = 5;
        for i in 0..num_keys {
            let key: FixedSizeKey<16> = i.into();
            for version in 1..versions_per_key + 1 {
                // println!("Inserting with version {}", version);
                tree.insert_without_version_increment_check(&key, i, version, 0_u64)
                    .unwrap();
            }
        }

        // Use the versioned iterator to iterate through the tree
        let versioned_iter = tree.versioned_iter();
        let mut versions_map = HashMap::new();
        for (key, value, version, _timestamp) in versioned_iter {
            println!("Key: {:?}, Value: {:?}, Version: {:?}", key, value, version);
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

            // Check if versions are sequential, assuming they start from 1
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
    fn versioned_iter_reads_versions_in_decreasing_order() {
        let mut tree = Tree::<FixedSizeKey<16>, u16>::new();

        // Insert multiple versions for a few keys in decreasing order
        let num_keys = 10;
        let versions_per_key = 5;
        for i in 0..num_keys {
            let key: FixedSizeKey<16> = i.into();
            for version in (1..=versions_per_key).rev() {
                tree.insert_without_version_increment_check(&key, i, version, 0_u64)
                    .unwrap();
            }
        }

        // Use the versioned iterator to iterate through the tree
        let versioned_iter = tree.versioned_iter();
        let mut versions_map = HashMap::new();
        for (key, value, version, _timestamp) in versioned_iter {
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
                tree.insert_without_version_increment_check(&key, i, version, 0_u64)
                    .unwrap();
            }
        }

        // Use the range query iterator to iterate through the tree for keys within the specified range

        let range_query_iter =
            tree.versioned_range(query_range_start.clone()..=query_range_end.clone());
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

                // Check if versions are sequential, assuming they start from 1
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
}
