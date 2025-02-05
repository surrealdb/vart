use std::slice::from_ref;
use std::sync::Arc;

use crate::version::{LeafTuple, Leaves, LeavesTrait, LeavesType};
use crate::{art::QueryType, KeyTrait};

/*
    Immutable nodes
*/

pub(crate) trait NodeTrait<N> {
    fn clone(&self) -> Self;
    fn add_child(&mut self, key: u8, node: N);
    fn find_child(&self, key: u8) -> Option<&Arc<N>>;
    fn find_child_mut(&mut self, key: u8) -> Option<&mut N>;
    fn delete_child(&self, key: u8) -> Self;
    fn num_children(&self) -> usize;
    fn size(&self) -> usize;
    fn replace_child(&self, key: u8, node: Arc<N>) -> Self;
}

#[derive(Clone)]
pub(crate) struct TwigNode<K: KeyTrait, V: Clone> {
    pub(crate) prefix: K,
    pub(crate) key: K,
    pub(crate) storage: Leaves<V>,
    pub(crate) version: u64, // Version for the twig node
}

impl<K: KeyTrait, V: Clone> TwigNode<K, V> {
    pub(crate) fn new(prefix: K, key: K) -> Self {
        TwigNode {
            prefix,
            key,
            storage: Leaves::new(LeavesType::Vector),
            version: 0,
        }
    }

    pub(crate) fn insert(&self, value: V, version: u64, ts: u64) -> Self {
        let mut new_storage = self.storage.clone();
        new_storage.insert_mut(value, version, ts);

        TwigNode {
            prefix: self.prefix.clone(),
            key: self.key.clone(),
            storage: new_storage,
            version: version.max(self.version),
        }
    }

    pub(crate) fn insert_mut(&mut self, value: V, version: u64, ts: u64) {
        self.storage.insert_mut(value, version, ts);
        self.version = version.max(self.version);
    }

    pub(crate) fn replace_if_newer_mut(&mut self, value: V, version: u64, ts: u64) {
        if version > self.version {
            self.storage.clear();
            self.storage.insert_mut(value, version, ts);
            self.version = version;
        }
    }

    pub(crate) fn insert_or_replace(
        &self,
        value: V,
        version: u64,
        ts: u64,
        replace: bool,
    ) -> TwigNode<K, V> {
        if replace {
            // Create a replacement Twig node with the new value only.
            let mut new_twig = Self::new(self.prefix.clone(), self.key.clone());
            new_twig.insert_mut(value, version, ts);
            new_twig
        } else {
            self.insert(value, version, ts)
        }
    }

    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = LeafTuple<'_, V>> + '_ {
        self.storage.iter()
    }
}

/// Helper functions for TwigNode for timestamp-based queries
impl<K: KeyTrait + Clone, V: Clone> TwigNode<K, V> {
    #[inline]
    pub(crate) fn get_leaf_by_query(&self, query_type: QueryType) -> Option<LeafTuple<'_, V>> {
        match query_type {
            QueryType::LatestByVersion(version) => self.get_leaf_by_version(version),
            QueryType::LatestByTs(ts) => self.get_leaf_by_ts(ts),
            QueryType::LastLessThanTs(ts) => self.last_less_than_ts(ts),
            QueryType::LastLessOrEqualTs(ts) => self.last_less_or_equal_ts(ts),
            QueryType::FirstGreaterThanTs(ts) => self.first_greater_than_ts(ts),
            QueryType::FirstGreaterOrEqualTs(ts) => self.first_greater_or_equal_ts(ts),
        }
    }

    #[inline]
    pub(crate) fn get_latest_leaf(&self) -> Option<LeafTuple<'_, V>> {
        self.storage.get_latest_leaf()
    }

    #[inline]
    pub(crate) fn get_leaf_by_version(&self, version: u64) -> Option<LeafTuple<'_, V>> {
        self.storage.get_leaf_by_version(version)
    }

    #[inline]
    pub(crate) fn get_leaf_by_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.storage.get_leaf_by_ts(ts)
    }

    pub(crate) fn get_all_versions(&self) -> Vec<(V, u64, u64)> {
        self.storage.get_all_versions()
    }

    #[inline]
    pub(crate) fn last_less_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.storage.last_less_than_ts(ts)
    }

    #[inline]
    pub(crate) fn last_less_or_equal_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.get_leaf_by_ts(ts)
    }

    #[inline]
    pub(crate) fn first_greater_than_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.storage.first_greater_than_ts(ts)
    }

    #[inline]
    pub(crate) fn first_greater_or_equal_ts(&self, ts: u64) -> Option<LeafTuple<'_, V>> {
        self.storage.first_greater_or_equal_ts(ts)
    }
}

// Source: https://www.the-paper-trail.org/post/art-paper-notes/
//
// Node4: For nodes with up to four children, ART stores all the keys in a list,
// and the child pointers in a parallel list. Looking up the next character
// in a string means searching the list of child keys, and then using the
// index to look up the corresponding pointer.
//
// Node16: Keys in a Node16 are stored sorted, so binary search could be used to
// find a particular key. Nodes with from 5 to 16 children have an identical layout
// to Node4, just with 16 children per node
//
// A FlatNode is a node with a fixed number of children. It is used for nodes with
// more than 16 children. The children are stored in a fixed-size array, and the
// keys are stored in a parallel array. The keys are stored in sorted order, so
// binary search can be used to find a particular key. The FlatNode is used for
// storing Node4 and Node16 since they have identical layouts.
pub(crate) struct FlatNode<P: KeyTrait, N, const WIDTH: usize> {
    pub(crate) prefix: P,
    keys: [u8; WIDTH],
    children: Box<[Option<Arc<N>>; WIDTH]>,
    pub(crate) inner_twig: Option<Arc<N>>,
    num_children: u8,
}

impl<P: KeyTrait, N, const WIDTH: usize> FlatNode<P, N, WIDTH> {
    pub(crate) fn new(prefix: P) -> Self {
        let children: [Option<Arc<N>>; WIDTH] = std::array::from_fn(|_| None);

        Self {
            prefix,
            keys: [0; WIDTH],
            children: Box::new(children),
            inner_twig: None,
            num_children: 0,
        }
    }

    fn find_pos(&self, key: u8) -> Option<usize> {
        let idx = (0..self.num_children as usize).find(|&i| key < self.keys[i]);
        idx.or(Some(self.num_children as usize))
    }

    fn index(&self, key: u8) -> Option<usize> {
        self.keys[..std::cmp::min(WIDTH, self.num_children as usize)]
            .iter()
            .position(|&c| key == c)
    }

    pub(crate) fn resize<const NEW_WIDTH: usize>(&self) -> FlatNode<P, N, NEW_WIDTH> {
        let mut new_node = FlatNode::<P, N, NEW_WIDTH>::new(self.prefix.clone());
        for i in 0..self.num_children as usize {
            new_node.keys[i] = self.keys[i];
            new_node.children[i].clone_from(&self.children[i]);
        }
        new_node.inner_twig = self.inner_twig.clone();
        new_node.num_children = self.num_children;
        new_node
    }

    pub(crate) fn get_value_if_single_child(&self) -> (&P, Option<Arc<N>>) {
        assert_eq!(self.num_children, 1);
        (&self.prefix, self.children[0].clone())
    }

    pub(crate) fn grow(&self) -> Node48<P, N> {
        let mut n48 = Node48::new(self.prefix.clone());
        for i in 0..self.num_children as usize {
            if let Some(child) = self.children[i].as_ref() {
                n48.insert_child(self.keys[i], child.clone());
            }
        }
        n48.inner_twig = self.inner_twig.clone();
        n48
    }

    // Helper function to insert a child node at the specified position
    #[inline]
    fn insert_child(&mut self, idx: usize, key: u8, node: Arc<N>) {
        for i in (idx..self.num_children as usize).rev() {
            self.keys[i + 1] = self.keys[i];
            self.children[i + 1] = self.children[i].take();
        }
        self.keys[idx] = key;
        self.children[idx] = Some(node);
        self.num_children += 1;
    }

    #[inline]
    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &Arc<N>> {
        let leaf_iter = from_ref(&self.inner_twig).iter();
        let children_iter = self.children.iter().take(self.num_children as usize);

        leaf_iter
            .chain(children_iter)
            .filter_map(|node| node.as_ref())
    }
}

impl<P: KeyTrait, N, const WIDTH: usize> NodeTrait<N> for FlatNode<P, N, WIDTH> {
    fn clone(&self) -> Self {
        let mut new_node = Self::new(self.prefix.clone());
        for i in 0..self.num_children as usize {
            new_node.keys[i] = self.keys[i];
            new_node.children[i].clone_from(&self.children[i])
        }
        new_node.inner_twig = self.inner_twig.clone();
        new_node.num_children = self.num_children;
        new_node
    }

    fn replace_child(&self, key: u8, node: Arc<N>) -> Self {
        let mut new_node = self.clone();
        let idx = new_node.index(key).unwrap();
        new_node.keys[idx] = key;
        new_node.children[idx] = Some(node);
        new_node
    }

    fn add_child(&mut self, key: u8, node: N) {
        let idx = self.find_pos(key).expect("node is full");
        self.insert_child(idx, key, Arc::new(node));
    }

    fn find_child(&self, key: u8) -> Option<&Arc<N>> {
        let idx = self.index(key)?;
        let child = self.children[idx].as_ref();
        child
    }

    // New find_child_mut method
    fn find_child_mut(&mut self, key: u8) -> Option<&mut N> {
        let idx = self.index(key)?;
        let child = self.children[idx].as_mut()?;
        Arc::get_mut(child)
    }

    fn delete_child(&self, key: u8) -> Self {
        let mut new_node = self.clone();
        let idx = self
            .keys
            .iter()
            .take(self.num_children as usize)
            .position(|&k| k == key)
            .unwrap();
        new_node.children[idx] = None;
        for i in idx..(WIDTH - 1) {
            new_node.keys[i] = self.keys[i + 1];
            new_node.children[i].clone_from(&self.children[i + 1])
        }

        new_node.keys[WIDTH - 1] = 0;
        new_node.children[WIDTH - 1] = None;
        new_node.num_children -= 1;

        new_node
    }

    #[inline(always)]
    fn num_children(&self) -> usize {
        self.num_children as usize
    }

    #[inline(always)]
    fn size(&self) -> usize {
        WIDTH
    }
}

// Source: https://www.the-paper-trail.org/post/art-paper-notes/
//
// Node48: It can hold up to three times as many keys as a Node16. As the paper says,
// when there are more than 16 children, searching for the key can become expensive,
// so instead the keys are stored implicitly in an array of 256 indexes. The entries
// in that array index a separate array of up to 48 pointers.
//
// A Node48 is a 256-entry array of pointers to children. The pointers are stored in
// a Vector Array, which is a Vector of length WIDTH (48) that stores the pointers.

pub(crate) struct Node48<P: KeyTrait, N> {
    pub(crate) prefix: P,
    keys: Box<[u8; 256]>,
    children: Box<[Option<Arc<N>>; 48]>,
    pub(crate) inner_twig: Option<Arc<N>>,
    child_bitmap: u64,
}

impl<P: KeyTrait, N> Node48<P, N> {
    pub(crate) fn new(prefix: P) -> Self {
        Self {
            prefix,
            keys: Box::new([u8::MAX; 256]),
            children: Box::new(std::array::from_fn(|_| None)),
            inner_twig: None,
            child_bitmap: 0,
        }
    }

    pub(crate) fn insert_child(&mut self, key: u8, node: Arc<N>) {
        let pos = self.child_bitmap.trailing_ones();
        assert!(pos < 48);

        self.keys[key as usize] = pos as u8;
        self.children[pos as usize] = Some(node);
        self.child_bitmap |= 1 << pos;
    }

    pub(crate) fn shrink<const NEW_WIDTH: usize>(&self) -> FlatNode<P, N, NEW_WIDTH> {
        let mut fnode = FlatNode::new(self.prefix.clone());
        for (key, pos) in self
            .keys
            .iter()
            .enumerate()
            .filter(|(_, idx)| **idx != u8::MAX)
        {
            let child = self.children[*pos as usize].as_ref().unwrap().clone();
            let idx = fnode.find_pos(key as u8).expect("node is full");
            fnode.insert_child(idx, key as u8, child);
        }
        fnode.inner_twig = self.inner_twig.clone();
        fnode
    }

    pub(crate) fn grow(&self) -> Node256<P, N> {
        let mut n256 = Node256::new(self.prefix.clone());
        for (key, pos) in self
            .keys
            .iter()
            .enumerate()
            .filter(|(_, idx)| **idx != u8::MAX)
        {
            let child = self.children[*pos as usize].as_ref().unwrap().clone();
            n256.insert_child(key as u8, child);
        }
        n256.inner_twig = self.inner_twig.clone();
        n256
    }

    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &Arc<N>> {
        let leaf_iter = from_ref(&self.inner_twig)
            .iter()
            .filter_map(|node| node.as_ref());

        let children_iter = self
            .keys
            .iter()
            .filter(|key| **key != u8::MAX)
            .map(move |pos| self.children[*pos as usize].as_ref().unwrap());

        leaf_iter.chain(children_iter)
    }
}

impl<P: KeyTrait, N> NodeTrait<N> for Node48<P, N> {
    fn clone(&self) -> Self {
        Node48 {
            prefix: self.prefix.clone(),
            keys: self.keys.clone(),
            children: self.children.clone(),
            inner_twig: self.inner_twig.clone(),
            child_bitmap: self.child_bitmap,
        }
    }

    fn replace_child(&self, key: u8, node: Arc<N>) -> Self {
        let mut new_node = self.clone();
        let idx = new_node.keys[key as usize];
        assert!(idx != u8::MAX);
        new_node.children[idx as usize] = Some(node);

        new_node
    }

    fn add_child(&mut self, key: u8, node: N) {
        self.insert_child(key, Arc::new(node));
    }

    fn delete_child(&self, key: u8) -> Self {
        let pos = self.keys[key as usize];
        assert!(pos != u8::MAX);
        let mut new_node = self.clone();
        new_node.keys[key as usize] = u8::MAX;
        new_node.children[pos as usize] = None;
        new_node.child_bitmap &= !(1 << pos);

        new_node
    }

    fn find_child(&self, key: u8) -> Option<&Arc<N>> {
        let idx = self.keys[key as usize];
        if idx == u8::MAX {
            return None;
        }
        Some(self.children[idx as usize].as_ref().unwrap())
    }

    // New find_child_mut method
    fn find_child_mut(&mut self, key: u8) -> Option<&mut N> {
        let idx = self.keys[key as usize];
        if idx == u8::MAX {
            return None;
        }
        let child_arc = self.children[idx as usize].as_mut()?;
        Arc::get_mut(child_arc)
    }

    fn num_children(&self) -> usize {
        self.child_bitmap.count_ones() as usize
    }

    #[inline(always)]
    fn size(&self) -> usize {
        48
    }
}

// Source: https://www.the-paper-trail.org/post/art-paper-notes/
//
// Node256: It is the traditional trie node, used when a node has
// between 49 and 256 children. Looking up child pointers is obviously
// very efficient - the most efficient of all the node types - and when
// occupancy is at least 49 children the wasted space is less significant.
//
// A Node256 is a 256-entry array of pointers to children. The pointers are stored in
// a Vector Array, which is a Vector of length WIDTH (256) that stores the pointers.
pub(crate) struct Node256<P: KeyTrait, N> {
    pub(crate) prefix: P, // Prefix associated with the node
    children: Box<[Option<Arc<N>>; 256]>,
    pub(crate) inner_twig: Option<Arc<N>>,
    num_children: usize,
}

impl<P: KeyTrait, N> Node256<P, N> {
    pub(crate) fn new(prefix: P) -> Self {
        Self {
            prefix,
            children: Box::new(std::array::from_fn(|_| None)),
            inner_twig: None,
            num_children: 0,
        }
    }

    pub(crate) fn shrink(&self) -> Node48<P, N> {
        debug_assert!(self.num_children() < 49);
        let mut indexed = Node48::new(self.prefix.clone());
        for (key, v) in self
            .children
            .iter()
            .enumerate()
            .filter_map(|m| m.1.clone().map(|x| (m.0, x)))
        {
            indexed.insert_child(key as u8, v);
        }
        indexed.inner_twig = self.inner_twig.clone();
        indexed
    }

    #[inline]
    fn insert_child(&mut self, key: u8, node: Arc<N>) {
        let new_insert = self.children[key as usize].is_none();
        self.children[key as usize] = Some(node);
        self.num_children += new_insert as usize;
    }

    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &Arc<N>> {
        let leaf_iter = from_ref(&self.inner_twig).iter();
        let children_iter = self.children.iter();

        leaf_iter
            .chain(children_iter)
            .filter_map(|node| node.as_ref())
    }
}

impl<P: KeyTrait, N> NodeTrait<N> for Node256<P, N> {
    fn clone(&self) -> Self {
        Self {
            prefix: self.prefix.clone(),
            children: self.children.clone(),
            inner_twig: self.inner_twig.clone(),
            num_children: self.num_children,
        }
    }

    fn replace_child(&self, key: u8, node: Arc<N>) -> Self {
        debug_assert!(self.children[key as usize].is_some());
        let mut new_node = self.clone();

        new_node.children[key as usize] = Some(node);
        new_node
    }

    #[inline]
    fn add_child(&mut self, key: u8, node: N) {
        self.insert_child(key, Arc::new(node));
    }

    #[inline]
    fn find_child(&self, key: u8) -> Option<&Arc<N>> {
        self.children[key as usize].as_ref()
    }

    // New find_child_mut method
    fn find_child_mut(&mut self, key: u8) -> Option<&mut N> {
        let child_arc = self.children[key as usize].as_mut()?;
        Arc::get_mut(child_arc)
    }

    #[inline]
    fn delete_child(&self, key: u8) -> Self {
        let mut new_node = self.clone();
        let removed = new_node.children[key as usize].take().is_some();
        new_node.num_children -= removed as usize;
        new_node
    }

    #[inline]
    fn num_children(&self) -> usize {
        self.num_children
    }

    #[inline(always)]
    fn size(&self) -> usize {
        256
    }
}

#[cfg(test)]
mod tests {
    use crate::FixedSizeKey;

    use super::{FlatNode, Node256, Node48, NodeTrait, TwigNode};
    use rand::prelude::SliceRandom;
    use std::sync::Arc;

    fn node_test<N: NodeTrait<usize>>(mut node: N, size: usize) {
        for i in 0..size {
            node.add_child(i as u8, i);
        }

        for i in 0..size {
            assert!(matches!(node.find_child(i as u8), Some(v) if *v == i.into()));
        }

        for i in 0..size {
            node = node.delete_child(i as u8);
        }

        assert_eq!(node.num_children(), 0);
    }

    #[test]
    fn flatnode() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());

        node_test(
            FlatNode::<FixedSizeKey<8>, usize, 4>::new(dummy_prefix.clone()),
            4,
        );
        node_test(
            FlatNode::<FixedSizeKey<8>, usize, 16>::new(dummy_prefix.clone()),
            16,
        );
        node_test(
            FlatNode::<FixedSizeKey<8>, usize, 32>::new(dummy_prefix.clone()),
            32,
        );
        node_test(
            FlatNode::<FixedSizeKey<8>, usize, 48>::new(dummy_prefix.clone()),
            48,
        );
        node_test(
            FlatNode::<FixedSizeKey<8>, usize, 64>::new(dummy_prefix.clone()),
            64,
        );

        // Resize from 16 to 4
        let mut node = FlatNode::<FixedSizeKey<8>, usize, 16>::new(dummy_prefix.clone());
        for i in 0..4 {
            node.add_child(i as u8, i);
        }

        let resized: FlatNode<FixedSizeKey<8>, usize, 4> = node.resize();
        assert_eq!(resized.num_children, 4);
        for i in 0..4 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i.into()));
        }

        // Resize from 4 to 16
        let mut node = FlatNode::<FixedSizeKey<8>, usize, 4>::new(dummy_prefix.clone());
        for i in 0..4 {
            node.add_child(i as u8, i);
        }
        let mut resized: FlatNode<FixedSizeKey<8>, usize, 16> = node.resize();
        assert_eq!(resized.num_children, 4);
        for i in 4..16 {
            resized.add_child(i as u8, i);
        }
        assert_eq!(resized.num_children, 16);
        for i in 0..16 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i.into()));
        }

        // Resize from 16 to 48
        let mut node = FlatNode::<FixedSizeKey<8>, usize, 16>::new(dummy_prefix.clone());
        for i in 0..16 {
            node.add_child(i as u8, i);
        }

        let resized = node.grow();
        assert_eq!(resized.num_children(), 16);
        for i in 0..16 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i.into()));
        }

        // Additional test for adding and deleting children
        let mut node = FlatNode::<FixedSizeKey<8>, usize, 4>::new(dummy_prefix);
        node.add_child(1, 1);
        node.add_child(2, 2);
        node.add_child(3, 3);
        node.add_child(4, 4);
        assert_eq!(node.num_children(), 4);
        assert_eq!(node.find_child(1), Some(&1.into()));
        assert_eq!(node.find_child(2), Some(&2.into()));
        assert_eq!(node.find_child(3), Some(&3.into()));
        assert_eq!(node.find_child(4), Some(&4.into()));
        assert_eq!(node.find_child(5), None);

        node = node.delete_child(1);
        node = node.delete_child(2);
        node = node.delete_child(3);
        node = node.delete_child(4);
        assert_eq!(node.num_children(), 0);
    }

    #[test]
    fn node48() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());

        // Create and test Node48
        let mut n48 = Node48::<FixedSizeKey<8>, u8>::new(dummy_prefix.clone());
        for i in 0..48 {
            n48.add_child(i, i);
        }
        for i in 0..48 {
            assert_eq!(n48.find_child(i), Some(&i.into()));
        }
        for i in 0..48 {
            n48 = n48.delete_child(i);
        }
        for i in 0..48 {
            assert!(n48.find_child(i as u8).is_none());
        }

        // Resize from 48 to 16
        let mut node = Node48::<FixedSizeKey<8>, u8>::new(dummy_prefix.clone());
        for i in 0..18 {
            node.add_child(i, i);
        }
        assert_eq!(node.num_children(), 18);
        node = node.delete_child(0);
        node = node.delete_child(1);
        assert_eq!(node.num_children(), 16);

        let resized = node.shrink::<16>();
        assert_eq!(resized.num_children, 16);
        for i in 2..18 {
            assert!(matches!(resized.find_child(i), Some(v) if *v == i.into()));
        }

        // Resize from 48 to 4
        let mut node = Node48::<FixedSizeKey<8>, u8>::new(dummy_prefix.clone());
        for i in 0..4 {
            node.add_child(i, i);
        }
        let resized = node.shrink::<4>();
        assert_eq!(resized.num_children, 4);
        for i in 0..4 {
            assert!(matches!(resized.find_child(i), Some(v) if *v == i.into()));
        }

        // Resize from 48 to 256
        let mut node = Node48::<FixedSizeKey<8>, u8>::new(dummy_prefix);
        for i in 0..48 {
            node.add_child(i, i);
        }

        let resized = node.grow();
        assert_eq!(resized.num_children, 48);
        for i in 0..48 {
            assert!(matches!(resized.find_child(i), Some(v) if *v == i.into()));
        }
    }

    #[test]
    fn node256() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());

        node_test(
            Node256::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone()),
            255,
        );

        let mut n256 = Node256::new(dummy_prefix.clone());
        for i in 0..255 {
            n256.add_child(i, i);
            assert_eq!(n256.find_child(i), Some(&i.into()));
            n256 = n256.delete_child(i);
            assert_eq!(n256.find_child(i), None);
        }

        // resize from 256 to 48
        let mut node = Node256::new(dummy_prefix);
        for i in 0..48 {
            node.add_child(i, i);
        }

        let resized = node.shrink();
        assert_eq!(resized.num_children(), 48);
        for i in 0..48 {
            assert!(matches!(resized.find_child(i), Some(v) if *v == i.into()));
        }
    }

    #[test]
    fn twig_insert() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());
        let node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);

        // Test initial state
        assert!(node.iter().next().is_none());

        // Test after insert
        let new_node = node.insert(42, 123, 0);
        assert!(node.iter().next().is_none()); // Original node unchanged

        let mut new_iter = new_node.iter();
        let leaf = new_iter.next().unwrap();
        assert_eq!(leaf.0, 123);
        assert_eq!(*leaf.2, 42);
        assert_eq!(leaf.1, 0);
        assert!(new_iter.next().is_none());
    }

    #[test]
    fn twig_insert_mut() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);

        node.insert_mut(42, 123, 0);

        let mut iter = node.iter();
        let leaf = iter.next().unwrap();
        assert_eq!(leaf.0, 123);
        assert_eq!(*leaf.2, 42);
        assert_eq!(leaf.1, 0);
        assert!(iter.next().is_none());
    }

    #[test]
    fn twig_get_latest_leaf() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);

        node.insert_mut(42, 123, 0);
        node.insert_mut(43, 124, 1);

        let leaf = node.get_latest_leaf().unwrap();
        assert_eq!(leaf.0, 124);
        assert_eq!(*leaf.2, 43);
        assert_eq!(leaf.1, 1);
    }

    #[test]
    fn twig_get_leaf_by_version() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);

        node.insert_mut(42, 123, 0);
        node.insert_mut(43, 124, 1);

        let leaf = node.get_leaf_by_version(123).unwrap();
        println!("{:?} {:?}", leaf.1, leaf.0);
        assert_eq!(leaf.0, 123);
        assert_eq!(*leaf.2, 42);
        assert_eq!(leaf.1, 0);

        let leaf = node.get_leaf_by_version(124).unwrap();
        assert_eq!(leaf.0, 124);
        assert_eq!(*leaf.2, 43);
        assert_eq!(leaf.1, 1);
    }

    #[test]
    fn twig_iter() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);

        node.insert_mut(42, 123, 0);
        node.insert_mut(43, 124, 1);

        let mut values: Vec<_> = node.iter().map(|leaf| (leaf.0, *leaf.2)).collect();
        values.sort_by_key(|&(v, _)| v);

        assert_eq!(values, vec![(123, 42), (124, 43)]);
    }

    #[test]
    fn memory_leak() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());

        // Create and test flatnode
        let mut node = FlatNode::<FixedSizeKey<8>, usize, 4>::new(dummy_prefix.clone());
        for i in 0..4 {
            node.add_child(i as u8, i);
        }

        for child in node.iter() {
            assert_eq!(Arc::strong_count(child), 1);
        }

        // Create and test Node48
        let mut n48 = Node48::<FixedSizeKey<8>, u8>::new(dummy_prefix.clone());
        for i in 0..48 {
            n48.add_child(i, i);
        }

        for child in n48.iter() {
            assert_eq!(Arc::strong_count(child), 1);
        }

        // Create and test Node256
        let mut n256 = Node256::new(dummy_prefix);
        for i in 0..255 {
            n256.add_child(i, i);
        }

        for child in n256.iter() {
            assert_eq!(Arc::strong_count(child), 1);
        }
    }

    #[test]
    fn cache_line_size() {
        assert!(std::mem::size_of::<FlatNode::<FixedSizeKey<8>, usize, 4>>() <= 64);
        assert!(std::mem::size_of::<FlatNode::<FixedSizeKey<8>, usize, 16>>() <= 64);
    }

    #[test]
    fn verify_node_insert_order() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("foo".as_bytes());

        let mut node4 = FlatNode::<FixedSizeKey<8>, usize, 4>::new(dummy_prefix.clone());
        node4.add_child(4, 1);
        node4.add_child(2, 1);
        node4.add_child(1, 1);
        node4.add_child(0, 1);

        // verify the order of keys as [0, 1, 2, 4]
        assert_eq!(node4.keys, [0, 1, 2, 4]);

        let mut node16 = FlatNode::<FixedSizeKey<8>, usize, 16>::new(dummy_prefix.clone());
        // Insert children into node16 in random order
        let mut rng = rand::thread_rng();
        let mut values: Vec<u8> = (0..16).collect();
        values.shuffle(&mut rng);
        for value in values {
            node16.add_child(value, 1);
        }
        // Verify the keys have been inserted in order
        assert_eq!(node16.keys, *(0..16).collect::<Vec<u8>>());
    }

    #[test]
    fn twig_get_leaf_by_ts() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("bar".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);

        // Inserting leaves with different timestamps
        node.insert_mut(50, 200, 10); // value: 50, version: 200, timestamp: 10
        node.insert_mut(51, 201, 20); // value: 51, version: 201, timestamp: 20

        // Test case 1: Retrieve leaf by exact timestamp
        let leaf = node.get_leaf_by_ts(10).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);

        // Test case 2: Retrieve leaf by another exact timestamp
        let leaf = node.get_leaf_by_ts(20).unwrap();
        assert_eq!(leaf.0, 201);
        assert_eq!(*leaf.2, 51);
        assert_eq!(leaf.1, 20);

        // Test case 3: Attempt to retrieve leaf by a non-existent timestamp
        let leaf = node.get_leaf_by_ts(30).unwrap();
        assert_eq!(leaf.0, 201);
        assert_eq!(*leaf.2, 51);
        assert_eq!(leaf.1, 20);
    }

    #[test]
    fn test_get_leaf_by_version() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("bar".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);
        node.insert_mut(50, 200, 10); // value: 50, version: 200, timestamp: 10
        node.insert_mut(51, 201, 20); // value: 51, version: 201, timestamp: 20

        // Exact version match
        let leaf = node.get_leaf_by_version(200).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);

        // Version not present, should get closest lower version
        let leaf = node.get_leaf_by_version(199);
        assert!(leaf.is_none());

        // Higher version, should get the highest available version
        let leaf = node.get_leaf_by_version(202).unwrap();
        assert_eq!(leaf.0, 201);
        assert_eq!(*leaf.2, 51);
        assert_eq!(leaf.1, 20);
    }

    #[test]
    fn test_get_leaf_by_ts() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("bar".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);
        node.insert_mut(50, 200, 10); // value: 50, version: 200, timestamp: 10
        node.insert_mut(51, 201, 20); // value: 51, version: 201, timestamp: 20

        // Exact timestamp match
        let leaf = node.get_leaf_by_ts(10).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);

        // Timestamp not present, should get closest lower timestamp
        let leaf = node.get_leaf_by_ts(15).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);

        // Higher timestamp, should get the highest available timestamp
        let leaf = node.get_leaf_by_ts(25).unwrap();
        assert_eq!(leaf.0, 201);
        assert_eq!(*leaf.2, 51);
        assert_eq!(leaf.1, 20);
    }

    #[test]
    fn test_get_all_versions() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("bar".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);
        node.insert_mut(50, 200, 10); // value: 50, version: 200, timestamp: 10
        node.insert_mut(51, 201, 20); // value: 51, version: 201, timestamp: 20

        let versions = node.get_all_versions();
        assert_eq!(versions.len(), 2);
        assert_eq!(versions[0], (50, 200, 10));
        assert_eq!(versions[1], (51, 201, 20));
    }

    #[test]
    fn test_last_less_than_ts() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("bar".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);
        node.insert_mut(50, 200, 10); // value: 50, version: 200, timestamp: 10
        node.insert_mut(51, 201, 20); // value: 51, version: 201, timestamp: 20

        // Timestamp just below an existing timestamp
        let leaf = node.last_less_than_ts(20).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);

        // Timestamp well below any existing timestamp
        let leaf = node.last_less_than_ts(5);
        assert!(leaf.is_none());

        // Timestamp above all existing timestamps
        let leaf = node.last_less_than_ts(25).unwrap();
        assert_eq!(leaf.0, 201);
        assert_eq!(*leaf.2, 51);
        assert_eq!(leaf.1, 20);
    }

    #[test]
    fn test_last_less_or_equal_ts() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("bar".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);
        node.insert_mut(50, 200, 10); // value: 50, version: 200, timestamp: 10
        node.insert_mut(51, 201, 20); // value: 51, version: 201, timestamp: 20

        // Exact timestamp
        let leaf = node.last_less_or_equal_ts(10).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);

        // Timestamp not present, should get closest lower timestamp
        let leaf = node.last_less_or_equal_ts(15).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);

        // Higher timestamp, should get the highest available timestamp
        let leaf = node.last_less_or_equal_ts(25).unwrap();
        assert_eq!(leaf.0, 201);
        assert_eq!(*leaf.2, 51);
        assert_eq!(leaf.1, 20);
    }

    #[test]
    fn test_first_greater_than_ts() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("bar".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);
        node.insert_mut(50, 200, 10); // value: 50, version: 200, timestamp: 10
        node.insert_mut(51, 201, 20); // value: 51, version: 201, timestamp: 20

        // Timestamp just above an existing timestamp
        let leaf = node.first_greater_than_ts(10).unwrap();
        assert_eq!(leaf.0, 201);
        assert_eq!(*leaf.2, 51);
        assert_eq!(leaf.1, 20);

        // Timestamp well above any existing timestamp
        let leaf = node.first_greater_than_ts(25);
        assert!(leaf.is_none());

        // Timestamp below all existing timestamps
        let leaf = node.first_greater_than_ts(5).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);
    }

    #[test]
    fn test_first_greater_or_equal_ts() {
        let dummy_prefix: FixedSizeKey<8> = FixedSizeKey::create_key("bar".as_bytes());
        let mut node = TwigNode::<FixedSizeKey<8>, usize>::new(dummy_prefix.clone(), dummy_prefix);
        node.insert_mut(50, 200, 10); // value: 50, version: 200, timestamp: 10
        node.insert_mut(51, 201, 20); // value: 51, version: 201, timestamp: 20

        // Exact timestamp
        let leaf = node.first_greater_or_equal_ts(10).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);

        // Timestamp not present, should get closest higher timestamp
        let leaf = node.first_greater_or_equal_ts(15).unwrap();
        assert_eq!(leaf.0, 201);
        assert_eq!(*leaf.2, 51);
        assert_eq!(leaf.1, 20);

        // Lower timestamp, should get the lowest available timestamp
        let leaf = node.first_greater_or_equal_ts(5).unwrap();
        assert_eq!(leaf.0, 200);
        assert_eq!(*leaf.2, 50);
        assert_eq!(leaf.1, 10);
    }
}
