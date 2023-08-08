use core::panic;
use std::cmp::min;
use std::collections::{Bound, HashMap};
use std::error::Error;
use std::fmt;
use std::ops::RangeBounds;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::sync::RwLock;

use crate::iter::{Iter, Range};
use crate::node::{FlatNode, LeafNode, Node256, Node48, NodeTrait, Timestamp};
use crate::snapshot::{Snapshot, SnapshotPointer};
use crate::{Key, Prefix, PrefixTrait};

// Minimum and maximum number of children for Node4
const NODE4MIN: usize = 2;
const NODE4MAX: usize = 4;

// Minimum and maximum number of children for Node16
const NODE16MIN: usize = NODE4MAX + 1;
const NODE16MAX: usize = 16;

// Minimum and maximum number of children for Node48
const NODE48MIN: usize = NODE16MAX + 1;
const NODE48MAX: usize = 48;

// Minimum and maximum number of children for Node256
const NODE256MIN: usize = NODE48MAX + 1;

// Maximum number of active snapshots
const DEFAULT_MAX_ACTIVE_SNAPSHOTS: u64 = 100;

// Define a custom error enum representing different error cases for the Trie
#[derive(Debug)]
pub enum TrieError {
    IllegalArguments,
    NotFound,
    MutexError,
    SnapshotNotFound,
    SnapshotMutexError,
    SnapshotAlreadyClosed,
    SnapshotReadersNotClosed,
    Other(String),
}

impl Error for TrieError {}

// Implement the Display trait to define how the error should be formatted as a string
impl fmt::Display for TrieError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TrieError::IllegalArguments => write!(f, "Illegal arguments"),
            TrieError::NotFound => write!(f, "Not found"),
            TrieError::MutexError => write!(f, "Failed to lock mutex"),
            TrieError::SnapshotNotFound => write!(f, "Snapshot not found"),
            TrieError::SnapshotMutexError => write!(f, "Failed to lock snapshot mutex"),
            TrieError::SnapshotAlreadyClosed => write!(f, "Snapshot already closed"),
            TrieError::SnapshotReadersNotClosed => {
                write!(f, "Readers in the snapshot are not closed")
            }
            TrieError::Other(ref message) => write!(f, "Other error: {}", message),
        }
    }
}

// From the specification: Adaptive Radix tries consist of two types of nodes:
// Inner nodes, which map prefix(prefix) keys to other nodes,
// and leaf nodes, which store the values corresponding to the key.
pub struct Node<P: Prefix + Clone, V: Clone> {
    node_type: NodeType<P, V>, // Type of the node
}

impl<P: Prefix + Clone, V: Clone> Timestamp for Node<P, V> {
    fn ts(&self) -> u64 {
        match &self.node_type {
            NodeType::Leaf(leaf) => leaf.ts(),
            NodeType::Node4(n) => n.ts(),
            NodeType::Node16(n) => n.ts(),
            NodeType::Node48(n) => n.ts(),
            NodeType::Node256(n) => n.ts(),
        }
    }
}

pub(crate) enum NodeType<P: Prefix + Clone, V: Clone> {
    // Leaf node of the adaptive radix trie
    Leaf(LeafNode<P, V>),
    // Inner node of the adaptive radix trie
    Node4(FlatNode<P, Node<P, V>, 4>), // Node with 4 keys and 4 children
    Node16(FlatNode<P, Node<P, V>, 16>), // Node with 16 keys and 16 children
    Node48(Node48<P, Node<P, V>>),     // Node with 256 keys and 48 children
    Node256(Node256<P, Node<P, V>>),   // Node with 256 keys and 256 children
}

// Adaptive radix trie
pub struct Tree<P: PrefixTrait, V: Clone> {
    root: Option<Arc<Node<P, V>>>, // Root node of the tree
    pub(crate) snapshots: RwLock<HashMap<u64, Snapshot<P, V>>>, // TODO: use a RWLock instead, and use a hashmap
    max_snapshot_id: AtomicU64,
    max_active_snapshots: u64,
}

impl<P: PrefixTrait + Clone, V: Clone> NodeType<P, V> {
    fn clone(&self) -> Self {
        match self {
            // leaf value not actually cloned
            NodeType::Leaf(leaf) => NodeType::Leaf(leaf.clone()),
            NodeType::Node4(n) => NodeType::Node4(n.clone()),
            NodeType::Node16(n) => NodeType::Node16(n.clone()),
            NodeType::Node48(n) => NodeType::Node48(n.clone()),
            NodeType::Node256(n) => NodeType::Node256(n.clone()),
        }
    }
}

// Default implementation for the Tree struct
impl<P: PrefixTrait, V: Clone> Default for Tree<P, V> {
    fn default() -> Self {
        Tree::new()
    }
}

impl<P: PrefixTrait + Clone, V: Clone> Node<P, V> {
    #[inline]
    pub(crate) fn new_leaf(prefix: P, key: P, value: V, ts: u64) -> Node<P, V> {
        Self {
            node_type: NodeType::Leaf(LeafNode {
                prefix,
                key,
                value,
                ts,
            }),
        }
    }

    // From the specification: The smallest node type can store up to 4 child
    // pointers and uses an array of length 4 for keys and another
    // array of the same length for pointers. The keys and pointers
    // are stored at corresponding positions and the keys are sorted.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn new_node4(prefix: P) -> Self {
        let nt = NodeType::Node4(FlatNode::new(prefix));
        Self { node_type: nt }
    }

    // From the specification: This node type is used for storing between 5 and
    // 16 child pointers. Like the Node4, the keys and pointers
    // are stored in separate arrays at corresponding positions, but
    // both arrays have space for 16 entries. A key can be found
    // efﬁciently with binary search or, on modern hardware, with
    // parallel comparisons using SIMD instructions.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn new_node16(prefix: P) -> Self {
        let nt = NodeType::Node16(FlatNode::new(prefix));
        Self { node_type: nt }
    }

    // From the specification: As the number of entries in a node increases,
    // searching the key array becomes expensive. Therefore, nodes
    // with more than 16 pointers do not store the keys explicitly.
    // Instead, a 256-element array is used, which can be indexed
    // with key bytes directly. If a node has between 17 and 48 child
    // pointers, this array stores indexes into a second array which
    // contains up to 48 pointers.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn new_node48(prefix: P) -> Self {
        let nt = NodeType::Node48(Node48::new(prefix));
        Self { node_type: nt }
    }

    // From the specification: The largest node type is simply an array of 256
    // pointers and is used for storing between 49 and 256 entries.
    // With this representation, the next node can be found very
    // efﬁciently using a single lookup of the key byte in that array.
    // No additional indirection is necessary. If most entries are not
    // null, this representation is also very space efﬁcient because
    // only pointers need to be stored.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn new_node256(prefix: P) -> Self {
        let nt = NodeType::Node256(Node256::new(prefix));
        Self { node_type: nt }
    }

    #[inline]
    fn is_full(&self) -> bool {
        match &self.node_type {
            NodeType::Node4(km) => self.num_children() >= km.size(),
            NodeType::Node16(km) => self.num_children() >= km.size(),
            NodeType::Node48(im) => self.num_children() >= im.size(),
            NodeType::Node256(_) => self.num_children() > 256,
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    #[inline]
    fn add_child(&self, key: u8, child: Node<P, V>) -> Self {
        match &self.node_type {
            NodeType::Node4(n) => {
                let node = NodeType::Node4(n.add_child(key, child));
                let mut new_node = Self { node_type: node };
                if new_node.is_full() {
                    new_node.grow();
                }
                new_node
            }
            NodeType::Node16(n) => {
                let node = NodeType::Node16(n.add_child(key, child));
                let mut new_node = Self { node_type: node };
                if new_node.is_full() {
                    new_node.grow();
                }
                new_node
            }
            NodeType::Node48(n) => {
                let node = NodeType::Node48(n.add_child(key, child));
                let mut new_node = Self { node_type: node };
                if new_node.is_full() {
                    new_node.grow();
                }
                new_node
            }
            NodeType::Node256(n) => {
                let node = NodeType::Node256(n.add_child(key, child));
                let mut new_node = Self { node_type: node };
                if new_node.is_full() {
                    new_node.grow();
                }
                new_node
            }
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    // Grows the current ArtNode to the next biggest size.
    // ArtNodes of type NODE4 will grow to NODE16
    // ArtNodes of type NODE16 will grow to NODE48.
    // ArtNodes of type NODE48 will grow to NODE256.
    // ArtNodes of type NODE256 will not grow, as they are the biggest type of ArtNodes
    #[inline]
    fn grow(&mut self) {
        match &mut self.node_type {
            NodeType::Node4(n) => {
                let n16 = NodeType::Node16(n.resize());
                self.node_type = n16
            }
            NodeType::Node16(n) => {
                let n48 = NodeType::Node48(n.grow());
                self.node_type = n48
            }
            NodeType::Node48(n) => {
                let n256 = NodeType::Node256(n.grow());
                self.node_type = n256
            }
            NodeType::Node256 { .. } => {
                panic!("should not grow a node 256")
            }
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    #[inline]
    fn find_child(&self, key: u8) -> Option<&Arc<Node<P, V>>> {
        if self.num_children() == 0 {
            return None;
        }

        match &self.node_type {
            NodeType::Node4(n) => n.find_child(key),
            NodeType::Node16(n) => n.find_child(key),
            NodeType::Node48(n) => n.find_child(key),
            NodeType::Node256(n) => n.find_child(key),
            NodeType::Leaf(_) => None,
        }
    }

    fn replace_child(&self, key: u8, node: Arc<Node<P, V>>) -> Self {
        match &self.node_type {
            NodeType::Node4(n) => {
                let node = NodeType::Node4(n.replace_child(key, node));
                Self { node_type: node }
            }
            NodeType::Node16(n) => {
                let node = NodeType::Node16(n.replace_child(key, node));
                Self { node_type: node }
            }
            NodeType::Node48(n) => {
                let node = NodeType::Node48(n.replace_child(key, node));
                Self { node_type: node }
            }
            NodeType::Node256(n) => {
                let node = NodeType::Node256(n.replace_child(key, node));
                Self { node_type: node }
            }
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    fn delete_child(&self, key: u8) -> Self {
        match &self.node_type {
            NodeType::Node4(n) => {
                let node = NodeType::Node4(n.delete_child(key));
                let mut new_node = Self { node_type: node };
                if new_node.num_children() < NODE4MIN {
                    new_node.shrink();
                }
                new_node
            }
            NodeType::Node16(n) => {
                let node = NodeType::Node16(n.delete_child(key));
                let mut new_node = Self { node_type: node };
                if new_node.num_children() < NODE16MIN {
                    new_node.shrink();
                }
                new_node
            }
            NodeType::Node48(n) => {
                let node = NodeType::Node48(n.delete_child(key));
                let mut new_node = Self { node_type: node };
                if new_node.num_children() < NODE48MIN {
                    new_node.shrink();
                }
                new_node
            }
            NodeType::Node256(n) => {
                let node = NodeType::Node256(n.delete_child(key));
                let mut new_node = Self { node_type: node };
                if new_node.num_children() < NODE256MIN {
                    new_node.shrink();
                }
                new_node
            }
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    #[inline]
    pub(crate) fn is_leaf(&self) -> bool {
        matches!(&self.node_type, NodeType::Leaf(_))
    }

    #[inline]
    pub(crate) fn is_inner(&self) -> bool {
        !self.is_leaf()
    }

    #[inline]
    pub(crate) fn prefix(&self) -> &P {
        match &self.node_type {
            NodeType::Node4(n) => &n.prefix,
            NodeType::Node16(n) => &n.prefix,
            NodeType::Node48(n) => &n.prefix,
            NodeType::Node256(n) => &n.prefix,
            NodeType::Leaf(n) => &n.prefix,
        }
    }

    #[inline]
    fn set_prefix(&mut self, prefix: P) {
        match &mut self.node_type {
            NodeType::Node4(n) => n.prefix = prefix,
            NodeType::Node16(n) => n.prefix = prefix,
            NodeType::Node48(n) => n.prefix = prefix,
            NodeType::Node256(n) => n.prefix = prefix,
            NodeType::Leaf(n) => n.prefix = prefix,
        }
    }

    // Shrinks the current ArtNode to the next smallest size.
    // ArtNodes of type NODE256 will shrink to NODE48
    // ArtNodes of type NODE48 will shrink to NODE16.
    // ArtNodes of type NODE16 will shrink to NODE4.
    // ArtNodes of type NODE4 will collapse into its first child.
    // If that child is not a leaf, it will concatenate its current prefix with that of its childs
    // before replacing itself.
    fn shrink(&mut self) {
        match &mut self.node_type {
            NodeType::Node4(n) => {
                self.node_type = NodeType::Node4(n.resize());
            }
            NodeType::Node16(n) => {
                self.node_type = NodeType::Node4(n.resize());
            }
            NodeType::Node48(n) => {
                let n16 = n.shrink();

                let new_node = NodeType::Node16(n16);
                self.node_type = new_node;
            }
            NodeType::Node256(n) => {
                let n48 = n.shrink();
                self.node_type = NodeType::Node48(n48);
            }
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    #[inline]
    pub fn num_children(&self) -> usize {
        match &self.node_type {
            NodeType::Node4(n) => n.num_children(),
            NodeType::Node16(n) => n.num_children(),
            NodeType::Node48(n) => n.num_children(),
            NodeType::Node256(n) => n.num_children(),
            NodeType::Leaf(_) => 0,
        }
    }

    #[inline]
    pub fn get_value(&self) -> Option<(&P, &V, &u64)> {
        let NodeType::Leaf(leaf) = &self.node_type else {
            return None;
        };
        // TODO: should return copy of value or reference?
        Some((&leaf.key, &leaf.value, &leaf.ts))
    }

    pub fn node_type_name(&self) -> String {
        match &self.node_type {
            NodeType::Node4(_) => "Node4".to_string(),
            NodeType::Node16(_) => "Node16".to_string(),
            NodeType::Node48(_) => "Node48".to_string(),
            NodeType::Node256(_) => "Node256".to_string(),
            NodeType::Leaf(_) => "Leaf".to_string(),
        }
    }

    fn clone_node(&self) -> Self {
        Self {
            node_type: self.node_type.clone(),
        }
    }

    pub(crate) fn insert_recurse<K: Key>(
        cur_node: &Arc<Node<P, V>>,
        key: &K,
        value: V,
        commit_ts: u64,
        depth: usize,
    ) -> Result<(Arc<Node<P, V>>, Option<V>), TrieError> {
        let cur_node_prefix = cur_node.prefix().clone();
        let cur_node_prefix_len = cur_node.prefix().length();

        let key_prefix = key.prefix_after(depth);
        let longest_common_prefix = cur_node_prefix.longest_common_prefix(key_prefix);

        let new_key = cur_node_prefix.prefix_after(longest_common_prefix);
        let prefix = cur_node_prefix.prefix_before(longest_common_prefix);
        let is_prefix_match = min(cur_node_prefix_len, key_prefix.len()) == longest_common_prefix;

        if let NodeType::Leaf(ref leaf) = &cur_node.node_type {
            if is_prefix_match && cur_node_prefix.length() == key_prefix.len() {
                return Ok((
                    Arc::new(Node::new_leaf(
                        key.as_slice().into(),
                        key.as_slice().into(),
                        value,
                        commit_ts,
                    )),
                    Some(leaf.value.clone()),
                ));
            }
        }

        if !is_prefix_match {
            let mut old_node = cur_node.clone_node();
            old_node.set_prefix(new_key);
            let mut n4 = Node::new_node4(prefix);

            let k1 = cur_node_prefix.at(longest_common_prefix);
            let k2 = key_prefix[longest_common_prefix];
            let new_leaf = Node::new_leaf(
                key_prefix[longest_common_prefix..].into(),
                key.as_slice().into(),
                value,
                commit_ts,
            );
            n4 = n4.add_child(k1, old_node).add_child(k2, new_leaf);
            return Ok((Arc::new(n4), None));
        }

        let k = key_prefix[longest_common_prefix];
        let child_for_key = cur_node.find_child(k);
        if let Some(child) = child_for_key {
            match Node::insert_recurse(child, key, value, commit_ts, depth + longest_common_prefix)
            {
                Ok((new_child, old_value)) => {
                    let new_node = cur_node.replace_child(k, new_child);
                    return Ok((Arc::new(new_node), old_value));
                }
                Err(err) => {
                    return Err(err);
                }
            }
        };

        let new_leaf = Node::new_leaf(
            key_prefix[longest_common_prefix..].into(),
            key.as_slice().into(),
            value,
            commit_ts,
        );
        let new_node = cur_node.add_child(k, new_leaf);
        Ok((Arc::new(new_node), None))
    }

    fn remove_recurse<K: Key>(
        cur_node: &Arc<Node<P, V>>,
        key: &K,
        depth: usize,
    ) -> (Option<Arc<Node<P, V>>>, bool) {
        let prefix = cur_node.prefix().clone();

        let key_prefix = key.prefix_after(depth);
        let longest_common_prefix = prefix.longest_common_prefix(key_prefix);
        let is_prefix_match = min(prefix.length(), key_prefix.len()) == longest_common_prefix;

        if is_prefix_match && prefix.length() == key_prefix.len() {
            return (None, true);
        }

        let k = key_prefix[longest_common_prefix];

        let child = cur_node.find_child(k);
        if let Some(child_node) = child {
            let (_new_child, removed) =
                Node::remove_recurse(child_node, key, depth + longest_common_prefix);
            if removed {
                let new_node = cur_node.delete_child(k);
                return (Some(Arc::new(new_node)), true);

                // if let Some(new_child_node) = new_child {
                //     let new_node = cur_node.clone().delete_child(k, new_child_node);
                //     return (Some(Arc::new(new_node)), true);
                // }
            }
        }

        (Some(cur_node.clone()), false)
    }

    pub fn get_recurse<'a, K: Key>(
        cur_node: &'a Node<P, V>,
        key: &K,
    ) -> Option<(&'a P, &'a V, &'a u64)> {
        let mut cur_node = cur_node;
        let mut depth = 0;
        loop {
            let key_prefix = key.prefix_after(depth);
            let prefix = cur_node.prefix();
            let lcp = prefix.longest_common_prefix(key_prefix);
            if lcp != prefix.length() {
                return None;
            }

            if prefix.length() == key_prefix.len() {
                return cur_node.get_value();
            }

            let k = key.at(depth + prefix.length());
            depth += prefix.length();
            cur_node = cur_node.find_child(k)?;
        }
    }

    #[allow(dead_code)]
    pub fn iter(&self) -> Box<dyn Iterator<Item = (u8, &Arc<Self>)> + '_> {
        return match &self.node_type {
            NodeType::Node4(n) => Box::new(n.iter()),
            NodeType::Node16(n) => Box::new(n.iter()),
            NodeType::Node48(n) => Box::new(n.iter()),
            NodeType::Node256(n) => Box::new(n.iter()),
            NodeType::Leaf(_) => Box::new(std::iter::empty()),
        };
    }
}

impl<P: PrefixTrait, V: Clone> Tree<P, V> {
    pub fn new() -> Self {
        Tree {
            root: None,
            max_snapshot_id: AtomicU64::new(0),
            snapshots: RwLock::new(HashMap::new()),
            max_active_snapshots: DEFAULT_MAX_ACTIVE_SNAPSHOTS,
        }
    }

    pub fn insert<K: Key>(&mut self, key: &K, value: V, ts: u64) -> Result<Option<V>, TrieError> {
        let (new_root, old_node) = match &self.root {
            None => {
                let mut commit_ts = ts;
                if ts == 0 {
                    commit_ts += 1;
                }
                (
                    Arc::new(Node::new_leaf(
                        key.as_slice().into(),
                        key.as_slice().into(),
                        value,
                        commit_ts,
                    )),
                    None,
                )
            }
            Some(root) => {
                // check if the given timestamp is older than the root's current timestamp
                // if so, return an error and do not insert the new node
                let curr_ts = root.ts();
                let mut commit_ts = ts;
                if ts == 0 {
                    commit_ts = curr_ts + 1;
                } else if curr_ts >= ts {
                    // TODO: check if this should be > because this means insertions with the ts equal to the root's ts will fail
                    return Err(TrieError::Other(
                        "given timestamp is older than root's current timestamp".to_string(),
                    ));
                }
                match Node::insert_recurse(root, key, value, commit_ts, 0) {
                    Ok((new_node, old_node)) => (new_node, old_node),
                    Err(err) => {
                        return Err(err);
                    }
                }
            }
        };

        self.root = Some(new_root);
        Ok(old_node)
    }

    pub fn remove<K: Key>(&mut self, key: &K) -> bool {
        let (new_root, is_deleted) = match &self.root {
            None => (None, false),
            Some(root) => {
                if root.is_leaf() {
                    (None, true)
                } else {
                    let (new_root, removed) = Node::remove_recurse(root, key, 0);
                    if removed {
                        (new_root, true)
                    } else {
                        (self.root.clone(), true)
                    }
                }
            }
        };

        self.root = new_root;
        is_deleted
    }

    pub fn get<K: Key>(&self, key: &K) -> Option<(&P, &V, &u64)> {
        Node::get_recurse(self.root.as_ref()?, key)
    }

    pub fn ts(&self) -> u64 {
        match &self.root {
            None => 0,
            Some(root) => root.ts(),
        }
    }

    pub fn create_snapshot(&self) -> Result<SnapshotPointer<P, V>, TrieError> {
        let max_snapshot_id = self.max_snapshot_id.load(Ordering::SeqCst);

        if max_snapshot_id >= self.max_active_snapshots {
            return Err(TrieError::Other(
                "max number of snapshots reached".to_string(),
            ));
        }

        let mut snapshots = self
            .snapshots
            .write()
            .map_err(|_| TrieError::SnapshotMutexError)?;

        // Increment the count atomically
        let new_snapshot_id = self.max_snapshot_id.fetch_add(1, Ordering::SeqCst);
        let new_snapshot = self.new_snapshot(new_snapshot_id)?;
        snapshots.insert(new_snapshot_id, new_snapshot);

        Ok(SnapshotPointer::new(self, new_snapshot_id))
    }

    pub(crate) fn get_snapshot(
        &self,
        snapshot_id: u64,
    ) -> Result<SnapshotPointer<P, V>, TrieError> {
        let snapshots = self
            .snapshots
            .read()
            .map_err(|_| TrieError::SnapshotMutexError)?;

        let _snapshot = snapshots
            .get(&snapshot_id)
            .ok_or(TrieError::SnapshotNotFound)?;
        Ok(SnapshotPointer::new(self, snapshot_id))
    }

    fn new_snapshot(&self, snapshot_id: u64) -> Result<Snapshot<P, V>, TrieError> {
        if self.root.is_none() {
            return Err(TrieError::Other(
                "cannot create snapshot from empty tree".to_string(),
            ));
        }

        let root = self.root.as_ref().unwrap();

        let snapshot = Snapshot {
            id: snapshot_id,
            ts: root.ts() + 1,
            root: RwLock::new(root.clone()),
            readers: RwLock::new(HashMap::new()),
            max_active_readers: AtomicU64::new(0),
            closed: false,
        };

        Ok(snapshot)
    }

    pub(crate) fn close(&self, snapshot_id: u64) -> Result<(), TrieError> {
        let mut snapshots = self
            .snapshots
            .write()
            .map_err(|_| TrieError::SnapshotMutexError)?;
        snapshots.remove(&snapshot_id);
        Ok(())
    }

    // Method to get the count of snapshots
    pub fn snapshot_count(&self) -> Result<usize, TrieError> {
        let snapshots = self
            .snapshots
            .read()
            .map_err(|_| TrieError::SnapshotMutexError)?;
        Ok(snapshots.len())
    }

    pub fn iter(&self) -> Iter<P, V> {
        Iter::new(self.root.as_ref())
    }

    pub fn range<'a, K: Key, R>(&'a self, range: R) -> Range<K, P, V>
    where
        R: RangeBounds<K> + 'a,
    {
        if self.root.is_none() {
            return Range::empty();
        }

        let mut iter = self.iter();

        let start_key = match range.start_bound() {
            Bound::Included(start_key) | Bound::Excluded(start_key) => start_key,
            Bound::Unbounded => {
                let bound = range.end_bound().cloned();
                return Range::for_iter(iter, bound);
            }
        };

        while let Some((k, _, _)) = iter.next() {
            if start_key.as_slice() == k.as_slice() {
                if let Bound::Excluded(_) = range.start_bound() {
                    iter.next();
                }
                let bound = range.end_bound().cloned();
                return Range::for_iter(iter, bound);
            }
        }

        Range::empty()
    }
}

/*
    Test cases for Adaptive Radix Tree
*/

#[cfg(test)]
mod tests {
    use super::Tree;
    use crate::ArrayPrefix;
    use crate::{ArrayKey, VectorKey};

    use rand::{thread_rng, Rng};
    use std::collections::BTreeMap;
    use std::fs::File;
    use std::io::{self, BufRead, BufReader};

    fn read_words_from_file(file_path: &str) -> io::Result<Vec<String>> {
        let file = File::open(file_path)?;
        let reader = BufReader::new(file);

        let words: Vec<String> = reader.lines().filter_map(|line| line.ok()).collect();

        Ok(words)
    }

    #[test]
    fn test_insert_many_words_and_ensure_search_and_delete_result() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();
        let file_path = "testdata/words.txt";
        match read_words_from_file(file_path) {
            Ok(words) => {
                for word in words {
                    let key = &VectorKey::from_str(&word);
                    tree.insert(key, 1, 0);
                }
            }
            Err(err) => {
                eprintln!("Error reading file: {}", err);
            }
        }
        assert_eq!(tree.ts(), 235886);

        match read_words_from_file(file_path) {
            Ok(words) => {
                for word in words {
                    let key = VectorKey::from_str(&word);
                    let (_, val, _ts) = tree.get(&key).unwrap();
                    assert_eq!(*val, 1);
                }
            }
            Err(err) => {
                eprintln!("Error reading file: {}", err);
            }
        }

        match read_words_from_file(file_path) {
            Ok(words) => {
                for word in words {
                    let key = VectorKey::from_str(&word);
                    assert!(tree.remove(&key));
                }
            }
            Err(err) => {
                eprintln!("Error reading file: {}", err);
            }
        }

        assert_eq!(tree.ts(), 0);
    }

    #[test]
    fn test_string_insert_delete() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
        tree.insert(&VectorKey::from_str("a"), 1, 0);
        tree.insert(&VectorKey::from_str("aa"), 1, 0);
        tree.insert(&VectorKey::from_str("aal"), 1, 0);
        tree.insert(&VectorKey::from_str("aalii"), 1, 0);

        assert!(tree.remove(&VectorKey::from_str("a")));
        assert!(tree.remove(&VectorKey::from_str("aa")));
        assert!(tree.remove(&VectorKey::from_str("aal")));
        assert!(tree.remove(&VectorKey::from_str("aalii")));

        tree.insert(&VectorKey::from_str("abc"), 2, 0);
        tree.insert(&VectorKey::from_str("abcd"), 1, 0);
        tree.insert(&VectorKey::from_str("abcde"), 3, 0);
        tree.insert(&VectorKey::from_str("xyz"), 4, 0);
        tree.insert(&VectorKey::from_str("axyz"), 6, 0);

        assert!(tree.remove(&VectorKey::from_str("abc")));
        assert!(tree.remove(&VectorKey::from_str("abcde")));
        assert!(tree.remove(&VectorKey::from_str("abcd")));
        assert!(tree.remove(&VectorKey::from_str("xyz")));
        assert!(tree.remove(&VectorKey::from_str("axyz")));
    }

    #[test]
    fn test_string_long() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
        tree.insert(&VectorKey::from_str("amyelencephalia"), 1, 0);
        tree.insert(&VectorKey::from_str("amyelencephalic"), 2, 0);
        tree.insert(&VectorKey::from_str("amyelencephalous"), 3, 0);

        let (_, val, _ts) = tree.get(&VectorKey::from_str("amyelencephalia")).unwrap();
        assert_eq!(*val, 1);

        let (_, val, _ts) = tree.get(&VectorKey::from_str("amyelencephalic")).unwrap();
        assert_eq!(*val, 2);

        let (_, val, _ts) = tree.get(&VectorKey::from_str("amyelencephalous")).unwrap();
        assert_eq!(*val, 3);
    }

    #[test]
    fn test_root_set_get() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
        let key = VectorKey::from_str("abc");
        tree.insert(&key, 1, 0);
        let (_, val, _ts) = tree.get(&key).unwrap();
        assert_eq!(*val, 1);
    }

    #[test]
    fn test_string_duplicate_insert() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
        let result = tree
            .insert(&VectorKey::from_str("abc"), 1, 0)
            .expect("Failed to insert");
        assert!(result.is_none());
        let result = tree
            .insert(&VectorKey::from_str("abc"), 1, 0)
            .expect("Failed to insert");
        assert!(result.is_some());
    }

    // Inserting a single value into the tree and removing it should result in a nil tree root.
    #[test]
    fn test_insert_and_remove() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

        let key = &VectorKey::from_str("test");
        tree.insert(key, 1, 0);

        assert!(tree.remove(key));
        assert!(tree.get(key).is_none());
    }

    // Inserting Two values into the tree and removing one of them
    // should result in a tree root of type LEAF
    #[test]
    fn test_insert2_and_remove1_and_root_should_be_node4() {
        let key1 = &VectorKey::from_str("test1");
        let key2 = &VectorKey::from_str("test2");

        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
        tree.insert(key1, 1, 0);
        tree.insert(key2, 1, 0);

        assert!(tree.remove(key1));
        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert_eq!(root.node_type_name(), "Node4");
    }

    // // Inserting Two values into a tree and deleting them both
    // // should result in a nil tree root
    // // This tests the expansion of the root into a NODE4 and
    // // successfully collapsing into a LEAF and then nil upon successive removals
    // #[test]
    // fn test_insert2_and_remove2_and_root_should_be_nil() {
    //     let key1 = &VectorKey::from_str("test1");
    //     let key2 = &VectorKey::from_str("test2");

    //     let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
    //     tree.insert(key1, 1, 0);
    //     tree.insert(key2, 1, 0);

    //     assert_eq!(tree.remove(key1), true);
    //     assert_eq!(tree.remove(key2), true);

    //     assert!(tree.root.is_none());
    // }

    // Inserting Five values into a tree and deleting one of them
    // should result in a tree root of type NODE4
    // This tests the expansion of the root into a NODE16 and
    // successfully collapsing into a NODE4 upon successive removals
    #[test]
    fn test_insert5_and_remove1_and_root_should_be_node4() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

        for i in 0..5u32 {
            let key = &VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1, 0);
        }

        assert!(
            tree.remove(&VectorKey::from_slice(&1u32.to_be_bytes()))
        );

        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert!(root.is_inner());
        assert_eq!(root.node_type_name(), "Node4");
    }

    //     // Inserting Five values into a tree and deleting all of them
    //     // should result in a tree root of type nil
    //     // This tests the expansion of the root into a NODE16 and
    //     // successfully collapsing into a NODE4, Leaf, then nil
    //     #[test]
    //     fn test_insert5_and_remove5_and_root_should_be_nil() {
    //         let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

    //         for i in 0..5u32 {
    //             let key = &VectorKey::from_slice(&i.to_be_bytes());
    //             tree.insert(key, 1);
    //         }

    //         for i in 0..5u32 {
    //             let key = &VectorKey::from_slice(&i.to_be_bytes());
    //             tree.remove(key);
    //         }

    //         assert!(tree.root.is_none());
    //     }

    // Inserting 17 values into a tree and deleting one of them should
    // result in a tree root of type NODE16
    // This tests the expansion of the root into a NODE48, and
    // successfully collapsing into a NODE16
    #[test]
    fn test_insert17_and_remove1_and_root_should_be_node16() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

        for i in 0..17u32 {
            let key = &VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1, 0);
        }

        assert!(
            tree.remove(&VectorKey::from_slice(&2u32.to_be_bytes()))
        );

        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert!(root.is_inner());
        assert_eq!(root.node_type_name(), "Node16");
    }

    #[test]
    fn test_insert17_and_root_should_be_node48() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

        for i in 0..17u32 {
            let key = VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1, 0);
        }

        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert!(root.is_inner());
        assert_eq!(root.node_type_name(), "Node48");
    }

    // // Inserting 17 values into a tree and removing them all should
    // // result in a tree of root type nil
    // // This tests the expansion of the root into a NODE48, and
    // // successfully collapsing into a NODE16, NODE4, Leaf, and then nil
    // #[test]
    // fn test_insert17_and_remove17_and_root_should_be_nil() {
    //     let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

    //     for i in 0..17u32 {
    //         let key = VectorKey::from_slice(&i.to_be_bytes());
    //         tree.insert(&key, 1);
    //     }

    //     for i in 0..17u32 {
    //         let key = VectorKey::from_slice(&i.to_be_bytes());
    //         tree.remove(&key);
    //     }

    //     assert!(tree.root.is_none());
    // }

    // Inserting 49 values into a tree and removing one of them should
    // result in a tree root of type NODE48
    // This tests the expansion of the root into a NODE256, and
    // successfully collapasing into a NODE48
    #[test]
    fn test_insert49_and_remove1_and_root_should_be_node48() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

        for i in 0..49u32 {
            let key = &VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1, 0);
        }

        assert!(
            tree.remove(&VectorKey::from_slice(&2u32.to_be_bytes()))
        );

        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert!(root.is_inner());
        assert_eq!(root.node_type_name(), "Node48");
    }

    #[test]
    fn test_insert49_and_root_should_be_node248() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

        for i in 0..49u32 {
            let key = &VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1, 0);
        }

        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert!(root.is_inner());
        assert_eq!(root.node_type_name(), "Node256");
    }

    //     // // Inserting 49 values into a tree and removing all of them should
    //     // // result in a nil tree root
    //     // // This tests the expansion of the root into a NODE256, and
    //     // // successfully collapsing into a Node48, Node16, Node4, Leaf, and finally nil
    //     // #[test]
    //     // fn test_insert49_and_remove49_and_root_should_be_nil() {
    //     //     let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

    //     //     for i in 0..49u32 {
    //     //         let key = &VectorKey::from_slice(&i.to_be_bytes());
    //     //         tree.insert(key, 1);
    //     //     }

    //     //     for i in 0..49u32 {
    //     //         let key = VectorKey::from_slice(&i.to_be_bytes());
    //     //         assert_eq!(tree.remove(&key), true);
    //     //     }

    //     //     assert!(tree.root.is_none());
    //     // }

    #[derive(Debug, Clone, PartialEq)]
    struct KVT {
        k: Vec<u8>, // Key
        ts: u64,    // Timestamp
    }

    #[test]
    fn test_timed_insertion() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();

        let kvts = vec![
            KVT {
                k: b"key1_0".to_vec(),
                ts: 0,
            },
            KVT {
                k: b"key2_0".to_vec(),
                ts: 0,
            },
            KVT {
                k: b"key3_0".to_vec(),
                ts: 0,
            },
            KVT {
                k: b"key4_0".to_vec(),
                ts: 0,
            },
            KVT {
                k: b"key5_0".to_vec(),
                ts: 0,
            },
            KVT {
                k: b"key6_0".to_vec(),
                ts: 0,
            },
        ];

        for kvt in &kvts {
            assert!(tree
                .insert(&VectorKey::from(kvt.k.to_vec()), 1, kvt.ts)
                .is_ok());
        }

        let mut curr_ts = 1;
        for kvt in &kvts {
            let (_, val, ts) = tree.get(&VectorKey::from(kvt.k.to_vec())).unwrap();
            assert_eq!(*val, 1);

            if kvt.ts == 0 {
                // zero-valued timestamps should be associated with current time plus one
                assert_eq!(curr_ts, *ts);
            } else {
                assert_eq!(kvt.ts, *ts);
            }

            curr_ts += 1;
        }

        // root's ts should match the greatest inserted timestamp
        assert_eq!(kvts.len() as u64, tree.ts());
    }

    #[test]
    fn test_timed_insertion_update_same_key() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();

        let key1 = &VectorKey::from_str("key_1");

        // insert key1 with ts 0
        assert!(tree.insert(key1, 1, 0).is_ok());
        // update key1 with ts 0
        assert!(tree.insert(key1, 1, 0).is_ok());

        // get key1 should return ts 2 as the same key was inserted and updated
        let (_, val, ts) = tree.get(key1).unwrap();
        assert_eq!(*val, 1);
        assert_eq!(*ts, 2);

        // update key1 with older timestamp should fail
        assert!(tree.insert(key1, 1, 1).is_err());
        assert_eq!(tree.ts(), 2);

        // update key1 with newer timestamp should pass
        assert!(tree.insert(key1, 1, 8).is_ok());
        let (_, val, ts) = tree.get(key1).unwrap();
        assert_eq!(*val, 1);
        assert_eq!(*ts, 8);

        assert_eq!(tree.ts(), 8);
    }

    #[test]
    fn test_timed_insertion_update_non_increasing_ts() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();

        let key1 = &VectorKey::from_str("key_1");
        let key2 = &VectorKey::from_str("key_2");

        assert!(tree.insert(key1, 1, 10).is_ok());
        let initial_ts = tree.ts();

        assert!(tree.insert(key1, 1, 2).is_err());
        assert_eq!(initial_ts, tree.ts());
        let (_, val, ts) = tree.get(key1).unwrap();
        assert_eq!(*val, 1);
        assert_eq!(*ts, 10);

        assert!(tree.insert(key2, 1, 15).is_ok());
        let initial_ts = tree.ts();

        assert!(tree.insert(key2, 1, 11).is_err());
        assert_eq!(initial_ts, tree.ts());
        let (_, val, ts) = tree.get(key2).unwrap();
        assert_eq!(*val, 1);
        assert_eq!(*ts, 15);

        // check if the max timestamp of the tree is the max of the two inserted timestamps
        assert_eq!(tree.ts(), 15);
    }

    #[test]
    fn test_timed_insertion_update_equal_to_root_ts() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();

        let key1 = &VectorKey::from_str("key_1");
        let key2 = &VectorKey::from_str("key_2");

        assert!(tree.insert(key1, 1, 10).is_ok());
        let initial_ts = tree.ts();
        assert!(tree.insert(key2, 1, initial_ts).is_err());
    }

    #[test]
    fn test_timed_deletion_root_ts() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();

        assert!(tree.insert(&VectorKey::from_str("key_1"), 1, 0).is_ok());
        assert!(tree.insert(&VectorKey::from_str("key_2"), 1, 0).is_ok());
        assert_eq!(tree.ts(), 2);

        assert!(tree.remove(&VectorKey::from_str("key_1")));
        assert!(tree.remove(&VectorKey::from_str("key_2")));
        assert_eq!(tree.ts(), 0);
    }

    fn from_be_bytes_key(k: &Vec<u8>) -> u64 {
        let k = if k.len() < 8 {
            let mut new_k = vec![0; 8];
            new_k[8 - k.len()..].copy_from_slice(k);
            new_k
        } else {
            k.clone()
        };
        let k = k.as_slice();

        u64::from_be_bytes(k[0..8].try_into().unwrap())
    }

    #[test]
    fn test_iter_seq_u16() {
        let mut tree = Tree::<ArrayPrefix<16>, u16>::new();
        for i in 0..=u16::MAX {
            let key: ArrayKey<32> = i.into();
            tree.insert(&key, i, 0);
        }

        let mut len = 0usize;
        let mut expected = 0u16;

        let tree_iter = tree.iter();
        for tree_entry in tree_iter {
            let k = from_be_bytes_key(&tree_entry.0);
            assert_eq!(expected as u64, k);
            expected = expected.wrapping_add(1);
            len += 1;
        }
        assert_eq!(len, u16::MAX as usize + 1);
    }

    #[test]
    fn test_iter_seq_u8() {
        let mut tree = Tree::<ArrayPrefix<16>, u8>::new();
        for i in 0..=u8::MAX {
            let key: ArrayKey<32> = i.into();
            tree.insert(&key, i, 0);
        }

        let mut len = 0usize;
        let mut expected = 0u8;

        let tree_iter = tree.iter();
        for tree_entry in tree_iter {
            let k = from_be_bytes_key(&tree_entry.0);
            assert_eq!(expected as u64, k);
            expected = expected.wrapping_add(1);
            len += 1;
        }
        assert_eq!(len, u8::MAX as usize + 1);
    }

    #[test]
    fn test_range() {
        let mut tree = Tree::<ArrayPrefix<16>, u64>::new();
        let count = 10000;
        let mut rng = thread_rng();
        let mut keys_inserted = BTreeMap::new();
        for i in 0..count {
            let _value = i;
            let random_val = rng.gen_range(0..count);
            let random_key: ArrayKey<16> = random_val.into();
            if tree.get(&random_key).is_none() && tree.insert(&random_key, random_val, 0).unwrap().is_none()
            {
                let result = tree.get(&random_key);
                assert!(result.is_some());
                keys_inserted.insert(random_val, random_val);
            }
        }

        let end_key: ArrayKey<16> = 100u64.into();
        let art_range = tree.range(..end_key);
        let btree_range = keys_inserted.range(..100);
        for (art_entry, btree_entry) in art_range.zip(btree_range) {
            let art_key = from_be_bytes_key(&art_entry.0);
            assert_eq!(art_key, *btree_entry.0);
            assert_eq!(art_entry.1, btree_entry.1);
        }
    }
}
