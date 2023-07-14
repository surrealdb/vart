use std::mem;
use std::{cmp::min, fmt::Debug};

use crate::{ArrayPartial, Key, Partial};

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
const NODE256MAX: usize = 256;

// Metadata associated with each node
#[derive(Debug, Clone)]
struct Meta<P: Partial> {
    prefix: P,           // Prefix associated with the node
    num_children: usize, // Number of children nodes
}

// Type of the node
#[derive(Debug, PartialEq, Clone)]
pub(crate) enum NodeType {
    Node4,   // Node with 4 keys and 4 children
    Node16,  // Node with 16 keys and 16 children
    Node48,  // Node with 256 keys and 48 children
    Node256, // Node with 256 keys and 256 children
}

// Inner node of the adaptive radix trie
#[derive(Debug, Clone)]
struct InnerNode<P: Partial, V> {
    meta: Meta<P>,       // Metadata of the node
    node_type: NodeType, // Type of the node

    // TODO: change this to an array
    keys: Box<[u8]>,             // Array of keys
    children: Box<[Node<P, V>]>, // Array of child nodes
}

// Leaf node of the adaptive radix trie
#[derive(Debug, Clone)]
struct LeafNode<P: Partial, V> {
    key: P,       // Key associated with the leaf node
    pub value: V, // Value associated with the leaf node
}

// From the specification: Radix trees consist of two types of nodes:
// Inner nodes, which map partial keys to other nodes,
// and leaf nodes, which store the values corresponding to the keys.
#[derive(Debug, Clone, Default)]
enum Node<P: Partial, V> {
    #[default]
    Empty, // Empty node #[default] Empty
    Leaf(Box<LeafNode<P, V>>),   // Leaf node
    Inner(Box<InnerNode<P, V>>), // Inner node
}

// Adaptive radix trie
pub trait PartialTrait: Partial + Clone + for<'a> From<&'a [u8]> {}
impl<T> PartialTrait for T where T: Partial + Clone + for<'a> From<&'a [u8]> {}

#[derive(Debug, Clone)]
pub struct Tree<P: PartialTrait, V> {
    root: Option<Node<P, V>>, // Root node of the tree
    size: u64,                // Number of elements in the tree
}

// Default implementation for the Tree struct
impl<P: PartialTrait, V> Default for Tree<P, V> {
    fn default() -> Self {
        Tree {
            root: None,
            size: 0,
        }
    }
}

// Implementation of methods for the Meta struct
impl<P: PartialTrait + Clone> Meta<P> {
    // Create a new Meta instance with the given prefix, prefix length, and number of children
    fn new(prefix: P, num_children: usize) -> Self {
        Meta {
            prefix: prefix,
            num_children,
        }
    }
}

// Implementation of methods for the LeafNode struct
impl<P: PartialTrait + Clone, V> LeafNode<P, V> {
    // Create a new LeafNode instance with the given key and value
    pub fn new(key: P, value: V) -> Self {
        Self { key: key, value }
    }
}

impl<P: PartialTrait, V> InnerNode<P, V> {
    // From the specification: The smallest node type can store up to 4 child
    // pointers and uses an array of length 4 for keys and another
    // array of the same length for pointers. The keys and pointers
    // are stored at corresponding positions and the keys are sorted.
    #[inline] // TODO: check if this is required
    fn new_node4(meta: Meta<P>) -> InnerNode<P, V> {
        let children: [Node<P, V>; NODE4MAX] = [Node::<P, V>::INIT; NODE4MAX];
        let keys: [u8; NODE4MAX] = [0; NODE4MAX];

        Self {
            meta: meta,
            node_type: NodeType::Node4,
            keys: Box::new(keys),
            children: Box::new(children),
        }
    }

    // From the specification: This node type is used for storing between 5 and
    // 16 child pointers. Like the Node4, the keys and pointers
    // are stored in separate arrays at corresponding positions, but
    // both arrays have space for 16 entries. A key can be found
    // efﬁciently with binary search or, on modern hardware, with
    // parallel comparisons using SIMD instructions.
    #[inline]
    fn new_node16(meta: Meta<P>) -> InnerNode<P, V> {
        let children: [Node<P, V>; NODE16MAX] = [Node::<P, V>::INIT; NODE16MAX];
        let keys: [u8; NODE16MAX] = [0; NODE16MAX];

        Self {
            meta: meta,
            node_type: NodeType::Node16,
            keys: Box::new(keys),
            children: Box::new(children),
        }
    }

    // From the specification: As the number of entries in a node increases,
    // searching the key array becomes expensive. Therefore, nodes
    // with more than 16 pointers do not store the keys explicitly.
    // Instead, a 256-element array is used, which can be indexed
    // with key bytes directly. If a node has between 17 and 48 child
    // pointers, this array stores indexes into a second array which
    // contains up to 48 pointers.
    #[inline]
    fn new_node48(meta: Meta<P>) -> InnerNode<P, V> {
        let children: [Node<P, V>; NODE48MAX] = [Node::<P, V>::INIT; NODE48MAX];
        let keys: [u8; NODE256MAX] = [0; NODE256MAX];

        Self {
            meta: meta,
            node_type: NodeType::Node48,
            keys: Box::new(keys),
            children: Box::new(children),
        }
    }

    // From the specification: The largest node type is simply an array of 256
    // pointers and is used for storing between 49 and 256 entries.
    // With this representation, the next node can be found very
    // efﬁciently using a single lookup of the key byte in that array.
    // No additional indirection is necessary. If most entries are not
    // null, this representation is also very space efﬁcient because
    // only pointers need to be stored.
    #[inline]
    fn new_node256(meta: Meta<P>) -> InnerNode<P, V> {
        let children: [Node<P, V>; NODE256MAX] = [Node::<P, V>::INIT; NODE256MAX];

        Self {
            meta: meta,
            node_type: NodeType::Node256,
            keys: Box::new([]),
            children: Box::new(children),
        }
    }

    #[inline]
    fn minimum_size(&self) -> usize {
        match self.node_type {
            NodeType::Node4 { .. } => NODE4MIN,
            NodeType::Node16 { .. } => NODE16MIN,
            NodeType::Node48 { .. } => NODE48MIN,
            NodeType::Node256 { .. } => NODE256MIN,
        }
    }

    #[inline]
    fn maximum_size(&self) -> usize {
        match self.node_type {
            NodeType::Node4 { .. } => NODE4MAX,
            NodeType::Node16 { .. } => NODE16MAX,
            NodeType::Node48 { .. } => NODE48MAX,
            NodeType::Node256 { .. } => NODE256MAX,
        }
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.meta.num_children == self.maximum_size()
    }

    #[inline]
    fn add_child(&mut self, key: u8, child: Node<P, V>) {
        if self.is_full() {
            self.grow();
        }

        let m = self.meta.num_children;

        match self.node_type {
            NodeType::Node4 => {
                let idx = self.keys[0..m].iter().position(|&c| key < c).unwrap_or(m);
                for i in (idx..m).rev() {
                    self.keys[i + 1] = self.keys[i];
                    self.children[i + 1] = mem::replace(&mut self.children[i], Node::Empty);
                }
                self.keys[idx] = key;
                self.children[idx] = child;
                self.meta.num_children += 1;
            }
            NodeType::Node16 => {
                let idx = self.keys[0..m].iter().position(|&c| key < c).unwrap_or(m);
                for i in (idx..m).rev() {
                    self.keys[i + 1] = self.keys[i];
                    self.children[i + 1] = mem::replace(&mut self.children[i], Node::Empty);
                }

                self.keys[idx] = key;
                self.children[idx] = child;
                self.meta.num_children += 1;
            }
            NodeType::Node48 => {
                let i = key as usize;
                if self.keys[i] == 0 {
                    self.keys[i] = (m + 1) as u8;
                    self.children[m] = child;
                    self.meta.num_children += 1;
                }
            }
            NodeType::Node256 => {
                self.meta.num_children += 1;
                self.children[key as usize] = child;
            }
        }
    }

    // Grows the current ArtNode to the next biggest size.
    // ArtNodes of type NODE4 will grow to NODE16
    // ArtNodes of type NODE16 will grow to NODE48.
    // ArtNodes of type NODE48 will grow to NODE256.
    // ArtNodes of type NODE256 will not grow, as they are the biggest type of ArtNodes
    #[inline]
    fn grow(&mut self) {
        match self.node_type {
            NodeType::Node4 => {
                // TODO: don't clone, change node to struct and add prefix
                let mut n16 = InnerNode::new_node16(self.meta.clone());
                for i in 0..self.meta.num_children {
                    n16.keys[i] = self.keys[i];
                    n16.children[i] = mem::replace(&mut self.children[i], Node::Empty);
                }
                *self = n16;
            }
            NodeType::Node16 => {
                // TODO: don't clone, change node to struct and add prefix
                let mut n48 = InnerNode::new_node48(self.meta.clone());
                for i in 0..self.meta.num_children {
                    n48.keys[self.keys[i] as usize] = (i + 1) as u8;
                    n48.children[i] = mem::replace(&mut self.children[i], Node::Empty);
                }
                *self = n48;
            }
            NodeType::Node48 => {
                // TODO: don't clone, change node to struct and add prefix
                let mut n256 = InnerNode::new_node256(self.meta.clone());

                for i in 0..self.keys.len() {
                    let child = self.find_child_mut(i as u8);
                    if let Some(child_node) = child {
                        if !child_node.is_empty() {
                            n256.children[i] = mem::take(child_node);
                        }
                    }
                }
                *self = n256;
            }
            NodeType::Node256 => {}
        }
    }

    #[inline]
    fn index(&self, key: u8) -> Option<usize> {
        match self.node_type {
            // ArtNodes of type NODE4 have a relatively simple lookup algorithm since
            // they are of very small size:  Simply iterate over all keys and check to
            // see if they match.
            NodeType::Node4 => {
                self.keys[0..min(NODE16MAX, self.meta.num_children)]
                    .iter()
                    .position(|&c| key == c)
            }
            NodeType::Node16 => self.keys[0..min(NODE16MAX, self.meta.num_children)]
                .iter()
                .position(|&c| key == c),
            // ArtNodes of type NODE48 store the indicies in which to access their children
            // in the keys array which are byte-accessible by the desired key.
            // However, when this key array initialized, it contains many 0 value indicies.
            // In order to distinguish if a child actually exists, we increment this value
            // during insertion and decrease it during retrieval.
            NodeType::Node48 => {
                let idx = self.keys[key as usize];
                if idx > 0 {
                    Some((idx - 1) as usize)
                } else {
                    None
                }
            }
            // ArtNodes of type NODE256 possibly have the simplest lookup algorithm.
            // Since all of their keys are byte-addressable, we can simply index to the
            // specific child with the key.
            NodeType::Node256 => Some(key as usize),
        }
    }

    #[inline]
    fn find_child(&self, key: u8) -> Option<&Node<P, V>> {
        let idx = self.index(key)?;
        match self.node_type {
            NodeType::Node4 => Some(&self.children[idx]),
            NodeType::Node16 => Some(&self.children[idx]),
            NodeType::Node48 => {
                let i = self.keys[key as usize] as usize;
                Some(&self.children[i - 1])
            }
            NodeType::Node256 => {
                let node = &self.children[key as usize];
                if node.is_empty() {
                    None
                } else {
                    Some(node)
                }
            }
        }
    }

    // Returns a mutablepointer to the child that matches
    // the passed in key, or none if not present.
    #[inline]
    fn find_child_mut(&mut self, key: u8) -> Option<&mut Node<P, V>> {
        let idx = self.index(key)?;
        match &mut self.node_type {
            NodeType::Node4 => {
                Some(&mut self.children[idx])
            }
            NodeType::Node16 => Some(&mut self.children[idx]),
            NodeType::Node48 => {
                let i = self.keys[key as usize] as usize;
                Some(&mut self.children[i - 1])
            }
            NodeType::Node256 => {
                let node = &mut self.children[key as usize];
                if node.is_empty() {
                    None
                } else {
                    Some(node)
                }
            }
        }
    }
}

// Implementation of methods for the Node enum
impl<P: PartialTrait, V> Node<P, V> {
    const INIT: Self = Node::Empty;

    // Check if the node is empty
    #[inline]
    fn is_empty(&self) -> bool {
        matches!(self, Node::Empty)
    }

    fn delete_child(&mut self, key: u8) {
        match self {
            Node::Inner(inner) => {
                let Some(idx) = inner.index(key) else {
                    return
                };

                match inner.node_type {
                    NodeType::Node4 | NodeType::Node16 => {
                        inner.keys[idx] = 0;
                        inner.children[idx] = Node::Empty;
                        for i in idx..inner.meta.num_children - 1 {
                            inner.keys[i] = inner.keys[i + 1];
                            inner.children[i] = mem::take(&mut inner.children[i + 1]);
                        }
                        inner.keys[inner.meta.num_children - 1] = 0;
                        inner.children[inner.meta.num_children - 1] = Node::Empty;
                        inner.meta.num_children -= 1;
                    }
                    NodeType::Node48 => {
                        let key_idx = key as usize;
                        if inner.keys[key_idx] != 0 {
                            let val_idx = inner.keys[key_idx] - 1;
                            let val = mem::take(&mut inner.children[val_idx as usize]);
                            inner.keys[key_idx] = 0;
                            if inner.meta.num_children == 1 {
                                inner.meta.num_children = 0;
                            } else {
                                for i in 0..inner.keys.len() {
                                    if inner.keys[i] == inner.meta.num_children as u8 {
                                        inner.keys[i] = val_idx + 1;
                                        inner.children[val_idx as usize] = mem::take(
                                            &mut inner.children
                                                [inner.meta.num_children as usize - 1],
                                        );
                                        break;
                                    }
                                }
                            }
                        }
                        inner.meta.num_children -= 1;
                    }
                    NodeType::Node256 => {
                        let child = &inner.children[idx];
                        if !child.is_empty() {
                            inner.children[idx] = Node::Empty;
                            inner.meta.num_children -= 1;
                        }
                    }
                }

                if inner.meta.num_children < inner.minimum_size() {
                    self.shrink();
                }
            }
            Node::Leaf(_) | Node::Empty => {} // do nothing
        }
    }

    fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf(_))
    }

    fn is_inner(&self) -> bool {
        matches!(self, Node::Inner(_))
    }

    fn inner_node(&mut self) -> Option<&mut InnerNode<P, V>> {
        match self {
            Node::Inner(inner) => Some(inner),
            _ => None,
        }
    }

    fn leaf_node(&mut self) -> Option<&mut LeafNode<P, V>> {
        match self {
            Node::Leaf(leaf) => Some(leaf),
            _ => None,
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
        match self {
            Node::Inner(inner) => match inner.node_type {
                NodeType::Node4 => {
                    let mut node4 = InnerNode::new_node4(inner.meta.clone());
                    node4.meta.num_children = 0;

                    for i in 0..inner.meta.num_children {
                        node4.keys[i] = inner.keys[i];
                        node4.children[i] = mem::take(&mut inner.children[i]);
                        node4.meta.num_children += 1;
                    }

                    *self = Node::Inner(Box::new(node4));
                }
                NodeType::Node16 => {
                    let mut node4 = InnerNode::new_node4(inner.meta.clone());
                    node4.meta.num_children = 0;

                    for i in 0..inner.meta.num_children {
                        node4.keys[i] = inner.keys[i];
                        node4.children[i] = mem::take(&mut inner.children[i]);
                        node4.meta.num_children += 1;
                    }

                    *self = Node::Inner(Box::new(node4));
                }
                NodeType::Node48 => {
                    let mut node16 = InnerNode::new_node16(inner.meta.clone());
                    node16.meta.num_children = 0;
                    for i in 0..inner.keys.len() {
                        let pos = inner.keys[i] as usize;
                        if pos != 0 {
                            node16.children[node16.meta.num_children] =
                                mem::take(&mut inner.children[pos - 1]);
                            node16.keys[node16.meta.num_children] = i as u8;
                            node16.meta.num_children += 1;
                        }
                    }
                    *self = Node::Inner(Box::new(node16));
                }
                NodeType::Node256 => {
                    let mut node48 = InnerNode::new_node48(inner.meta.clone());
                    node48.meta.num_children = 0;

                    for i in 0..256 {
                        let child = &mut inner.children[i];
                        if !child.is_empty() {
                            node48.children[node48.meta.num_children] = mem::take(child);
                            node48.keys[i] = (node48.meta.num_children + 1) as u8;
                            node48.meta.num_children += 1;
                        }
                    }

                    *self = Node::Inner(Box::new(node48));
                }
            },
            Node::Leaf(_) | Node::Empty => {} // do nothing
        }
    }

    pub fn add_child(&mut self, key: u8, node: Node<P, V>) {
        match self {
            Node::Inner(inner) => {
                inner.add_child(key, node);
            }
            Node::Leaf(_) => panic!("Should not be possible."),
            Node::Empty => panic!("Should not be possible."),
        }
    }

    pub fn num_children(&self) -> usize {
        match self {
            Node::Inner(n) => n.meta.num_children,
            Node::Leaf(n) => 0,
            Node::Empty => panic!("Should not be possible."),
        }
    }

    fn prefix_clone(&self) -> P {
        match self {
            Node::Inner(n) => n.meta.prefix.clone(),
            Node::Leaf(n) => n.key.clone(),
            Node::Empty => panic!("Should not be possible."),
        }
    }

    fn prefix(&self) -> &P {
        match self {
            Node::Inner(n) => &n.meta.prefix,
            Node::Leaf(n) => &n.key,
            Node::Empty => panic!("Should not be possible."),
        }
    }

    fn prefix_len(&self) -> usize {
        match self {
            Node::Inner(n) => n.meta.prefix.length(),
            Node::Leaf(n) => n.key.length(),
            Node::Empty => panic!("Should not be possible."),
        }
    }

    fn set_prefix(&mut self, prefix: P) {
        match self {
            Node::Inner(n) => {
                n.meta.prefix = prefix;
            }
            Node::Leaf(n) => {
                n.key = prefix;
            }
            Node::Empty => panic!("Should not be possible."),
        }
    }

    pub fn value(&self) -> Option<&V> {
        let Node::Leaf(leaf) = &self else {
            return None;
        };
        Some(&leaf.value)
    }

    pub fn find_child(&self, key: u8) -> Option<&Node<P, V>> {
        if self.num_children() == 0 {
            return None;
        }

        match self {
            Node::Inner(inner) => inner.find_child(key),
            Node::Leaf(_) => None,
            Node::Empty => panic!("Should not be possible."),
        }
    }

    pub fn find_child_mut(&mut self, key: u8) -> Option<&mut Node<P, V>> {
        if self.num_children() == 0 {
            return None;
        }

        match self {
            Node::Inner(inner) => inner.find_child_mut(key),
            Node::Leaf(_) => None,
            Node::Empty => panic!("Should not be possible."),
        }
    }

    pub fn node_type_name(&self) -> String {
        match self {
            Node::Inner(inner) => match &inner.node_type {
                NodeType::Node4 => "Node4".to_string(),
                NodeType::Node16 => "Node16".to_string(),
                NodeType::Node48 => "Node48".to_string(),
                NodeType::Node256 => "Node256".to_string(),
            },
            Node::Leaf(_) => "Leaf".to_string(),
            Node::Empty => panic!("Should not be possible."),
        }
    }
}

impl<P: PartialTrait, V> Tree<P, V> {
    pub fn new() -> Self {
        Tree {
            root: None,
            size: 0,
        }
    }

    pub fn insert<K: Key>(&mut self, key: &K, value: V) -> Option<V> {
        if self.root.is_none() {
            self.root = Some(Node::Leaf(Box::new(LeafNode::new(
                key.partial_after(0).into(),
                value,
            ))));
            return None;
        };

        let root = self.root.as_mut().unwrap();
        return Tree::insert_recurse(root, key, value, 0);
    }

    fn insert_recurse<K: Key>(
        cur_node: &mut Node<P, V>,
        key: &K,
        value: V,
        depth: usize,
    ) -> Option<V> {
        let cur_node_prefix = cur_node.prefix_clone();
        let cur_node_prefix_len = cur_node.prefix_len();

        let key_prefix = key.partial_after(depth);
        let longest_common_prefix = cur_node_prefix.longest_common_prefix(key_prefix);

        let new_key = cur_node_prefix.partial_after(longest_common_prefix);
        let partial = cur_node_prefix.partial_before(longest_common_prefix);
        let partial_len = partial.length();

        let is_prefix_match = min(cur_node_prefix_len, key_prefix.len()) == longest_common_prefix;

        if let Node::Leaf(ref mut leaf) = cur_node {
            if is_prefix_match && leaf.key.length() == key_prefix.len() {
                return Some(mem::replace(&mut leaf.value, value));
            }
        }

        if !is_prefix_match {
            cur_node.set_prefix(new_key);

            let mut n4: InnerNode<P, V> = InnerNode::new_node4(Meta::new(partial, 0));
            let n4_node: Node<P, V> = Node::Inner(Box::new(n4));
            let replacement_current = mem::replace(cur_node, n4_node);

            let k1 = cur_node_prefix.at(longest_common_prefix);
            let k2 = key_prefix[longest_common_prefix];
            let new_leaf = LeafNode::new(key_prefix[longest_common_prefix..].into(), value);

            cur_node.add_child(k1, replacement_current);
            cur_node.add_child(k2, Node::Leaf(Box::new(new_leaf)));

            return None;
        }

        let k = key_prefix[longest_common_prefix];

        if let Node::Inner(ref mut inner) = cur_node {
            let next_child = inner.find_child_mut(k);
            if let Some(child) = next_child {
                return Tree::insert_recurse(child, key, value, depth + longest_common_prefix);
            }
        }

        let new_leaf = LeafNode::new(key_prefix[longest_common_prefix..].into(), value);
        cur_node.add_child(k, Node::Leaf(Box::new(new_leaf)));
        return None;
    }

    pub fn remove<K: Key>(&mut self, key: &K) -> bool {
        if self.root.is_none() {
            return false;
        }

        let root = self.root.as_mut().unwrap();
        if root.is_leaf() {
            mem::take(root);
            self.root = None;
            return true;
        }

        // // This is a special case where the root is an inner node and has no children
        // // This is because currently the Node4 is not shrunk to a leaf
        // if root.is_inner(){
        //     let inner = root.inner_node().unwrap();
        //     if inner.meta.num_children == 0{
        //         mem::take(root);
        //         self.root = None;
        //         return true;
        //     }
        // }

        return Tree::remove_recurse(&mut self.root.as_mut(), key, 0);
    }

    fn remove_recurse<K: Key>(
        cur_node_ptr: &mut Option<&mut Node<P, V>>,
        key: &K,
        mut depth: usize,
    ) -> bool {
        if cur_node_ptr.is_none() {
            return false;
        }

        let cur_node = cur_node_ptr.as_mut().unwrap();
        if cur_node.is_empty() {
            return false;
        }

        let prefix = cur_node.prefix();
        let prefix_len = cur_node.prefix_len();
        let key_prefix = key.partial_after(depth);
        let longest_common_prefix = prefix.longest_common_prefix(key_prefix);
        let is_prefix_match = min(prefix_len, key_prefix.len()) == longest_common_prefix;

        if is_prefix_match && prefix_len == key_prefix.len() {
            *cur_node_ptr = None;
            return true;
        }

        let k = key_prefix[longest_common_prefix];

        let inner = cur_node.inner_node().unwrap();
        let next_child = &mut inner.find_child_mut(k);

        if let Some(child) = next_child {
            if child.num_children() == 0 {
                if child.prefix_len() == key_prefix.len() - longest_common_prefix {
                    cur_node.delete_child(k);
                    return true;
                }
                return false;
            }

            return Tree::remove_recurse(next_child, key, depth + longest_common_prefix);
        }

        return false;
    }

    pub fn get<K: Key>(&self, key: &K) -> Option<&V> {
        Tree::find(self.root.as_ref()?, key)
    }

    fn find<'a, K: Key>(cur_node: &'a Node<P, V>, key: &K) -> Option<&'a V> {
        let mut cur_node = cur_node;
        let mut depth = 0;
        loop {
            let key_prefix = key.partial_after(depth);
            let prefix = cur_node.prefix();
            let prefix_common_match = prefix.longest_common_prefix(key_prefix);
            if prefix_common_match != cur_node.prefix_len() {
                return None;
            }
            if cur_node.prefix_len() == key_prefix.len() {
                return cur_node.value();
            }

            let k = key.at(depth + cur_node.prefix_len());
            depth += cur_node.prefix_len();
            cur_node = cur_node.find_child(k)?;
        }
    }
}

/*
    Test cases for Adaptive Radix Tree
*/

#[cfg(test)]
mod tests {
    use crate::art::{ArrayPartial, InnerNode, LeafNode, Meta, Node, NodeType, Tree, NODE4MAX};
    use crate::{Key, VectorKey};
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
        let mut tree = Tree::<ArrayPartial<24>, i32>::new();
        let file_path = "testdata/words.txt";
        match read_words_from_file(file_path) {
            Ok(words) => {
                for word in words {
                    let key = VectorKey::from_str(word.as_str());
                    // assert!(tree.insert(&key, 1).is_none());
                    tree.insert(&key, 1);
                }
            }
            Err(err) => {
                eprintln!("Error reading file: {}", err);
            }
        }

        match read_words_from_file(file_path) {
            Ok(words) => {
                for word in words {
                    let key = VectorKey::from_str(word.as_str());
                    assert_eq!(*tree.get(&key).unwrap(), 1);
                }
            }
            Err(err) => {
                eprintln!("Error reading file: {}", err);
            }
        }

        match read_words_from_file(file_path) {
            Ok(words) => {
                for word in words {
                    let key = VectorKey::from_str(word.as_str());
                    assert_eq!(tree.remove(&key), true);
                }
            }
            Err(err) => {
                eprintln!("Error reading file: {}", err);
            }
        }
    }

    #[test]
    fn test_string_insert_delete() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        tree.insert(&VectorKey::from_str("a"), 1);
        tree.insert(&VectorKey::from_str("aa"), 1);
        tree.insert(&VectorKey::from_str("aal"), 1);
        tree.insert(&VectorKey::from_str("aalii"), 1);

        assert!(tree.remove(&VectorKey::from_str("a")));
        assert!(tree.remove(&VectorKey::from_str("aa")));
        assert!(tree.remove(&VectorKey::from_str("aal")));
        assert!(tree.remove(&VectorKey::from_str("aalii")));
    }

    #[test]
    fn test_string_long() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        tree.insert(&VectorKey::from_str("amyelencephalia"), 1);
        tree.insert(&VectorKey::from_str("amyelencephalic"), 2);
        tree.insert(&VectorKey::from_str("amyelencephalous"), 3);

        assert_eq!(
            *tree.get(&VectorKey::from_str("amyelencephalia")).unwrap(),
            1
        );
        assert_eq!(
            *tree.get(&VectorKey::from_str("amyelencephalic")).unwrap(),
            2
        );
        assert_eq!(
            *tree.get(&VectorKey::from_str("amyelencephalous")).unwrap(),
            3
        );
    }

    #[test]
    fn test_root_set_get() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        let key = VectorKey::from_str("abc");
        assert!(tree.insert(&key, 1).is_none());
        assert_eq!(*tree.get(&key).unwrap(), 1);
    }

    #[test]
    fn test_string_keys_get_set() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        tree.insert(&VectorKey::from_str("abcd"), 1);
        tree.insert(&VectorKey::from_str("abc"), 2);
        tree.insert(&VectorKey::from_str("abcde"), 3);
        tree.insert(&VectorKey::from_str("xyz"), 4);
        tree.insert(&VectorKey::from_str("xyz"), 5);
        tree.insert(&VectorKey::from_str("axyz"), 6);
        tree.insert(&VectorKey::from_str("1245zzz"), 6);

        assert_eq!(*tree.get(&VectorKey::from_str("abcd")).unwrap(), 1);
        assert_eq!(*tree.get(&VectorKey::from_str("abc")).unwrap(), 2);
        assert_eq!(*tree.get(&VectorKey::from_str("abcde")).unwrap(), 3);
        assert_eq!(*tree.get(&VectorKey::from_str("axyz")).unwrap(), 6);
        assert_eq!(*tree.get(&VectorKey::from_str("xyz")).unwrap(), 5);

        assert!(tree.remove(&VectorKey::from_str("abcde")));
        assert_eq!(tree.get(&VectorKey::from_str("abcde")), None);
        assert_eq!(*tree.get(&VectorKey::from_str("abc")).unwrap(), 2);
        assert_eq!(*tree.get(&VectorKey::from_str("axyz")).unwrap(), 6);
        assert!(tree.remove(&VectorKey::from_str("abc")));
        assert_eq!(tree.get(&VectorKey::from_str("abc")), None);
    }

    #[test]
    fn test_string_duplicate_insert() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        assert!(tree.insert(&VectorKey::from_str("abc"), 1).is_none());
        assert!(tree.insert(&VectorKey::from_str("abc"), 2).is_some());
    }

    #[test]
    fn test_string_keys_set_remove() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        tree.insert(&VectorKey::from_str("abc"), 2);
        tree.insert(&VectorKey::from_str("abcd"), 1);
        tree.insert(&VectorKey::from_str("abcde"), 3);
        tree.insert(&VectorKey::from_str("xyz"), 4);
        tree.insert(&VectorKey::from_str("axyz"), 6);
        tree.insert(&VectorKey::from_str("1245zzz"), 6);

        assert_eq!(tree.remove(&VectorKey::from_str("abc")), true);
        assert_eq!(tree.remove(&VectorKey::from_str("abcde")), true);
        assert_eq!(tree.remove(&VectorKey::from_str("abcd")), true);
        assert_eq!(tree.remove(&VectorKey::from_str("xyz")), true);
        assert_eq!(tree.remove(&VectorKey::from_str("axyz")), true);
        assert_eq!(tree.remove(&VectorKey::from_str("1245zzz")), true);
    }

    #[test]
    fn test_insert() {
        let DUMMY_VALUE: i32 = 1;
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        assert!(tree
            .insert(&VectorKey::from_str("hello"), DUMMY_VALUE)
            .is_none());
        assert!(tree
            .insert(&VectorKey::from_str("hi"), DUMMY_VALUE)
            .is_none());
        assert!(tree
            .insert(&VectorKey::from_str("bye"), DUMMY_VALUE)
            .is_none());
        assert!(tree
            .insert(&VectorKey::from_str("world"), DUMMY_VALUE)
            .is_none());
        assert!(tree
            .insert(&VectorKey::from_str("real"), DUMMY_VALUE)
            .is_none());
    }

    // #[test]
    // fn test_find_child_mut() {
    //     // Create a sample innerNode
    //     let mut inner_node = InnerNode::new_node48();
    //     let leaf = LeafNode::new(b"hello", 1);

    //     // Add a child node at index 42
    //     inner_node.add_child(42, Node::Leaf(Box::new(leaf)));

    //     // Test finding the child with key 42
    //     let found_child = inner_node.find_child_mut(42).unwrap();
    //     // Assert the type of the node
    //     match found_child {
    //         Node::Empty => panic!("Expected a non-empty node"),
    //         Node::Leaf(_) => {
    //             // The type of the node is Leaf
    //         }
    //         Node::Inner(_) => panic!("Expected a Leaf node"),
    //     }
    // }

    // #[test]
    // fn test_add_child() {
    //     let leaf = LeafNode::new(b"hello", 1);
    //     let leaf2 = LeafNode::new(b"hell", 1);
    //     let leaf3 = LeafNode::new(b"hello world", 1);

    //     let prefix_key = b"hello"[0];

    //     let mut inner = InnerNode::new_node4();
    //     inner.add_child(prefix_key, Node::Leaf(Box::new(leaf)));
    //     inner.add_child(prefix_key, Node::Leaf(Box::new(leaf2)));
    //     inner.add_child(prefix_key, Node::Leaf(Box::new(leaf3)));

    //     assert_eq!(inner.meta.num_children, 3);
    //     assert_eq!(inner.keys[0], prefix_key);
    //     assert_eq!(inner.keys[1], prefix_key);
    //     assert_eq!(inner.keys[2], prefix_key);
    // }

    // #[test]
    // fn test_grow() {
    //     let leaf = LeafNode::new(b"hello", 1);
    //     let leaf2 = LeafNode::new(b"hell", 1);
    //     let leaf3 = LeafNode::new(b"hello world", 1);
    //     let leaf4 = LeafNode::new(b"hella", 1);
    //     let leaf5 = LeafNode::new(b"hellb", 1);

    //     let prefix_key = b"hello"[0];

    //     let mut inner = InnerNode::new_node4();
    //     inner.add_child(prefix_key, Node::Leaf(Box::new(leaf)));
    //     inner.add_child(prefix_key, Node::Leaf(Box::new(leaf2)));
    //     inner.add_child(prefix_key, Node::Leaf(Box::new(leaf3)));
    //     inner.add_child(prefix_key, Node::Leaf(Box::new(leaf4)));
    //     inner.add_child(prefix_key, Node::Leaf(Box::new(leaf5)));

    //     assert_eq!(inner.node_type, NodeType::Node16);
    //     assert_eq!(inner.meta.num_children, 5);
    //     assert_eq!(inner.keys[0], prefix_key);
    //     assert_eq!(inner.keys[1], prefix_key);
    //     assert_eq!(inner.keys[2], prefix_key);
    //     assert_eq!(inner.keys[3], prefix_key);
    // }

    #[test]
    fn test_n4() {
        let test_key: ArrayPartial<16> = ArrayPartial::key("abc".as_bytes());
        let meta = Meta::new(test_key.clone(), 0);

        let mut n4 = InnerNode::new_node4(meta);
        let mut n4 = Node::Inner(Box::new(n4));

        n4.add_child(5, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), 1))));
        n4.add_child(4, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), 2))));
        n4.add_child(3, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), 3))));
        n4.add_child(2, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), 4))));

        assert_eq!(*n4.find_child(5).unwrap().value().unwrap(), 1);
        assert_eq!(*n4.find_child(4).unwrap().value().unwrap(), 2);
        assert_eq!(*n4.find_child(3).unwrap().value().unwrap(), 3);
        assert_eq!(*n4.find_child(2).unwrap().value().unwrap(), 4);

        n4.delete_child(5);
        assert!(n4.find_child(5).is_none());
        assert_eq!(*n4.find_child(4).unwrap().value().unwrap(), 2);
        assert_eq!(*n4.find_child(3).unwrap().value().unwrap(), 3);
        assert_eq!(*n4.find_child(2).unwrap().value().unwrap(), 4);

        n4.delete_child(2);
        assert!(n4.find_child(5).is_none());
        assert!(n4.find_child(2).is_none());

        n4.add_child(2, Node::Leaf(Box::new(LeafNode::new(test_key, 4))));
        n4.delete_child(3);
        assert!(n4.find_child(5).is_none());
        assert!(n4.find_child(3).is_none());
    }

    #[test]
    fn test_node16() {
        let test_key: ArrayPartial<16> = ArrayPartial::key("abc".as_bytes());
        let meta = Meta::new(test_key.clone(), 0);

        let mut n16 = InnerNode::new_node16(meta);
        let mut n16 = Node::Inner(Box::new(n16));

        // Fill up the node with keys in reverse order.
        for i in (0..16).rev() {
            n16.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), i))));
        }

        for i in 0..16 {
            assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
        }

        // Delete from end doesn't affect position of others.
        n16.delete_child(15);
        n16.delete_child(14);
        assert!(n16.find_child(15).is_none());
        assert!(n16.find_child(14).is_none());
        for i in 0..14 {
            assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
        }

        n16.delete_child(0);
        n16.delete_child(1);
        assert!(n16.find_child(0).is_none());
        assert!(n16.find_child(1).is_none());
        for i in 2..14 {
            assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
        }

        // Delete from the middle
        n16.delete_child(5);
        n16.delete_child(6);
        assert!(n16.find_child(5).is_none());
        assert!(n16.find_child(6).is_none());
        for i in 2..5 {
            assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
        }
        for i in 7..14 {
            assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
        }
    }

    #[test]
    fn test_node48() {
        let test_key: ArrayPartial<16> = ArrayPartial::key("abc".as_bytes());
        let meta = Meta::new(test_key.clone(), 0);

        let mut n48 = InnerNode::new_node48(meta);
        let mut n48 = Node::Inner(Box::new(n48));

        // indexes in n48 have no sort order, so we don't look at that
        for i in 0..48 {
            n48.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), i))));
        }

        for i in 0..48 {
            assert_eq!(*n48.find_child(i).unwrap().value().unwrap(), i);
        }

        n48.delete_child(47);
        n48.delete_child(46);
        assert!(n48.find_child(47).is_none());
        assert!(n48.find_child(46).is_none());
        for i in 0..46 {
            assert_eq!(*n48.find_child(i).unwrap().value().unwrap(), i);
        }
    }

    #[test]
    fn test_node256() {
        let test_key: ArrayPartial<16> = ArrayPartial::key("abc".as_bytes());
        let meta = Meta::new(test_key.clone(), 0);

        let mut n256 = InnerNode::new_node256(meta);
        let mut n256 = Node::Inner(Box::new(n256));

        for i in 0..=255 {
            n256.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), i))));
        }
        for i in 0..=255 {
            assert_eq!(*n256.find_child(i).unwrap().value().unwrap(), i);
        }

        n256.delete_child(47);
        n256.delete_child(46);
        assert!(n256.find_child(47).is_none());
        assert!(n256.find_child(46).is_none());
        for i in 0..46 {
            assert_eq!(*n256.find_child(i).unwrap().value().unwrap(), i);
        }
        for i in 48..=255 {
            assert_eq!(*n256.find_child(i).unwrap().value().unwrap(), i);
        }
    }

    // Inserting a single value into the tree and removing it should result in a nil tree root.
    #[test]
    fn test_insert_and_remove() {
        let key = &VectorKey::from_str("test");

        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        tree.insert(key, 1);

        assert_eq!(tree.remove(key), true);
        assert!(tree.get(key).is_none());
    }

    // Inserting Two values into the tree and removing one of them
    // should result in a tree root of type LEAF
    #[test]
    fn test_insert2_and_remove1_and_root_should_be_node4() {
        let key1 = &VectorKey::from_str("test1");
        let key2 = &VectorKey::from_str("test2");

        let mut tree = Tree::<ArrayPartial<16>, i32>::new();
        tree.insert(key1, 1);
        tree.insert(key2, 1);

        assert_eq!(tree.remove(key1), true);
        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert_eq!(root.node_type_name(), "Node4");
    }

    //     // Inserting Two values into a tree and deleting them both
    //     // should result in a nil tree root
    //     // This tests the expansion of the root into a NODE4 and
    //     // successfully collapsing into a LEAF and then nil upon successive removals
    //     #[test]
    //     fn test_insert2_and_remove2_and_root_should_be_nil() {
    //         let key1 = &VectorKey::from_str("test1");
    //         let key2 = &VectorKey::from_str("test2");

    //         let mut tree = Tree::<ArrayPartial<16>, i32>::new();
    //         tree.insert(key1, 1);
    //         tree.insert(key2, 1);

    //         assert_eq!(tree.remove(key1), true);
    //         assert_eq!(tree.remove(key2), true);

    //         assert!(tree.root.is_none());
    //     }

    // Inserting Five values into a tree and deleting one of them
    // should result in a tree root of type NODE4
    // This tests the expansion of the root into a NODE16 and
    // successfully collapsing into a NODE4 upon successive removals
    #[test]
    fn test_insert5_and_remove1_and_root_should_be_node4() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();

        for i in 0..5u32 {
            let key = &VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1);
        }

        assert_eq!(
            tree.remove(&VectorKey::from_slice(&1u32.to_be_bytes())),
            true
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
    //         let mut tree = Tree::<ArrayPartial<16>, i32>::new();

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
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();

        for i in 0..17u32 {
            let key = &VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1);
        }

        assert_eq!(
            tree.remove(&VectorKey::from_slice(&2u32.to_be_bytes())),
            true
        );

        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert!(root.is_inner());
        assert_eq!(root.node_type_name(), "Node16");
    }

    #[test]
    fn test_insert17_and_root_should_be_node48() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();

        for i in 0..17u32 {
            let key = VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1);
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
    //     let mut tree = Tree::<ArrayPartial<16>, i32>::new();

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
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();

        for i in 0..49u32 {
            let key = &VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1);
        }

        assert_eq!(
            tree.remove(&VectorKey::from_slice(&2u32.to_be_bytes())),
            true
        );

        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert!(root.is_inner());
        assert_eq!(root.node_type_name(), "Node48");
    }

    #[test]
    fn test_insert49_and_root_should_be_node248() {
        let mut tree = Tree::<ArrayPartial<16>, i32>::new();

        for i in 0..49u32 {
            let key = &VectorKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1);
        }

        assert!(tree.root.is_some());
        let root = tree.root.unwrap();
        assert!(root.is_inner());
        assert_eq!(root.node_type_name(), "Node256");
    }

    // // Inserting 49 values into a tree and removing all of them should
    // // result in a nil tree root
    // // This tests the expansion of the root into a NODE256, and
    // // successfully collapsing into a Node48, Node16, Node4, Leaf, and finally nil
    // #[test]
    // fn test_insert49_and_remove49_and_root_should_be_nil() {
    //     let mut tree = Tree::<ArrayPartial<16>, i32>::new();

    //     for i in 0..49u32 {
    //         let key = &VectorKey::from_slice(&i.to_be_bytes());
    //         tree.insert(key, 1);
    //     }

    //     for i in 0..49u32 {
    //         let key = VectorKey::from_slice(&i.to_be_bytes());
    //         // println!("removing key: {:?}", key);
    //         assert_eq!(tree.remove(&key), true);
    //     }

    //     assert!(tree.root.is_none());
    // }
}
