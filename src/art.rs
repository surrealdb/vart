use std::cmp::min;
use std::mem;

// Maximum length of a prefix
const MAX_PREFIX_LEN: usize = 10;

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
#[derive(Debug, Copy, Clone)]
struct Meta {
    prefix: [u8; MAX_PREFIX_LEN], // Prefix associated with the node
    prefix_len: usize,            // Length of the prefix
    num_children: usize,          // Number of children nodes
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
struct InnerNode<V> {
    meta: Meta,               // Metadata of the node
    node_type: NodeType,      // Type of the node
    keys: Box<[u8]>,          // Array of keys
    children: Box<[Node<V>]>, // Array of child nodes
}

// Leaf node of the adaptive radix trie
#[derive(Debug, Clone)]
struct LeafNode<V> {
    key: Box<[u8]>, // Key associated with the leaf node
    pub value: V,   // Value associated with the leaf node
}

// From the specification: Radix trees consist of two types of nodes:
// Inner nodes, which map partial keys to other nodes,
// and leaf nodes, which store the values corresponding to the keys.
#[derive(Debug, Clone, Default)]
enum Node<V> {
    #[default]
    Empty, // Empty node #[default] Empty
    Leaf(Box<LeafNode<V>>),   // Leaf node
    Inner(Box<InnerNode<V>>), // Inner node
}

// Adaptive radix trie
#[derive(Debug, Clone)]
pub struct Tree<V> {
    root: Option<Node<V>>, // Root node of the tree
    size: u64,             // Number of elements in the tree
}

// Default implementation for the Tree struct
impl<V> Default for Tree<V> {
    fn default() -> Self {
        Tree {
            root: None,
            size: 0,
        }
    }
}

// Implementation of methods for the Meta struct
impl Meta {
    // Check the length of the common prefix between the node's prefix and the given key
    fn check_prefix(&self, key: &[u8]) -> usize {
        let mut i = 0;
        while i < self.prefix_len && i < key.len() && self.prefix[i] == key[i] {
            i += 1;
        }
        i
    }

    // Create a new Meta instance with the given prefix, prefix length, and number of children
    fn new(prefix: &[u8], prefix_len: usize, num_children: usize) -> Self {
        let mut p = [0; MAX_PREFIX_LEN];
        p[..prefix_len].copy_from_slice(&prefix[..prefix_len]);
        Meta {
            prefix: p,
            prefix_len,
            num_children,
        }
    }
}

// Implementation of methods for the LeafNode struct
impl<V> LeafNode<V> {
    // Create a new LeafNode instance with the given key and value
    pub fn new(key: &[u8], value: V) -> Self {
        Self {
            key: key.into(),
            value,
        }
    }

    // Check if the leaf node matches the given key
    #[inline]
    pub fn matches(&self, key: &[u8]) -> bool {
        if self.key.len() != key.len() {
            return false;
        }
        self.key == key.into()
    }

    // Find the length of the longest common prefix between the leaf node and another leaf node, starting from a given depth
    #[inline]
    pub fn longest_common_prefix(&self, other: &[u8]) -> usize {
        let limit = min(self.key.len(), other.len());
        let limit = min(limit, MAX_PREFIX_LEN);
        for idx in 0..limit {
            if self.key[idx] != other[idx] {
                return idx;
            }
        }
        limit
    }
}

impl<V> InnerNode<V> {
    // From the specification: The smallest node type can store up to 4 child
    // pointers and uses an array of length 4 for keys and another
    // array of the same length for pointers. The keys and pointers
    // are stored at corresponding positions and the keys are sorted.
    #[inline] // TODO: check if this is required
    fn new_node4() -> InnerNode<V> {
        let children: [Node<V>; NODE4MAX] = [Node::<V>::INIT; NODE4MAX];
        let keys: [u8; NODE4MAX] = [0; NODE4MAX];

        Self {
            meta: Meta::new(&[0; MAX_PREFIX_LEN], 0, 0),
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
    fn new_node16() -> InnerNode<V> {
        let children: [Node<V>; NODE16MAX] = [Node::<V>::INIT; NODE16MAX];
        let keys: [u8; NODE16MAX] = [0; NODE16MAX];

        Self {
            meta: Meta::new(&[0; MAX_PREFIX_LEN], 0, 0),
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
    fn new_node48() -> InnerNode<V> {
        let children: [Node<V>; NODE48MAX] = [Node::<V>::INIT; NODE48MAX];
        let keys: [u8; NODE256MAX] = [0; NODE256MAX];

        Self {
            meta: Meta::new(&[0; MAX_PREFIX_LEN], 0, 0),
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
    fn new_node256() -> InnerNode<V> {
        let children: [Node<V>; NODE256MAX] = [Node::<V>::INIT; NODE256MAX];

        Self {
            meta: Meta::new(&[0; MAX_PREFIX_LEN], 0, 0),
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
    fn add_child(&mut self, key: u8, child: Node<V>) {
        if self.is_full() {
            self.grow();
        }

        let m = self.meta.num_children;

        match self.node_type {
            NodeType::Node4 => {
                let mut idx = 0;
                while idx < m {
                    if key < self.keys[idx] {
                        break;
                    }
                    idx += 1;
                }

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
                let m = self.meta.num_children;
                let mut idx = 0;
                while idx < m {
                    if !self.children[idx].is_empty() {
                        idx += 1;
                    }
                }
                self.children[idx] = child;
                self.keys[key as usize] = (idx + 1) as u8;
                self.meta.num_children += 1;
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
                let mut n16 = InnerNode::new_node16();
                for i in 0..self.meta.num_children {
                    n16.keys[i] = self.keys[i];
                    n16.children[i] = mem::replace(&mut self.children[i], Node::Empty);
                }
                *self = n16;
            }
            NodeType::Node16 => {
                let mut n48 = InnerNode::new_node48();
                for i in 0..self.meta.num_children {
                    n48.keys[i] = self.keys[i];
                    n48.children[i] = mem::replace(&mut self.children[i], Node::Empty);
                }
                *self = n48;
            }
            NodeType::Node48 => {
                let mut n256 = InnerNode::new_node256();
                for i in 0..self.meta.num_children {
                    n256.children[self.keys[i] as usize] =
                        mem::replace(&mut self.children[i], Node::Empty);
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
                let res = (0..self.meta.num_children).find(|&i| self.keys[i] == key);
                return res;
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
    fn find_child(&self, key: u8) -> Option<&Node<V>> {
        let idx = self.index(key)?;
        match self.node_type {
            NodeType::Node4 => Some(&self.children[idx]),
            NodeType::Node16 => Some(&self.children[idx]),
            NodeType::Node48 => Some(&self.children[idx]),
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
    fn find_child_mut(&mut self, key: u8) -> Option<&mut Node<V>> {
        let idx = self.index(key)?;
        match &mut self.node_type {
            NodeType::Node4 => {
                Some(&mut self.children[idx])
            }
            NodeType::Node16 => Some(&mut self.children[idx]),
            NodeType::Node48 => Some(&mut self.children[idx]),
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

    #[inline]
    pub fn longest_common_prefix(&self, other: &[u8]) -> usize {
        let limit = min(self.meta.prefix_len, other.len());
        let limit = min(limit, MAX_PREFIX_LEN);
        for idx in 0..limit {
            if self.meta.prefix[idx] != other[idx] {
                return idx;
            }
        }
        limit
    }
}

// Implementation of methods for the Node enum
impl<V> Node<V> {
    const INIT: Self = Node::Empty;

    // Check if the node is empty
    #[inline]
    fn is_empty(&self) -> bool {
        matches!(self, Node::Empty)
    }

    fn delete_child(&mut self, key: u8) {
        match self {
            Node::Inner(inner) => {
                match inner.node_type {
                    NodeType::Node4 | NodeType::Node16 => {
                        let Some(idx) = inner.index(key) else {
                            return
                        };
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
                        let Some(idx) = inner.index(key) else {
                            return
                        };
                        let child = &inner.children[idx];
                        if !child.is_empty() {
                            inner.children[idx] = Node::Empty;
                            inner.keys[key as usize] = 0;
                            inner.meta.num_children -= 1;
                        }
                    }
                    NodeType::Node256 => {
                        let Some(idx) = inner.index(key) else {
                            return
                        };
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

    fn inner_node(&mut self) -> Option<&mut InnerNode<V>> {
        match self {
            Node::Inner(inner) => Some(inner),
            _ => None,
        }
    }

    fn leaf_node(&mut self) -> Option<&mut LeafNode<V>> {
        match self {
            Node::Leaf(leaf) => Some(leaf),
            _ => None,
        }
    }

    // Shrinks the current ArtNode to the next smallest size.
    // ArtNodes of type NODE256 will grow to NODE48
    // ArtNodes of type NODE48 will grow to NODE16.
    // ArtNodes of type NODE16 will grow to NODE4.
    // ArtNodes of type NODE4 will collapse into its first child.
    // If that child is not a leaf, it will concatenate its current prefix with that of its childs
    // before replacing itself.
    fn shrink(&mut self) {
        match self {
            Node::Inner(inner) => match inner.node_type {
                NodeType::Node4 => {
                    let child = &mut inner.children[0];
                    if child.is_inner() {
                        let child_inner = child.inner_node().unwrap();
                        let mut current_prefix_len = inner.meta.prefix_len;

                        if current_prefix_len < MAX_PREFIX_LEN {
                            inner.meta.prefix[current_prefix_len] = inner.keys[0];
                            current_prefix_len += 1;
                        }

                        if current_prefix_len < MAX_PREFIX_LEN {
                            let child_prefix_len = min(
                                child_inner.meta.prefix_len,
                                MAX_PREFIX_LEN - current_prefix_len,
                            );
                            for i in 0..child_prefix_len {
                                inner.meta.prefix[current_prefix_len + i] =
                                    child_inner.meta.prefix[i];
                            }
                            current_prefix_len += child_prefix_len;
                        }

                        let copy_len = min(current_prefix_len, MAX_PREFIX_LEN);
                        for i in 0..min(copy_len, MAX_PREFIX_LEN) {
                            child_inner.meta.prefix[i] = inner.meta.prefix[i];
                        }
                        child_inner.meta.prefix_len += inner.meta.prefix_len + 1;

                        *self = mem::take(child);
                    }
                }
                NodeType::Node16 => {
                    let mut node4 = InnerNode::new_node4();
                    node4.meta.clone_from(&inner.meta);
                    node4.meta.num_children = 0;

                    for i in 0..inner.meta.num_children {
                        node4.keys[i] = inner.keys[i];
                        node4.children[i] = mem::take(&mut inner.children[i]);
                        node4.meta.num_children += 1;
                    }

                    *self = Node::Inner(Box::new(node4));
                }
                NodeType::Node48 => {
                    let mut node16 = InnerNode::new_node16();
                    node16.meta.clone_from(&inner.meta);
                    node16.meta.num_children = 0;

                    for i in 0..inner.meta.num_children {
                        let idx = inner.keys[i] as usize;
                        if idx > 0 {
                            let child = &inner.children[idx - 1];
                            if !child.is_empty() {
                                node16.children[node16.meta.num_children] =
                                    mem::take(&mut inner.children[idx - 1]);
                                node16.keys[node16.meta.num_children] = i as u8;
                                node16.meta.num_children += 1;
                            }
                        }
                    }

                    *self = Node::Inner(Box::new(node16));
                }
                NodeType::Node256 => {
                    let mut node48 = InnerNode::new_node48();
                    node48.meta.clone_from(&inner.meta);
                    node48.meta.num_children = 0;

                    for i in 0..inner.meta.num_children {
                        let child = &inner.children[i];
                        if !child.is_empty() {
                            node48.children[node48.meta.num_children] =
                                mem::take(&mut inner.children[i]);
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

    pub fn add_child(&mut self, key: u8, node: Node<V>) {
        match self {
            Node::Inner(inner) => {
                inner.add_child(key, node);
            }
            Node::Leaf(_) => unreachable!("Should not be possible."),
            Node::Empty => unreachable!("Should not be possible."),
        }
    }

    pub fn num_children(&self) -> usize {
        match self {
            Node::Inner(n) => n.children.len(),
            Node::Leaf(n) => 0,
            Node::Empty => unreachable!("Should not be possible."),
        }
    }

    fn prefix_clone(&self) -> Box<[u8]> {
        match self {
            Node::Inner(n) => n.meta.prefix.to_vec().into_boxed_slice(),
            Node::Leaf(n) => n.key.to_vec().into_boxed_slice(),
            Node::Empty => unreachable!("Should not be possible."),
        }
    }

    fn prefix(&self) -> &[u8] {
        match self {
            Node::Inner(n) => &n.meta.prefix[..n.meta.prefix.len()],
            Node::Leaf(n) => &n.key[..n.key.len()],
            Node::Empty => unreachable!("Should not be possible."),
        }
    }

    fn prefix_len(&self) -> usize {
        match self {
            Node::Inner(n) => n.meta.prefix_len,
            Node::Leaf(n) => n.key.len(),
            Node::Empty => unreachable!("Should not be possible."),
        }
    }

    fn longest_common_prefix(&self, other: &[u8]) -> usize {
        let limit = min(self.prefix_len(), other.len());
        let limit = min(limit, MAX_PREFIX_LEN);
        let prefix = self.prefix();
        for idx in 0..limit {
            if prefix[idx] != other[idx] {
                return idx;
            }
        }
        limit
    }

    fn set_prefix(&mut self, prefix: &[u8]) {
        match self {
            Node::Inner(n) => {
                let mut length = 0;
                for i in 0..prefix.len() {
                    if prefix[i] != 0 {
                        length += 1;
                    }
                    n.meta.prefix[i] = prefix[i];
                }
                n.meta.prefix_len = length;
            }
            Node::Leaf(n) => {
                n.key = prefix.to_vec().into_boxed_slice();
            }
            Node::Empty => unreachable!("Should not be possible."),
        }
    }

    pub fn value(&self) -> Option<&V> {
        let Node::Leaf(leaf) = &self else {
            return None;
        };
        Some(&leaf.value)
    }

    pub fn find_child(&self, key: u8) -> Option<&Node<V>> {
        if self.num_children() == 0 {
            return None;
        }

        match self {
            Node::Inner(inner) => inner.find_child(key),
            Node::Leaf(_) => None,
            Node::Empty => unreachable!("Should not be possible."),
        }
    }
}

fn partial_after(slice: &[u8], start_position: usize) -> &[u8] {
    assert!(start_position <= slice.len());
    &slice[start_position..slice.len()]
}

fn partial_before(slice: &[u8], length: usize) -> &[u8] {
    assert!(length <= slice.len());
    &slice[..length]
}

impl<V> Tree<V> {
    pub fn new() -> Self {
        Tree {
            root: None,
            size: 0,
        }
    }

    pub fn insert(&mut self, key: &[u8], value: V) -> Option<V> {
        if self.root.is_none() {
            self.root = Some(Node::Leaf(Box::new(LeafNode::new(key, value))));
            return None;
        };

        let root = self.root.as_mut().unwrap();
        return Tree::insert_recurse(root, key, value, 0);
    }

    fn insert_recurse(cur_node: &mut Node<V>, key: &[u8], value: V, depth: usize) -> Option<V> {
        let cur_node_prefix = cur_node.prefix_clone();
        let cur_node_prefix_len = cur_node.prefix_len();

        let key_prefix = partial_after(key, depth);
        let longest_common_prefix = cur_node.longest_common_prefix(key_prefix);

        let new_key = partial_after(cur_node_prefix.as_ref(), longest_common_prefix);
        let partial = partial_before(cur_node_prefix.as_ref(), longest_common_prefix);
        let partial_len = partial.len();
        let new_partial = copy_to_fixed_array(partial);

        let is_prefix_match = min(cur_node_prefix_len, key_prefix.len()) == longest_common_prefix;

        if let Node::Leaf(ref mut leaf) = cur_node {
            if is_prefix_match && leaf.key.len() == key_prefix.len() {
                return Some(mem::replace(&mut leaf.value, value));
            }
        }

        let k1 = cur_node_prefix[longest_common_prefix];
        let k2 = key_prefix[longest_common_prefix];

        if !is_prefix_match {
            cur_node.set_prefix(new_key);

            let mut n4: InnerNode<V> = InnerNode::new_node4();
            n4.meta.prefix_len = partial_len;
            n4.meta.prefix = new_partial;
            let n4_node: Node<V> = Node::Inner(Box::new(n4));

            let replacement_current = mem::replace(cur_node, n4_node);

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

    pub fn remove(&mut self, key: &[u8]) -> bool {
        if self.root.is_none() {
            return false;
        }
        return Tree::remove_recurse(&mut self.root.as_mut(), key, 0);
    }

    fn remove_recurse(
        cur_node_ptr: &mut Option<&mut Node<V>>,
        key: &[u8],
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
        let key_prefix = partial_after(key, depth);
        let longest_common_prefix = cur_node.longest_common_prefix(key_prefix);
        let is_prefix_match = min(prefix_len, key_prefix.len()) == longest_common_prefix;

        // if prefix.len() !=longest_common_prefix{
        //     return false;
        // }

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

    pub fn get(&self, key: &[u8]) -> Option<&V> {
        Tree::find(self.root.as_ref()?, key)
    }

    fn find<'a>(cur_node: &'a Node<V>, key: &[u8]) -> Option<&'a V> {
        let mut cur_node = cur_node;
        let mut depth = 0;
        loop {
            let key_prefix = partial_after(key, depth);
            let prefix_common_match = cur_node.longest_common_prefix(key_prefix);
            if prefix_common_match != cur_node.prefix_len() {
                return None;
            }

            if cur_node.prefix_len() == key_prefix.len() {
                return cur_node.value();
            }

            let k = key[depth + cur_node.prefix_len()];
            depth += cur_node.prefix_len();
            cur_node = cur_node.find_child(k)?;
        }
    }
}

// TODO: get rid for this
fn copy_to_fixed_array(source: &[u8]) -> [u8; 10] {
    let mut destination: [u8; 10] = [0; 10];
    let length = std::cmp::min(source.len(), destination.len());
    destination[..length].copy_from_slice(&source[..length]);
    destination
}

/*
    Test cases for Adaptive Radix Tree
*/

#[cfg(test)]
mod tests {
    use crate::art::{
        copy_to_fixed_array, InnerNode, LeafNode, Meta, Node, NodeType, 
        Tree, MAX_PREFIX_LEN,NODE4MAX,
    };

    fn add_zero_to_bytestring(bytestring: &[u8]) -> Vec<u8> {
        let mut new_bytestring = Vec::with_capacity(bytestring.len() + 1);
        new_bytestring.extend_from_slice(bytestring);
        new_bytestring.push(0);
        new_bytestring
    }

    #[test]
    fn test_root_set_get() {
        let mut tree = Tree::new();
        let key = add_zero_to_bytestring(b"abc");
        assert!(tree.insert(&key, 1).is_none());
        assert_eq!(*tree.get(&key).unwrap(), 1);
    }

    #[test]
    fn test_string_keys_get_set() {
        let mut q = Tree::new();
        q.insert(&add_zero_to_bytestring(b"abcd"), 1);
        q.insert(&add_zero_to_bytestring(b"abc"), 2);
        q.insert(&add_zero_to_bytestring(b"abcde"), 3);
        q.insert(&add_zero_to_bytestring(b"xyz"), 4);
        q.insert(&add_zero_to_bytestring(b"xyz"), 5);
        q.insert(&add_zero_to_bytestring(b"axyz"), 6);
        q.insert(&add_zero_to_bytestring(b"1245zzz"), 6);

        assert_eq!(*q.get(&add_zero_to_bytestring(b"abcd")).unwrap(), 1);
        assert_eq!(*q.get(&add_zero_to_bytestring(b"abc")).unwrap(), 2);
        assert_eq!(*q.get(&add_zero_to_bytestring(b"abcde")).unwrap(), 3);
        assert_eq!(*q.get(&add_zero_to_bytestring(b"axyz")).unwrap(), 6);
        assert_eq!(*q.get(&add_zero_to_bytestring(b"xyz")).unwrap(), 5);

        assert!(q.remove(&add_zero_to_bytestring(b"abcde")));
        assert_eq!(q.get(&add_zero_to_bytestring(b"abcde")), None);
        assert_eq!(*q.get(&add_zero_to_bytestring(b"abc")).unwrap(), 2);
        assert_eq!(*q.get(&add_zero_to_bytestring(b"axyz")).unwrap(), 6);
        assert!(q.remove(&add_zero_to_bytestring(b"abc")));
        assert_eq!(q.get(&add_zero_to_bytestring(b"abc")), None);
    }

    #[test]
    fn test_string_duplicate_insert() {
        let mut tree = Tree::new();
        assert!(tree.insert(&add_zero_to_bytestring(b"abc"), 1).is_none());
        assert!(tree.insert(&add_zero_to_bytestring(b"abc"), 2).is_some());
    }

    #[test]
    fn test_string_keys_set_remove() {
        let mut tree = Tree::new();
        tree.insert(&add_zero_to_bytestring(b"abc"), 2);
        tree.insert(&add_zero_to_bytestring(b"abcd"), 1);
        tree.insert(&add_zero_to_bytestring(b"abcde"), 3);
        tree.insert(&add_zero_to_bytestring(b"xyz"), 4);
        tree.insert(&add_zero_to_bytestring(b"axyz"), 6);
        tree.insert(&add_zero_to_bytestring(b"1245zzz"), 6);

        assert_eq!(tree.remove(&add_zero_to_bytestring(b"abc")), true);
        assert_eq!(tree.remove(&add_zero_to_bytestring(b"abcde")), true);
        assert_eq!(tree.remove(&add_zero_to_bytestring(b"abcd")), true);
        assert_eq!(tree.remove(&add_zero_to_bytestring(b"xyz")), true);
        assert_eq!(tree.remove(&add_zero_to_bytestring(b"axyz")), true);
        assert_eq!(tree.remove(&add_zero_to_bytestring(b"1245zzz")), true);
    }

    #[test]
    fn test_find_child_mut() {
        let mut inner_node = InnerNode::new_node48();
        let leaf = LeafNode::new(b"hello", 1);

        // Add a child node at index 42
        inner_node.add_child(42, Node::Leaf(Box::new(leaf)));

        // Test finding the child with key 42
        let found_child = inner_node.find_child_mut(42).unwrap();
        // Assert the type of the node
        match found_child {
            Node::Empty => panic!("Expected a non-empty node"),
            Node::Leaf(_) => {
                // The type of the node is Leaf
            }
            Node::Inner(_) => panic!("Expected a Leaf node"),
        }
    }

    #[test]
    fn test_add_child() {
        let leaf = LeafNode::new(b"hello", 1);
        let leaf2 = LeafNode::new(b"hell", 1);
        let leaf3 = LeafNode::new(b"hello world", 1);

        let prefix_key = b"hello"[0];

        let mut inner = InnerNode::new_node4();
        inner.add_child(prefix_key, Node::Leaf(Box::new(leaf)));
        inner.add_child(prefix_key, Node::Leaf(Box::new(leaf2)));
        inner.add_child(prefix_key, Node::Leaf(Box::new(leaf3)));

        assert_eq!(inner.meta.num_children, 3);
        assert_eq!(inner.keys[0], prefix_key);
        assert_eq!(inner.keys[1], prefix_key);
        assert_eq!(inner.keys[2], prefix_key);
    }

    #[test]
    fn test_grow() {
        let leaf = LeafNode::new(b"hello", 1);
        let leaf2 = LeafNode::new(b"hell", 1);
        let leaf3 = LeafNode::new(b"hello world", 1);
        let leaf4 = LeafNode::new(b"hella", 1);
        let leaf5 = LeafNode::new(b"hellb", 1);

        let prefix_key = b"hello"[0];

        let mut inner = InnerNode::new_node4();
        inner.add_child(prefix_key, Node::Leaf(Box::new(leaf)));
        inner.add_child(prefix_key, Node::Leaf(Box::new(leaf2)));
        inner.add_child(prefix_key, Node::Leaf(Box::new(leaf3)));
        inner.add_child(prefix_key, Node::Leaf(Box::new(leaf4)));
        inner.add_child(prefix_key, Node::Leaf(Box::new(leaf5)));

        assert_eq!(inner.node_type, NodeType::Node16);
        assert_eq!(inner.meta.num_children, 1);
        assert_eq!(inner.keys[0], prefix_key);
        assert_eq!(inner.keys[1], prefix_key);
        assert_eq!(inner.keys[2], prefix_key);
        assert_eq!(inner.keys[3], prefix_key);
    }

    #[test]
    fn test_matches() {
        let leaf = LeafNode::new(b"hello", 1);
        assert_eq!(leaf.matches(b"hello"), true);
        assert_eq!(leaf.matches(b"hello world"), false);
        assert_eq!(leaf.matches(b"hell"), false);
        assert_eq!(leaf.matches(b"hell"), false);
    }

    #[test]
    fn test_check_prefix() {
        let mut meta = Meta {
            prefix: [0; MAX_PREFIX_LEN],
            prefix_len: 0,
            num_children: NODE4MAX,
        };
        let key = b"hello";
        let prefix_len = meta.check_prefix(key);
        assert_eq!(prefix_len, 0);

        meta.prefix[0] = b'h';
        meta.prefix[1] = b'e';
        meta.prefix[2] = b'l';
        meta.prefix[3] = b'l';
        meta.prefix[4] = b'o';
        meta.prefix_len = 5;
        let prefix_len = meta.check_prefix(key);
        assert_eq!(prefix_len, 5);

        let key = b"hell";
        let prefix_len = meta.check_prefix(key);
        assert_eq!(prefix_len, 4);

        let key = b"hello world";
        let prefix_len = meta.check_prefix(key);
        assert_eq!(prefix_len, 5);
    }

    #[test]
    fn test_n4() {
        let test_key = &add_zero_to_bytestring(b"abc");

        let mut n4 = InnerNode::new_node4();
        n4.meta.prefix = copy_to_fixed_array(test_key);
        n4.meta.prefix_len = test_key.len();
        let mut n4 = Node::Inner(Box::new(n4));

        n4.add_child(5, Node::Leaf(Box::new(LeafNode::new(test_key, 1))));
        n4.add_child(4, Node::Leaf(Box::new(LeafNode::new(test_key, 2))));
        n4.add_child(3, Node::Leaf(Box::new(LeafNode::new(test_key, 3))));
        n4.add_child(2, Node::Leaf(Box::new(LeafNode::new(test_key, 4))));

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
    fn test_n16() {
        let test_key = &add_zero_to_bytestring(b"abc");

        let mut n16 = InnerNode::new_node16();
        n16.meta.prefix = copy_to_fixed_array(test_key);
        n16.meta.prefix_len = test_key.len();
        let mut n16 = Node::Inner(Box::new(n16));

        // Fill up the node with keys in reverse order.
        for i in (0..16).rev() {
            n16.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key, i))));
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
    fn test_n48() {
        let test_key = &add_zero_to_bytestring(b"abc");

        let mut n48 = InnerNode::new_node48();
        n48.meta.prefix = copy_to_fixed_array(test_key);
        n48.meta.prefix_len = test_key.len();
        let mut n48 = Node::Inner(Box::new(n48));

        // indexes in n48 have no sort order, so we don't look at that
        for i in 0..48 {
            n48.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key, i))));
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
    fn test_n_256() {
        let test_key = &add_zero_to_bytestring(b"abc");

        let mut n256 = InnerNode::new_node256();
        n256.meta.prefix = copy_to_fixed_array(test_key);
        n256.meta.prefix_len = test_key.len();
        let mut n256 = Node::Inner(Box::new(n256));

        for i in 0..=255 {
            n256.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key, i))));
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
}
