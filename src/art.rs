use core::panic;
use std::cmp::min;
use std::mem;

use crate::node::{FlatNode, LeafNode, Node256, Node48, NodeTrait};
use crate::{ArrayPrefix, Key, Prefix, PrefixTrait};

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

// From the specification: Adaptive Radix tries consist of two types of nodes:
// Inner nodes, which map prefix(prefix) keys to other nodes,
// and leaf nodes, which store the values corresponding to the key.
struct Node<P: Prefix + Clone, V> {
    pub node_type: NodeType<P, V>, // Type of the node
}

enum NodeType<P: Prefix + Clone, V> {
    // Leaf node of the adaptive radix trie
    Leaf(LeafNode<P, V>),
    // Inner node of the adaptive radix trie
    Node4(FlatNode<P, Node<P, V>, 4>), // Node with 4 keys and 4 children
    Node16(FlatNode<P, Node<P, V>, 16>), // Node with 16 keys and 16 children
    Node48(Node48<P, Node<P, V>, 48>), // Node with 256 keys and 48 children
    Node256(Node256<P, Node<P, V>>),   // Node with 256 keys and 256 children
}

// Adaptive radix trie
pub struct Tree<P: PrefixTrait, V> {
    root: Option<Node<P, V>>, // Root node of the tree
    size: u64,                // Number of elements in the tree
}

// Default implementation for the Tree struct
impl<P: PrefixTrait, V> Default for Tree<P, V> {
    fn default() -> Self {
        Tree {
            root: None,
            size: 0,
        }
    }
}

impl<P: PrefixTrait + Clone, V> Node<P, V> {
    #[inline]
    pub(crate) fn new_leaf(key: P, value: V) -> Node<P, V> {
        Self {
            node_type: NodeType::Leaf(LeafNode {
                key: key,
                value: value,
                ts: 0,
            }),
        }
    }

    // From the specification: The smallest node type can store up to 4 child
    // pointers and uses an array of length 4 for keys and another
    // array of the same length for pointers. The keys and pointers
    // are stored at corresponding positions and the keys are sorted.
    #[inline]
    #[allow(dead_code)]
    pub fn new_node4(prefix: P) -> Self {
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
    pub fn new_node16(prefix: P) -> Self {
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
    pub fn new_node48(prefix: P) -> Self {
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
    pub fn new_node256(prefix: P) -> Self {
        let nt = NodeType::Node256(Node256::new(prefix));
        Self { node_type: nt }
    }

    #[inline]
    fn is_full(&self) -> bool {
        match &self.node_type {
            NodeType::Node4(km) => self.num_children() >= km.size(),
            NodeType::Node16(km) => self.num_children() >= km.size(),
            NodeType::Node48(im) => self.num_children() >= im.size(),
            NodeType::Node256(_) => self.num_children() >= 256,
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    #[inline]
    fn add_child(&mut self, key: u8, child: Node<P, V>) {
        if self.is_full() {
            self.grow();
        }

        match &mut self.node_type {
            NodeType::Node4(n) => {
                n.add_child(key, child);
            }
            NodeType::Node16(n) => {
                n.add_child(key, child);
            }
            NodeType::Node48(n) => {
                n.add_child(key, child);
            }
            NodeType::Node256(n) => {
                n.add_child(key, child);
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
                let n256 = n.grow();
                self.node_type = NodeType::Node256(n256)
            }
            NodeType::Node256 { .. } => {
                panic!("should not grow a node 256")
            }
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    #[inline]
    fn find_child(&self, key: u8) -> Option<&Node<P, V>> {
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

    #[inline]
    fn find_child_mut(&mut self, key: u8) -> Option<&mut Node<P, V>> {
        if self.num_children() == 0 {
            return None;
        }

        match &mut self.node_type {
            NodeType::Node4(n) => n.find_child_mut(key),
            NodeType::Node16(n) => n.find_child_mut(key),
            NodeType::Node48(n) => n.find_child_mut(key),
            NodeType::Node256(n) => n.find_child_mut(key),
            NodeType::Leaf(_) => None,
        }
    }

    fn delete_child(&mut self, key: u8) -> Option<Node<P, V>> {
        match &mut self.node_type {
            NodeType::Node4(n) => {
                let node = n.delete_child(key);
                if self.num_children() < NODE4MIN {
                    self.shrink();
                }

                node
            }
            NodeType::Node16(n) => {
                let node = n.delete_child(key);
                if self.num_children() < NODE16MIN {
                    self.shrink();
                }

                node
            }
            NodeType::Node48(n) => {
                let node = n.delete_child(key);
                if self.num_children() < NODE48MIN {
                    self.shrink();
                }

                node
            }
            NodeType::Node256(n) => {
                let node = n.delete_child(key);
                if self.num_children() < NODE256MIN {
                    self.shrink();
                }

                node
            }
            NodeType::Leaf(_) => panic!("should not be reached"),
        }
    }

    #[inline]
    fn is_leaf(&self) -> bool {
        matches!(&self.node_type, NodeType::Leaf(_))
    }

    #[inline]
    fn is_inner(&self) -> bool {
        !self.is_leaf()
    }

    #[inline]
    fn prefix(&self) -> &P {
        match &self.node_type {
            NodeType::Node4(n) => &n.prefix,
            NodeType::Node16(n) => &n.prefix,
            NodeType::Node48(n) => &n.prefix,
            NodeType::Node256(n) => &n.prefix,
            NodeType::Leaf(n) => &n.key,
        }
    }

    #[inline]
    fn set_prefix(&mut self, prefix: P) {
        match &mut self.node_type {
            NodeType::Node4(n) => n.prefix = prefix,
            NodeType::Node16(n) => n.prefix = prefix,
            NodeType::Node48(n) => n.prefix = prefix,
            NodeType::Node256(n) => n.prefix = prefix,
            NodeType::Leaf(n) => n.key = prefix,
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
    pub fn get_value(&self) -> Option<&V> {
        let NodeType::Leaf(leaf) = &self.node_type else {
            return None;
        };
        Some(&leaf.value)
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
}

impl<P: PrefixTrait, V> Tree<P, V> {
    pub fn new() -> Self {
        Tree {
            root: None,
            size: 0,
        }
    }

    pub fn insert<K: Key>(&mut self, key: &K, value: V) -> Option<V> {
        if self.root.is_none() {
            self.root = Some(Node::new_leaf(key.as_slice().into(), value));
            return None;
        };

        let mut stack = vec![(self.root.as_mut().unwrap(), key, value, 0)];

        while let Some((cur_node, key, value, depth)) = stack.pop() {
            let cur_node_prefix = cur_node.prefix().clone();
            let cur_node_prefix_len = cur_node.prefix().length();

            let key_prefix = key.prefix_after(depth);
            let longest_common_prefix = cur_node_prefix.longest_common_prefix(key_prefix);

            let new_key = cur_node_prefix.prefix_after(longest_common_prefix);
            let prefix = cur_node_prefix.prefix_before(longest_common_prefix);
            let is_prefix_match =
                min(cur_node_prefix_len, key_prefix.len()) == longest_common_prefix;

            if let NodeType::Leaf(ref mut leaf) = &mut cur_node.node_type {
                if is_prefix_match && cur_node_prefix.length() == key_prefix.len() {
                    return Some(std::mem::replace(&mut leaf.value, value));
                }
            }

            if !is_prefix_match {
                cur_node.set_prefix(new_key);
                let n4 = Node::new_node4(prefix);
                let old_node = std::mem::replace(cur_node, n4);

                let k1 = cur_node_prefix.at(longest_common_prefix);
                let k2 = key_prefix[longest_common_prefix];
                let new_leaf = Node::new_leaf(
                    key_prefix[longest_common_prefix..key_prefix.len()].into(),
                    value,
                );

                cur_node.add_child(k1, old_node);
                cur_node.add_child(k2, new_leaf);

                return None;
            }

            let k = key_prefix[longest_common_prefix];
            if cur_node.find_child(k).is_some() {
                let child = cur_node.find_child_mut(k).unwrap();
                stack.push((child, key, value, depth + longest_common_prefix));
            } else {
                let new_leaf = Node::new_leaf(
                    key_prefix[longest_common_prefix..key_prefix.len()].into(),
                    value,
                );

                cur_node.add_child(k, new_leaf);

                return None;
            }
        }
        None
    }

    pub fn remove<K: Key>(&mut self, key: &K) -> bool {
        if self.root.is_none() {
            return false;
        }

        let root = self.root.as_mut().unwrap();
        if root.is_leaf() {
            self.root = None;
            return true;
        }

        let mut stack = vec![(self.root.as_mut().unwrap(), key, 0)];

        while let Some((cur_node, key, depth)) = stack.pop() {
            let prefix = cur_node.prefix().clone();

            let key_prefix = key.prefix_after(depth);
            let longest_common_prefix = prefix.longest_common_prefix(key_prefix);
            let is_prefix_match = min(prefix.length(), key_prefix.len()) == longest_common_prefix;

            if is_prefix_match && prefix.length() == key_prefix.len() {
                return true;
            }

            let k = key_prefix[longest_common_prefix];
            if let Some(child) = cur_node.find_child(k) {
                if child.num_children() == 0 {
                    if child.prefix().length() == key_prefix.len() - longest_common_prefix {
                        cur_node.delete_child(k).expect("child not found");
                        return true;
                    }
                    return false;
                }
                let child = cur_node.find_child_mut(k).unwrap();
                stack.push((child, key, depth + longest_common_prefix));
            }
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
}

/*
    Test cases for Adaptive Radix Tree
*/

#[cfg(test)]
mod tests {
    use crate::art::{ArrayPrefix, Tree};
    use crate::VectorKey;
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
        let mut tree: Tree<ArrayPrefix<24>, i32> = Tree::<ArrayPrefix<24>, i32>::new();
        let file_path = "testdata/words.txt";
        match read_words_from_file(file_path) {
            Ok(words) => {
                for word in words {
                    let key = &VectorKey::from_str(&word);

                    tree.insert(&VectorKey::from_str(&word), 1);
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
                    let key = VectorKey::from_str(&word);
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
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
        tree.insert(&VectorKey::from_str("a"), 1);
        tree.insert(&VectorKey::from_str("aa"), 1);
        tree.insert(&VectorKey::from_str("aal"), 1);
        tree.insert(&VectorKey::from_str("aalii"), 1);

        assert!(tree.remove(&VectorKey::from_str("a")));
        assert!(tree.remove(&VectorKey::from_str("aa")));
        assert!(tree.remove(&VectorKey::from_str("aal")));
        assert!(tree.remove(&VectorKey::from_str("aalii")));

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
    fn test_string_long() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
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
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
        let key = VectorKey::from_str("abc");
        assert!(tree.insert(&key, 1).is_none());
        assert_eq!(*tree.get(&key).unwrap(), 1);
    }

    #[test]
    fn test_string_duplicate_insert() {
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
        assert!(tree.insert(&VectorKey::from_str("abc"), 1).is_none());
        assert!(tree.insert(&VectorKey::from_str("abc"), 2).is_some());
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

    // #[test]
    // fn test_n4() {
    //     let test_key: ArrayPrefix<16> = ArrayPrefix::key("abc".as_bytes());
    //     let meta = Meta::new(test_key.clone(), 0);

    //     let mut n4 = InnerNode::new_node4(meta);
    //     let mut n4 = Node::Inner(Box::new(n4));

    //     n4.add_child(5, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), 1))));
    //     n4.add_child(4, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), 2))));
    //     n4.add_child(3, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), 3))));
    //     n4.add_child(2, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), 4))));

    //     assert_eq!(*n4.find_child(5).unwrap().value().unwrap(), 1);
    //     assert_eq!(*n4.find_child(4).unwrap().value().unwrap(), 2);
    //     assert_eq!(*n4.find_child(3).unwrap().value().unwrap(), 3);
    //     assert_eq!(*n4.find_child(2).unwrap().value().unwrap(), 4);

    //     n4.delete_child(5);
    //     assert!(n4.find_child(5).is_none());
    //     assert_eq!(*n4.find_child(4).unwrap().value().unwrap(), 2);
    //     assert_eq!(*n4.find_child(3).unwrap().value().unwrap(), 3);
    //     assert_eq!(*n4.find_child(2).unwrap().value().unwrap(), 4);

    //     n4.delete_child(2);
    //     assert!(n4.find_child(5).is_none());
    //     assert!(n4.find_child(2).is_none());

    //     n4.add_child(2, Node::Leaf(Box::new(LeafNode::new(test_key, 4))));
    //     n4.delete_child(3);
    //     assert!(n4.find_child(5).is_none());
    //     assert!(n4.find_child(3).is_none());
    // }

    // #[test]
    // fn test_node16() {
    //     let test_key: ArrayPrefix<16> = ArrayPrefix::key("abc".as_bytes());
    //     let meta = Meta::new(test_key.clone(), 0);

    //     let mut n16 = InnerNode::new_node16(meta);
    //     let mut n16 = Node::Inner(Box::new(n16));

    //     // Fill up the node with keys in reverse order.
    //     for i in (0..16).rev() {
    //         n16.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), i))));
    //     }

    //     for i in 0..16 {
    //         assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
    //     }

    //     // Delete from end doesn't affect position of others.
    //     n16.delete_child(15);
    //     n16.delete_child(14);
    //     assert!(n16.find_child(15).is_none());
    //     assert!(n16.find_child(14).is_none());
    //     for i in 0..14 {
    //         assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
    //     }

    //     n16.delete_child(0);
    //     n16.delete_child(1);
    //     assert!(n16.find_child(0).is_none());
    //     assert!(n16.find_child(1).is_none());
    //     for i in 2..14 {
    //         assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
    //     }

    //     // Delete from the middle
    //     n16.delete_child(5);
    //     n16.delete_child(6);
    //     assert!(n16.find_child(5).is_none());
    //     assert!(n16.find_child(6).is_none());
    //     for i in 2..5 {
    //         assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
    //     }
    //     for i in 7..14 {
    //         assert_eq!(*n16.find_child(i).unwrap().value().unwrap(), i);
    //     }
    // }

    // #[test]
    // fn test_node48() {
    //     let test_key: ArrayPrefix<16> = ArrayPrefix::key("abc".as_bytes());
    //     let meta = Meta::new(test_key.clone(), 0);

    //     let mut n48 = InnerNode::new_node48(meta);
    //     let mut n48 = Node::Inner(Box::new(n48));

    //     // indexes in n48 have no sort order, so we don't look at that
    //     for i in 0..48 {
    //         n48.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), i))));
    //     }

    //     for i in 0..48 {
    //         assert_eq!(*n48.find_child(i).unwrap().value().unwrap(), i);
    //     }

    //     n48.delete_child(47);
    //     n48.delete_child(46);
    //     assert!(n48.find_child(47).is_none());
    //     assert!(n48.find_child(46).is_none());
    //     for i in 0..46 {
    //         assert_eq!(*n48.find_child(i).unwrap().value().unwrap(), i);
    //     }
    // }

    // #[test]
    // fn test_node256() {
    //     let test_key: ArrayPrefix<16> = ArrayPrefix::key("abc".as_bytes());
    //     let meta = Meta::new(test_key.clone(), 0);

    //     let mut n256 = InnerNode::new_node256(meta);
    //     let mut n256 = Node::Inner(Box::new(n256));

    //     for i in 0..=255 {
    //         n256.add_child(i, Node::Leaf(Box::new(LeafNode::new(test_key.clone(), i))));
    //     }
    //     for i in 0..=255 {
    //         assert_eq!(*n256.find_child(i).unwrap().value().unwrap(), i);
    //     }

    //     n256.delete_child(47);
    //     n256.delete_child(46);
    //     assert!(n256.find_child(47).is_none());
    //     assert!(n256.find_child(46).is_none());
    //     for i in 0..46 {
    //         assert_eq!(*n256.find_child(i).unwrap().value().unwrap(), i);
    //     }
    //     for i in 48..=255 {
    //         assert_eq!(*n256.find_child(i).unwrap().value().unwrap(), i);
    //     }
    // }

    // Inserting a single value into the tree and removing it should result in a nil tree root.
    #[test]
    fn test_insert_and_remove() {
        let key = &VectorKey::from_str("test");

        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
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

        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
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

    //         let mut tree = Tree::<ArrayPrefix<16>, i32>::new();
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
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

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
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

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
        let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

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
    //     let mut tree = Tree::<ArrayPrefix<16>, i32>::new();

    //     for i in 0..49u32 {
    //         let key = &VectorKey::from_slice(&i.to_be_bytes());
    //         tree.insert(key, 1);
    //     }

    //     for i in 0..49u32 {
    //         let key = VectorKey::from_slice(&i.to_be_bytes());
    //         assert_eq!(tree.remove(&key), true);
    //     }

    //     assert!(tree.root.is_none());
    // }
}
