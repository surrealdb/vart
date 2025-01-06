use core::panic;
use std::cmp::min;
use std::cmp::Ordering;
use std::ops::RangeBounds;
use std::sync::Arc;

use crate::iter::{query_keys_at_node, scan_node, Iter, Range};
use crate::node::{FlatNode, LeafValue, Node256, Node48, NodeTrait, TwigNode};
use crate::{KeyTrait, TrieError};

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

/// A struct representing a node in an Adaptive Radix Trie.
///
/// The `Node` struct encapsulates a single node within the adaptive radix trie structure.
/// It holds information about the type of the node, which can be one of the various node types
/// defined by the `NodeType` enum.
///
/// # Type Parameters
///
/// - `P`: A type implementing the `Prefix` trait, defining the key prefix for the node.
/// - `V`: The type of value associated with the node.
///
/// # Fields
///
/// - `node_type`: The `NodeType` variant representing the type of the node, containing its
///                specific structure and associated data.
///
pub(crate) struct Node<P: KeyTrait, V: Clone> {
    pub(crate) node_type: NodeType<P, V>, // Type of the node
}

#[derive(Copy, Clone)]
// An enum for the different types of queries on the TwigNode
pub enum QueryType {
    LatestByVersion(u64),
    LatestByTs(u64),
    LastLessThanTs(u64),
    LastLessOrEqualTs(u64),
    FirstGreaterThanTs(u64),
    FirstGreaterOrEqualTs(u64),
}

/// An enumeration representing different types of nodes in an Adaptive Radix Trie.
///
/// The `NodeType` enum encompasses various node types that can exist within the adaptive radix trie structure.
/// It includes different types of inner nodes, such as `Node4`, `Node16`, `Node48`, and `Node256`, as well as the
/// leaf nodes represented by `TwigNode`.
///
/// # Type Parameters
///
/// - `P`: A type implementing the `Prefix` trait, which is used to define the key prefix for each node.
/// - `V`: The type of value associated with each node.
///
/// # Variants
///
/// - `Twig(TwigNode<P, V>)`: Represents a Twig node, which is a leaf node in the adaptive radix trie.
/// - `Node4(FlatNode<P, Node<P, V>, 4>)`: Represents an inner node with 4 keys and 4 children.
/// - `Node16(FlatNode<P, Node<P, V>, 16>)`: Represents an inner node with 16 keys and 16 children.
/// - `Node48(Node48<P, Node<P, V>>)`: Represents an inner node with 256 keys and 48 children.
/// - `Node256(Node256<P, Node<P, V>>)`: Represents an inner node with 256 keys and 256 children.
///
pub(crate) enum NodeType<P: KeyTrait, V: Clone> {
    // Twig node of the adaptive radix trie
    Twig(TwigNode<P, V>),
    // Inner node of the adaptive radix trie
    Node4(FlatNode<P, Node<P, V>, 4>), // Node with 4 keys and 4 children
    Node16(FlatNode<P, Node<P, V>, 16>), // Node with 16 keys and 16 children
    Node48(Node48<P, Node<P, V>>),     // Node with 256 keys and 48 children
    Node256(Node256<P, Node<P, V>>),   // Node with 256 keys and 256 children
}

impl<P: KeyTrait, V: Clone> NodeType<P, V> {
    pub(crate) fn set_prefix(&mut self, prefix: P) {
        match self {
            NodeType::Node4(n) => n.prefix = prefix,
            NodeType::Node16(n) => n.prefix = prefix,
            NodeType::Node48(n) => n.prefix = prefix,
            NodeType::Node256(n) => n.prefix = prefix,
            NodeType::Twig(n) => n.prefix = prefix,
        }
    }

    fn get_inner_twig(&self) -> Option<&Node<P, V>> {
        match self {
            NodeType::Node4(n) => n.inner_twig.as_deref(),
            NodeType::Node16(n) => n.inner_twig.as_deref(),
            NodeType::Node48(n) => n.inner_twig.as_deref(),
            NodeType::Node256(n) => n.inner_twig.as_deref(),
            NodeType::Twig(_) => None,
        }
    }

    fn get_inner_twig_mut(&mut self) -> Option<&mut Node<P, V>> {
        match self {
            NodeType::Node4(n) => Arc::get_mut(n.inner_twig.as_mut()?),
            NodeType::Node16(n) => Arc::get_mut(n.inner_twig.as_mut()?),
            NodeType::Node48(n) => Arc::get_mut(n.inner_twig.as_mut()?),
            NodeType::Node256(n) => Arc::get_mut(n.inner_twig.as_mut()?),
            NodeType::Twig(_) => None,
        }
    }

    fn clone_inner_twig(&self) -> Option<Arc<Node<P, V>>> {
        match self {
            NodeType::Node4(n) => n.inner_twig.clone(),
            NodeType::Node16(n) => n.inner_twig.clone(),
            NodeType::Node48(n) => n.inner_twig.clone(),
            NodeType::Node256(n) => n.inner_twig.clone(),
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in clone_inner_twig()"),
        }
    }
}

impl<P: KeyTrait, V: Clone> Node<P, V> {
    /// Creates a new Twig node with a given prefix, key, value, and version.
    ///
    /// Constructs a new Twig node using the provided prefix, key, and value. The version
    /// indicates the time of the insertion.
    ///
    /// # Parameters
    ///
    /// - `prefix`: The common prefix for the node.
    /// - `key`: The key associated with the Twig node.
    /// - `value`: The value to be associated with the key.
    /// - `ts`: The version when the value was inserted.
    ///
    /// # Returns
    ///
    /// Returns a new `Node` instance with a Twig node containing the provided key, value, and version.
    ///
    #[inline]
    pub(crate) fn new_twig(prefix: P, key: P, value: V, version: u64, ts: u64) -> Node<P, V> {
        // Create a new TwigNode instance using the provided prefix and key.
        let mut twig = TwigNode::new(prefix, key);

        // Insert the provided value into the TwigNode along with the version.
        twig.insert_mut(value, version, ts);

        // Return a new Node instance encapsulating the constructed Twig node.
        Self {
            node_type: NodeType::Twig(twig),
        }
    }

    /// Creates a new inner Node4 node with the provided prefix.
    ///
    /// Constructs a new Node4 node using the provided prefix. Node4 is an inner node
    /// type that can store up to 4 child pointers and uses arrays for keys and pointers.
    ///
    /// # Parameters
    ///
    /// - `prefix`: The common prefix for the Node4 node.
    ///
    /// # Returns
    ///
    /// Returns a new `Node` instance with an empty Node4 node.
    ///
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn new_node4(prefix: P) -> Self {
        // Create a new FlatNode instance using the provided prefix.
        let flat_node = FlatNode::new(prefix);

        // Create a new Node4 instance with the constructed FlatNode.
        Self {
            node_type: NodeType::Node4(flat_node),
        }
    }

    /// Checks if the current node is full based on its type.
    ///
    /// Determines if the current node is full by comparing the number of children to its
    /// capacity, which varies based on the node type.
    ///
    /// # Returns
    ///
    /// Returns `true` if the node is full, `false` otherwise.
    ///
    #[inline]
    fn is_full(&self) -> bool {
        match &self.node_type {
            NodeType::Node4(n) => n.num_children() >= n.size(),
            NodeType::Node16(n) => n.num_children() >= n.size(),
            NodeType::Node48(n) => n.num_children() >= n.size(),
            NodeType::Node256(n) => n.num_children() > n.size(),
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in is_full()"),
        }
    }

    /// Adds a child node with the given key to the current node.
    ///
    /// Inserts a child node with the specified key into the current node.
    /// Depending on the node type, this may lead to growth if the node becomes full.
    ///
    /// # Parameters
    ///
    /// - `key`: The key associated with the child node.
    /// - `child`: The child node to be added.
    ///
    /// # Returns
    ///
    /// Returns a new `Node` instance with the added child node.
    ///
    #[inline]
    fn add_child(&self, key: u8, child: Node<P, V>) -> Self {
        let cloned_node = if self.is_full() {
            self.grow()
        } else {
            match &self.node_type {
                NodeType::Node4(n) => Self {
                    node_type: NodeType::Node4(n.clone()),
                },
                NodeType::Node16(n) => Self {
                    node_type: NodeType::Node16(n.clone()),
                },
                NodeType::Node48(n) => Self {
                    node_type: NodeType::Node48(n.clone()),
                },
                NodeType::Node256(n) => Self {
                    node_type: NodeType::Node256(n.clone()),
                },
                NodeType::Twig(_) => panic!("Unexpected Twig node encountered in add_child()"),
            }
        };

        match cloned_node.node_type {
            NodeType::Node4(mut n) => {
                // Add the child node to the Node4 instance.
                n.add_child(key, child);
                let node = NodeType::Node4(n);

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
            }
            NodeType::Node16(mut n) => {
                // Add the child node to the Node16 instance.
                n.add_child(key, child);
                let node = NodeType::Node16(n);

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
            }
            NodeType::Node48(mut n) => {
                // Add the child node to the Node48 instance.
                n.add_child(key, child);
                let node = NodeType::Node48(n);

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
            }
            NodeType::Node256(mut n) => {
                // Add the child node to the Node256 instance.
                n.add_child(key, child);
                let node = NodeType::Node256(n);

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
            }
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in add_child_mut()"),
        }
    }

    #[inline]
    fn add_child_mut(&mut self, key: u8, child: Node<P, V>) {
        if self.is_full() {
            let new_node = self.grow();
            *self = new_node;
        }

        match &mut self.node_type {
            NodeType::Node4(ref mut n) => {
                // Add the child node to the Node4 instance.
                n.add_child(key, child);
            }
            NodeType::Node16(ref mut n) => {
                // Add the child node to the Node16 instance.
                n.add_child(key, child);
            }
            NodeType::Node48(ref mut n) => {
                // Add the child node to the Node48 instance.
                n.add_child(key, child);
            }
            NodeType::Node256(ref mut n) => {
                // Add the child node to the Node256 instance.
                n.add_child(key, child);
            }
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in add_child()"),
        }
    }

    /// Grows the current node to the next bigger size.
    ///
    /// Grows the current node to a larger size based on its type.
    /// This method is typically used to upgrade nodes when they become full.
    ///
    /// ArtNodes of type NODE4 will grow to NODE16
    /// ArtNodes of type NODE16 will grow to NODE48.
    /// ArtNodes of type NODE48 will grow to NODE256.
    /// ArtNodes of type NODE256 will not grow, as they are the biggest type of ArtNodes
    #[inline]
    fn grow(&self) -> Self {
        let node_type = match &self.node_type {
            NodeType::Node4(n) => {
                // Grow a Node4 to a Node16 by resizing.
                NodeType::Node16(n.resize())
            }
            NodeType::Node16(n) => {
                // Grow a Node16 to a Node48 by performing growth.
                NodeType::Node48(n.grow())
            }
            NodeType::Node48(n) => {
                // Grow a Node48 to a Node256 by performing growth.
                NodeType::Node256(n.grow())
            }
            NodeType::Node256 { .. } => {
                panic!("Node256 cannot be grown further");
            }
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in grow()"),
        };
        Self { node_type }
    }

    /// Recursively searches for a child node with the specified key.
    ///
    /// Searches for a child node with the given key in the current node.
    /// The search continues recursively in the child nodes based on the node type.
    ///
    /// # Parameters
    ///
    /// - `key`: The key associated with the child node.
    ///
    /// # Returns
    ///
    /// Returns an `Option` containing a reference to the found child node or `None` if not found.
    ///
    #[inline]
    fn find_child(&self, key: u8) -> Option<&Arc<Node<P, V>>> {
        // If there are no children, return None.
        if self.num_children() == 0 {
            return None;
        }

        // Match the node type to find the child using the appropriate method.
        match &self.node_type {
            NodeType::Node4(n) => n.find_child(key),
            NodeType::Node16(n) => n.find_child(key),
            NodeType::Node48(n) => n.find_child(key),
            NodeType::Node256(n) => n.find_child(key),
            NodeType::Twig(_) => None,
        }
    }

    #[inline]
    fn find_child_mut(&mut self, key: u8) -> Option<&mut Node<P, V>> {
        // If there are no children, return None.
        if self.num_children() == 0 {
            return None;
        }

        // Match the node type to find the child using the appropriate method.
        match &mut self.node_type {
            NodeType::Node4(n) => n.find_child_mut(key),
            NodeType::Node16(n) => n.find_child_mut(key),
            NodeType::Node48(n) => n.find_child_mut(key),
            NodeType::Node256(n) => n.find_child_mut(key),
            NodeType::Twig(_) => None,
        }
    }

    /// Replaces a child node with a new node for the given key.
    ///
    /// Replaces the child node associated with the specified key with the provided new node.
    ///
    /// # Parameters
    ///
    /// - `key`: The key associated with the child node to be replaced.
    /// - `node`: The new node to replace the existing child node.
    ///
    /// # Returns
    ///
    /// Returns a new `Node` instance with the child node replaced.
    ///
    fn replace_child(&self, key: u8, node: Arc<Node<P, V>>) -> Self {
        match &self.node_type {
            NodeType::Node4(n) => {
                // Replace the child node in the Node4 instance and update the NodeType.
                let node = NodeType::Node4(n.replace_child(key, node));
                Self { node_type: node }
            }
            NodeType::Node16(n) => {
                // Replace the child node in the Node16 instance and update the NodeType.
                let node = NodeType::Node16(n.replace_child(key, node));
                Self { node_type: node }
            }
            NodeType::Node48(n) => {
                // Replace the child node in the Node48 instance and update the NodeType.
                let node = NodeType::Node48(n.replace_child(key, node));
                Self { node_type: node }
            }
            NodeType::Node256(n) => {
                // Replace the child node in the Node256 instance and update the NodeType.
                let node = NodeType::Node256(n.replace_child(key, node));
                Self { node_type: node }
            }
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in replace_child()"),
        }
    }

    /// Removes a child node with the specified key from the current node.
    ///
    /// Removes a child node with the provided key from the current node.
    /// Depending on the node type, this may trigger shrinking if the number of children becomes low.
    ///
    /// # Parameters
    ///
    /// - `key`: The key associated with the child node to be removed.
    ///
    /// # Returns
    ///
    /// Returns a new `Node` instance with the child node removed.
    ///
    #[inline]
    fn delete_child(&self, key: u8) -> Self {
        match &self.node_type {
            NodeType::Node4(n) => {
                // Delete the child node from the Node4 instance and update the NodeType.
                let node = NodeType::Node4(n.delete_child(key));
                let mut new_node = Self { node_type: node };

                // Shrink if the number of remaining children is below the threshold and
                // there's no inner twig.
                //
                // Checking for the inner twig is only needed for Node4, because only its
                // shrink() implementation pulls up a single remaining child and replaces
                // itself with it in the tree.
                if new_node.num_children() < NODE4MIN && new_node.get_inner_twig().is_none() {
                    new_node.shrink();
                }

                new_node
            }
            NodeType::Node16(n) => {
                // Delete the child node from the Node16 instance and update the NodeType.
                let node = NodeType::Node16(n.delete_child(key));
                let mut new_node = Self { node_type: node };

                // Check if the number of remaining children is below the threshold.
                if new_node.num_children() < NODE16MIN {
                    new_node.shrink();
                }

                new_node
            }
            NodeType::Node48(n) => {
                // Delete the child node from the Node48 instance and update the NodeType.
                let node = NodeType::Node48(n.delete_child(key));
                let mut new_node = Self { node_type: node };

                // Check if the number of remaining children is below the threshold.
                if new_node.num_children() < NODE48MIN {
                    new_node.shrink();
                }

                new_node
            }
            NodeType::Node256(n) => {
                // Delete the child node from the Node256 instance and update the NodeType.
                let node = NodeType::Node256(n.delete_child(key));
                let mut new_node = Self { node_type: node };

                // Check if the number of remaining children is below the threshold.
                if new_node.num_children() < NODE256MIN {
                    new_node.shrink();
                }

                new_node
            }
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in delete_child()"),
        }
    }

    /// Checks if the node type is a Twig node.
    ///
    /// Determines whether the current node is a Twig node based on its node type.
    ///
    /// # Returns
    ///
    /// Returns `true` if the node type is a Twig node, otherwise returns `false`.
    ///
    #[inline]
    pub(crate) fn is_twig(&self) -> bool {
        matches!(&self.node_type, NodeType::Twig(_))
    }

    /// Checks if the node type is an inner node.
    ///
    /// Determines whether the current node is an inner node, which includes Node4, Node16, Node48, and Node256.
    /// The check is performed based on the absence of a Twig node.
    ///
    /// # Returns
    ///
    /// Returns `true` if the node type is an inner node, otherwise returns `false`.
    ///
    #[allow(dead_code)]
    pub(crate) fn is_inner(&self) -> bool {
        !self.is_twig()
    }

    /// Gets the prefix associated with the node.
    ///
    /// Retrieves the prefix associated with the current node based on its node type.
    ///
    /// # Returns
    ///
    /// Returns a reference to the prefix associated with the node.
    ///
    #[inline]
    pub(crate) fn prefix(&self) -> &P {
        match &self.node_type {
            NodeType::Node4(n) => &n.prefix,
            NodeType::Node16(n) => &n.prefix,
            NodeType::Node48(n) => &n.prefix,
            NodeType::Node256(n) => &n.prefix,
            NodeType::Twig(n) => &n.prefix,
        }
    }

    /// Sets the prefix for the node.
    ///
    /// Updates the prefix associated with the current node based on its node type.
    ///
    /// # Parameters
    ///
    /// - `prefix`: The new prefix to be associated with the node.
    ///
    #[inline]
    fn set_prefix(&mut self, prefix: P) {
        // The prefixes of a node and its inner twig must be kept
        // the same, because remove() relies on this when replacing
        // a Node4 without children with its inner twig.
        if let Some(inner_twig) = self.get_inner_twig_mut() {
            inner_twig.prefix = prefix.clone();
        } else if let Some(inner_twig) = self.get_inner_twig() {
            let mut cloned_twig = inner_twig.clone();
            cloned_twig.prefix = prefix.clone();
            self.set_inner_twig(cloned_twig);
        }

        self.node_type.set_prefix(prefix);
    }

    /// Shrinks the current node to a smaller size.
    ///
    /// Shrinks the current node to a smaller size based on its type.
    /// This method is typically used to downgrade nodes when the number of children becomes low.
    ///
    /// ArtNodes of type NODE256 will shrink to NODE48
    /// ArtNodes of type NODE48 will shrink to NODE16.
    /// ArtNodes of type NODE16 will shrink to NODE4.
    /// ArtNodes of type NODE4 will collapse into its first child.
    ///
    /// If that child is not a twig, it will concatenate its current prefix with that of its childs
    /// before replacing itself.
    fn shrink(&mut self) {
        match &mut self.node_type {
            NodeType::Node4(n) => {
                // Shrink Node4 to Node1 by resizing it.
                // In an Adaptive Radix Tree (ART), when a node has only one child,
                // it can be collapsed into its first child to save space and improve efficiency.
                // During this process, the prefix of the current node and the prefix of the child node
                // are combined (compressed) into a single prefix.
                let (curr_prefix, child) = n.get_value_if_single_child();
                let child = child.unwrap();
                let child_type = child.node_type.clone();
                let new_prefix = curr_prefix.extend(child.prefix());
                self.node_type = child_type;
                self.set_prefix(new_prefix);
            }
            NodeType::Node16(n) => {
                // Shrink Node16 to Node4 by resizing it.
                self.node_type = NodeType::Node4(n.resize());
            }
            NodeType::Node48(n) => {
                // Shrink Node48 to Node16 by obtaining the shrunken Node16 instance.
                let n16 = n.shrink();

                // Update the node type to Node16 after the shrinking operation.
                let new_node = NodeType::Node16(n16);
                self.node_type = new_node;
            }
            NodeType::Node256(n) => {
                // Shrink Node256 to Node48 by obtaining the shrunken Node48 instance.
                let n48 = n.shrink();

                // Update the node type to Node48 after the shrinking operation.
                self.node_type = NodeType::Node48(n48);
            }
            NodeType::Twig(_) => panic!("Twig node encountered in shrink()"),
        }
    }

    fn set_inner_twig(&mut self, leaf: TwigNode<P, V>) {
        let node = Node {
            node_type: NodeType::Twig(leaf),
        };
        let new_leaf = Some(Arc::new(node));
        match &mut self.node_type {
            NodeType::Node4(n) => {
                n.inner_twig = new_leaf;
            }
            NodeType::Node16(n) => {
                n.inner_twig = new_leaf;
            }
            NodeType::Node48(n) => {
                n.inner_twig = new_leaf;
            }
            NodeType::Node256(n) => {
                n.inner_twig = new_leaf;
            }
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in set_inner_twig()"),
        }
    }

    fn get_inner_twig(&self) -> Option<&TwigNode<P, V>> {
        let leaf_node = self.node_type.get_inner_twig()?;
        match &leaf_node.node_type {
            NodeType::Twig(twig) => Some(twig),
            _ => panic!("Unexpected non-Twig node encountered in get_inner_twig()"),
        }
    }

    fn get_inner_twig_mut(&mut self) -> Option<&mut TwigNode<P, V>> {
        let leaf_node = self.node_type.get_inner_twig_mut()?;
        match &mut leaf_node.node_type {
            NodeType::Twig(twig) => Some(twig),
            _ => panic!("Unexpected non-Twig node encountered in get_inner_twig_mut()"),
        }
    }

    fn delete_inner_twig(&self) -> Self {
        let node_type = match &self.node_type {
            NodeType::Node4(n) => {
                let mut cloned = n.clone();
                cloned.inner_twig.take();
                NodeType::Node4(cloned)
            }
            NodeType::Node16(n) => {
                let mut cloned = n.clone();
                cloned.inner_twig.take();
                NodeType::Node16(cloned)
            }
            NodeType::Node48(n) => {
                let mut cloned = n.clone();
                cloned.inner_twig.take();
                NodeType::Node48(cloned)
            }
            NodeType::Node256(n) => {
                let mut cloned = n.clone();
                cloned.inner_twig.take();
                NodeType::Node256(cloned)
            }
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in delete_inner_twig()"),
        };
        Self { node_type }
    }

    #[inline]
    pub(crate) fn num_children(&self) -> usize {
        match &self.node_type {
            NodeType::Node4(n) => n.num_children(),
            NodeType::Node16(n) => n.num_children(),
            NodeType::Node48(n) => n.num_children(),
            NodeType::Node256(n) => n.num_children(),
            NodeType::Twig(_) => 0,
        }
    }

    #[inline]
    pub(crate) fn get_leaf_by_query(&self, query_type: QueryType) -> Option<Arc<LeafValue<V>>> {
        let twig = if let NodeType::Twig(twig) = &self.node_type {
            // For a Twig node simply use its inner value.
            twig
        } else {
            // For an interior node, use its inner Twig if exists.
            self.get_inner_twig()?
        };

        twig.get_leaf_by_query(query_type)
    }

    #[inline]
    pub(crate) fn get_all_versions(&self) -> Option<Vec<(V, u64, u64)>> {
        // Unwrap the NodeType::Twig to access the TwigNode instance.
        let NodeType::Twig(twig) = &self.node_type else {
            return None;
        };

        // Get the value from the TwigNode instance by the specified version.
        let val = twig.get_all_versions();

        // Return the retrieved key, value, and version as a tuple.
        Some(val)
    }

    #[allow(unused)]
    pub(crate) fn node_type_name(&self) -> String {
        match &self.node_type {
            NodeType::Node4(_) => "Node4".to_string(),
            NodeType::Node16(_) => "Node16".to_string(),
            NodeType::Node48(_) => "Node48".to_string(),
            NodeType::Node256(_) => "Node256".to_string(),
            NodeType::Twig(_) => "Twig".to_string(),
        }
    }

    /// Creates a clone of the current node.
    ///
    /// Creates and returns a new instance of the current node with the same node type and contents.
    ///
    /// # Returns
    ///
    /// Returns a cloned instance of the current node with the same node type and contents.
    ///
    fn clone_node(&self) -> Self {
        // Create a new instance with the same node type as the current node.
        Self {
            node_type: self.node_type.clone(),
        }
    }

    // Common logic for insert to extract common prefix and key prefix
    fn common_insert_logic<'a>(
        cur_node_prefix: &P,
        key: &'a P,
        depth: usize,
    ) -> (
        &'a [u8], // remaining_key_suffix
        P,        // remaining_node_suffix
        P,        // shared_prefix
        bool,     // is_prefix_match
        usize,    // shared_prefix_length
    ) {
        // Obtain the current node's prefix and its length.
        let cur_node_prefix_len = cur_node_prefix.len();

        // Determine the prefix of the key after the current depth.
        let remaining_key_suffix = key.prefix_after(depth);

        // Find the longest common prefix between the current node's prefix and the key's prefix.
        let shared_prefix_length = cur_node_prefix.longest_common_prefix(remaining_key_suffix);

        // Create a new key that represents the remaining part of the current node's prefix after the common prefix.
        let mut remaining_node_suffix = cur_node_prefix.prefix_after(shared_prefix_length);
        if remaining_node_suffix.is_empty() {
            // In the case where the current node's prefix is shorter than the key,
            // the suffix comes from the key_prefix. For example, cur_node.prefix="key"
            // and key="keyboard", then remaining_node_suffix should be "board".
            remaining_node_suffix = &remaining_key_suffix[shared_prefix_length..];
        }

        // Extract the prefix of the current node up to the common prefix.
        let shared_prefix = cur_node_prefix.prefix_before(shared_prefix_length).into();
        // Determine whether the current node's prefix and the key's prefix match up to the common prefix.
        let is_prefix_match =
            min(cur_node_prefix_len, remaining_key_suffix.len()) == shared_prefix_length;

        (
            remaining_key_suffix, // remaining_key_suffix: the part of the key that still needs to be processed
            remaining_node_suffix.into(), // remaining_node_suffix: the remaining part of the node's prefix after splitting
            shared_prefix, // shared_prefix: the shared prefix that will become the new parent node
            is_prefix_match, // is_prefix_match: whether the prefixes match completely up to the common point
            shared_prefix_length, // shared_prefix_length: length of the shared prefix between node and key
        )
    }

    /// Recursively inserts a key-value pair into the current node and its child nodes.
    pub(crate) fn insert_recurse(
        cur_node: &Arc<Node<P, V>>,
        key: &P,
        value: V,
        commit_version: u64,
        ts: u64,
        depth: usize,
        replace: bool,
    ) -> NodeArc<P, V> {
        let (key_prefix, new_prefix, shared_prefix, is_prefix_match, shared_prefix_length) =
            Self::common_insert_logic(cur_node.prefix(), key, depth);

        // Case 1: No prefix match - create new Node4 with split
        if !is_prefix_match {
            // If the prefixes don't match, create a new Node4 with the old node and a new Twig as children.
            let mut old_node = cur_node.clone_node();
            old_node.set_prefix(new_prefix);
            let k1 = cur_node.prefix().at(shared_prefix_length);
            let k2 = key_prefix[shared_prefix_length];
            let new_twig = Node::new_twig(
                key_prefix[shared_prefix_length..].into(),
                key.as_slice().into(),
                value,
                commit_version,
                ts,
            );

            let mut n4 = Node::new_node4(shared_prefix);
            n4 = n4.add_child(k1, old_node).add_child(k2, new_twig);
            return Arc::new(n4);
        }

        // Case 2: Handle prefix match scenarios
        let cur_prefix_len = cur_node.prefix().len();
        let key_prefix_len = key_prefix.len();

        match cur_prefix_len.cmp(&key_prefix_len) {
            // Case 2a: Exact prefix match
            Ordering::Equal => {
                // If the current node is a Twig node and the prefixes match up to the end of both prefixes,
                // update the existing value in the Twig node.
                if let NodeType::Twig(twig) = &cur_node.node_type {
                    let new_twig = twig.insert_or_replace(value, commit_version, ts, replace);
                    Arc::new(Node {
                        node_type: NodeType::Twig(new_twig),
                    })
                } else {
                    // If the current node is an inner node, then either insert the new value
                    // in its existing inner Twig node, or create new one.
                    let leaf = match cur_node.get_inner_twig() {
                        Some(twig) => twig.insert_or_replace(value, commit_version, ts, replace),
                        None => {
                            let mut new_twig =
                                TwigNode::new(cur_node.prefix().clone(), key.as_slice().into());
                            new_twig.insert_mut(value, commit_version, ts);
                            new_twig
                        }
                    };
                    let mut new_node = cur_node.clone_node();
                    new_node.set_inner_twig(leaf);
                    Arc::new(new_node)
                }
            }

            // Case 2b: Current prefix is shorter and node is Twig
            Ordering::Less => {
                // The current node is Twig and there is a prefix match and the current node's
                // prefix is shorter than the remainder of the key, e.g. current node is "key1"
                // and "key123" is inserted.
                // Current Twig must be replaced by a Node4, made its inner Twig node, and a new
                // Twig node created as a normal child node with a prefix being the reminder of
                // the new key.
                let k = key_prefix[shared_prefix_length];

                // Case 2b1: Current node is Twig
                if let NodeType::Twig(twig) = &cur_node.node_type {
                    let mut n4 = Node::new_node4(shared_prefix);
                    n4.set_inner_twig(twig.clone());
                    let new_twig =
                        Node::new_twig(new_prefix, key.clone(), value, commit_version, ts);
                    n4.add_child_mut(k, new_twig);
                    Arc::new(n4)
                } else {
                    // Case 2b2: Continue traversal with existing child
                    if let Some(child) = cur_node.find_child(k) {
                        let new_child = Node::insert_recurse(
                            child,
                            key,
                            value,
                            commit_version,
                            ts,
                            depth + shared_prefix_length,
                            replace,
                        );
                        let new_node = cur_node.replace_child(k, new_child);
                        return Arc::new(new_node);
                    }

                    // Case 2b3: Create new child node
                    let new_twig = Node::new_twig(
                        key_prefix[shared_prefix_length..].into(),
                        key.as_slice().into(),
                        value,
                        commit_version,
                        ts,
                    );
                    let new_node = cur_node.add_child(k, new_twig);
                    Arc::new(new_node)
                }
            }

            // Case 2c: Current prefix is longer
            Ordering::Greater => {
                // Similar to the case above, but this time the current node's prefix is longer
                // than the remainder of the key, e.g. current node is "key123" and "key1" is
                // inserted.
                // Current node is also replaced by a new Node4, but this time its prefix is
                // adjusted and it becomes the Node4's child, while the new Twig node becomes
                // Node4's inner Twig.
                let mut inner_twig = TwigNode::new(key_prefix.into(), key.clone());
                inner_twig.insert_mut(value, commit_version, ts);
                let old_node_key = new_prefix.at(0);
                let mut old_node = cur_node.clone_node();
                old_node.set_prefix(new_prefix);

                let mut n4 = Node::new_node4(key_prefix.into());
                n4.set_inner_twig(inner_twig);
                n4.add_child_mut(old_node_key, old_node);
                Arc::new(n4)
            }
        }
    }

    pub(crate) fn insert_recurse_mut(
        cur_node: &mut Node<P, V>,
        key: &P,
        value: V,
        commit_version: u64,
        ts: u64,
        depth: usize,
        replace: bool,
    ) {
        let (key_prefix, new_prefix, shared_prefix, is_prefix_match, shared_prefix_length) =
            Self::common_insert_logic(cur_node.prefix(), key, depth);

        // Case 1: No prefix match - create a new Node4 with old node and new Twig as children
        if !is_prefix_match {
            let n4 = Node::new_node4(shared_prefix);

            let k1 = cur_node.prefix().at(shared_prefix_length);
            let k2 = key_prefix[shared_prefix_length];

            // Must be set after the calculation of k1 above
            cur_node.set_prefix(new_prefix);

            let old_node = std::mem::replace(cur_node, n4);

            let new_twig = Node::new_twig(
                key_prefix[shared_prefix_length..].into(),
                key.as_slice().into(),
                value,
                commit_version,
                ts,
            );
            cur_node.add_child_mut(k1, old_node);
            cur_node.add_child_mut(k2, new_twig);

            return;
        }

        // Case 2: Handle prefix match scenarios
        let cur_prefix_len = cur_node.prefix().len();
        let key_prefix_len = key_prefix.len();

        match cur_prefix_len.cmp(&key_prefix_len) {
            // Case 2a: Exact prefix match
            Ordering::Equal => {
                // If the current node is a Twig node and the prefixes match up to the
                // end of both prefixes, update the existing value in the Twig node.
                if let NodeType::Twig(ref mut twig) = &mut cur_node.node_type {
                    if replace {
                        // Only replace if the provided value is more recent than
                        // the existing ones. This is important because this method
                        // is used for loading the index in SurrealKV and thus must
                        // be able to handle segments left by an unfinished compaction
                        // where older versions can end up in more recent segments
                        // after the newer versions.
                        twig.replace_if_newer_mut(value, commit_version, ts);
                    } else {
                        twig.insert_mut(value, commit_version, ts);
                    }
                } else {
                    // If the current node is an inner node, then either insert the new value
                    // in its existing inner Twig node, or create new one.
                    match cur_node.get_inner_twig_mut() {
                        Some(twig) => {
                            if replace {
                                twig.replace_if_newer_mut(value, commit_version, ts);
                            } else {
                                twig.insert_mut(value, commit_version, ts);
                            }
                        }
                        None => {
                            let mut new_twig =
                                TwigNode::new(cur_node.prefix().clone(), key.as_slice().into());
                            new_twig.insert_mut(value, commit_version, ts);
                            cur_node.set_inner_twig(new_twig);
                        }
                    }
                }
            }

            // Case 2b: Current prefix is shorter and node is Twig
            // e.g., current node is "key1" and "key123" is inserted
            Ordering::Less => {
                let k = key_prefix[shared_prefix_length];
                if cur_node.is_twig() {
                    // The current node is Twig and there is a prefix match and the current node's
                    // prefix is shorter than the remainder of the key, e.g. current node is "key1"
                    // and "key123" is inserted.
                    // Current Twig must be replaced by a Node4, made its inner Twig node, and a new
                    // Twig node created as a normal child node with a prefix being the reminder of
                    // the new key.
                    let n4 = Node::new_node4(shared_prefix);
                    let old_twig = std::mem::replace(cur_node, n4);
                    match old_twig.node_type {
                        NodeType::Twig(n) => cur_node.set_inner_twig(n),
                        _ => panic!("must be Twig"),
                    }
                    let new_twig =
                        Node::new_twig(new_prefix, key.clone(), value, commit_version, ts);
                    cur_node.add_child_mut(k, new_twig);
                } else {
                    // Case 2b2: Continue traversal with existing child
                    if let Some(child) = cur_node.find_child_mut(k) {
                        Node::insert_recurse_mut(
                            child,
                            key,
                            value,
                            commit_version,
                            ts,
                            depth + shared_prefix_length,
                            replace,
                        );
                        return;
                    }

                    // Case 2b3: Create new child node
                    // If no child exists for the key's character, create a new Twig node and add it as a child.
                    let new_twig = Node::new_twig(
                        key_prefix[shared_prefix_length..].into(),
                        key.as_slice().into(),
                        value,
                        commit_version,
                        ts,
                    );
                    cur_node.add_child_mut(k, new_twig);
                }
            }

            // Case 2c: Current prefix is longer
            // e.g., current node is "key123" and "key1" is inserted
            Ordering::Greater => {
                // Similar to the case above, but this time the current node's prefix is longer
                // than the remainder of the key, e.g. current node is "key123" and "key1" is
                // inserted.
                // Current node is also replaced by a new Node4, but this time its prefix is
                // adjusted and it becomes the Node4's child, while the new Twig node becomes
                // Node4's inner Twig.
                let n4 = Node::new_node4(key_prefix.into());
                let mut old_node = std::mem::replace(cur_node, n4);
                let mut inner_twig = TwigNode::new(key_prefix.into(), key.clone());
                inner_twig.insert_mut(value, commit_version, ts);
                cur_node.set_inner_twig(inner_twig);
                let old_node_key = new_prefix.at(0);
                old_node.set_prefix(new_prefix);
                cur_node.add_child_mut(old_node_key, old_node);
            }
        }
    }

    fn navigate_to_node<'a>(cur_node: &'a Node<P, V>, key: &P) -> Option<&'a Node<P, V>> {
        let mut cur_node = cur_node;
        let mut depth = 0;

        loop {
            let key_prefix = key.prefix_after(depth);
            let prefix = cur_node.prefix();
            let lcp = prefix.longest_common_prefix(key_prefix);

            if lcp != prefix.len() {
                return None;
            }

            if prefix.len() == key_prefix.len() {
                return Some(cur_node);
            }

            let k = key.at(depth + prefix.len());
            depth += prefix.len();

            match cur_node.find_child(k) {
                Some(child) => cur_node = child,
                None => return None,
            }
        }
    }

    /// Recursively searches for a key in the node and its children.
    pub(crate) fn get_recurse(
        cur_node: &Node<P, V>,
        key: &P,
        query_type: QueryType,
    ) -> Option<(V, u64, u64)> {
        let cur_node = Self::navigate_to_node(cur_node, key)?;
        let val = cur_node.get_leaf_by_query(query_type)?;
        Some((val.value.clone(), val.version, val.ts))
    }

    pub(crate) fn get_version_history(
        cur_node: &Node<P, V>,
        key: &P,
    ) -> Option<Vec<(V, u64, u64)>> {
        Self::navigate_to_node(cur_node, key).and_then(|cur_node| cur_node.get_all_versions())
    }

    /// Returns an iterator that iterates over child nodes of the current node.
    ///
    /// This function provides an iterator that traverses through the child nodes of the current node,
    /// returning tuples of keys and references to child nodes.
    ///
    /// # Returns
    ///
    /// Returns a boxed iterator that yields tuples containing keys and references to child nodes.
    ///
    pub(crate) fn iter(&self) -> Box<dyn DoubleEndedIterator<Item = &Arc<Self>> + '_> {
        match &self.node_type {
            NodeType::Node4(n) => Box::new(n.iter()),
            NodeType::Node16(n) => Box::new(n.iter()),
            NodeType::Node48(n) => Box::new(n.iter()),
            NodeType::Node256(n) => Box::new(n.iter()),
            NodeType::Twig(_) => Box::new(std::iter::empty()),
        }
    }
}

/// A struct representing an Adaptive Radix Trie.
///
/// The `Tree` struct encompasses the entire adaptive radix trie data structure.
/// It manages the root node of the tree.
///
/// # Type Parameters
///
/// - `P`: A type implementing the `KeyTrait` trait, defining the prefix traits for nodes.
/// - `V`: The type of value associated with nodes.
///
/// # Fields
///
/// - `root`: An optional shared reference (using `Rc`) to the root node of the tree.
///
pub struct Tree<P: KeyTrait, V: Clone> {
    /// An optional shared reference to the root node of the tree.
    pub(crate) root: Option<Arc<Node<P, V>>>,
    pub size: usize,
    pub version: u64,
}

// A type alias for a node reference.
type NodeArc<P, V> = Arc<Node<P, V>>;

impl<P: KeyTrait, V: Clone> NodeType<P, V> {
    fn clone(&self) -> Self {
        match self {
            // twig value not actually cloned
            NodeType::Twig(twig) => NodeType::Twig(twig.clone()),
            NodeType::Node4(n) => NodeType::Node4(n.clone()),
            NodeType::Node16(n) => NodeType::Node16(n.clone()),
            NodeType::Node48(n) => NodeType::Node48(n.clone()),
            NodeType::Node256(n) => NodeType::Node256(n.clone()),
        }
    }
}

// Default implementation for the Tree struct
impl<P: KeyTrait, V: Clone> Default for Tree<P, V> {
    fn default() -> Self {
        Tree::new()
    }
}

impl<P: KeyTrait, V: Clone> Clone for Tree<P, V> {
    fn clone(&self) -> Self {
        Self {
            root: self.root.as_ref().cloned(),
            size: self.size,
            version: self.version,
        }
    }
}

impl<P: KeyTrait, V: Clone> Tree<P, V> {
    pub fn new() -> Self {
        Tree {
            root: None,
            size: 0,
            version: 0,
        }
    }

    fn update_version(&mut self, version: u64) {
        self.version = if version == 0 {
            self.version + 1
        } else if version > self.version {
            version
        } else {
            self.version
        };
    }

    fn insert_common(
        &mut self,
        key: &P,
        value: V,
        version: u64,
        ts: u64,
        check_version: bool,
        replace: bool,
    ) -> Result<(), TrieError> {
        let new_root = match &self.root {
            None => {
                let commit_version = if version == 0 { 1 } else { version };
                Arc::new(Node::new_twig(
                    key.as_slice().into(),
                    key.as_slice().into(),
                    value,
                    commit_version,
                    ts,
                ))
            }
            Some(root) => {
                let curr_version = self.version;
                let mut commit_version = version;
                if version == 0 {
                    commit_version = curr_version + 1;
                } else if check_version && curr_version > version {
                    return Err(TrieError::VersionIsOld);
                }
                Node::insert_recurse(root, key, value, commit_version, ts, 0, replace)
            }
        };

        self.root = Some(new_root);
        self.size += 1;
        self.update_version(version);

        Ok(())
    }

    fn insert_common_mut(
        &mut self,
        key: &P,
        value: V,
        version: u64,
        ts: u64,
        check_version: bool,
        replace: bool,
    ) -> Result<(), TrieError> {
        if let Some(root_arc) = self.root.as_mut() {
            let curr_version = self.version;
            let mut commit_version = version;
            if version == 0 {
                commit_version = curr_version + 1;
            } else if check_version && curr_version > version {
                return Err(TrieError::VersionIsOld);
            }
            if let Some(root) = Arc::get_mut(root_arc) {
                Node::insert_recurse_mut(root, key, value, commit_version, ts, 0, replace)
            } else {
                return Err(TrieError::RootIsNotUniquelyOwned);
            }
        } else {
            let commit_version = if version == 0 { 1 } else { version };
            self.root = Some(Arc::new(Node::new_twig(
                key.as_slice().into(),
                key.as_slice().into(),
                value,
                commit_version,
                ts,
            )));
        }
        self.size += 1;
        self.update_version(version);

        Ok(())
    }

    /// Inserts a new key-value pair with the specified version into the Trie.
    ///
    /// This function inserts a new key-value pair into the Trie. If the key already exists,
    /// the previous value associated with the key is returned. The `version`` is used to
    /// ensure proper ordering of values for versioning. The `ts` parameter is used to
    /// record the timestamp of the insertion.
    ///
    /// This method ensures that the `version` provided is equal to or greater than the
    /// current version of the tree. If a strictly greater guarantee is required, then
    /// the caller is responsible for enforcing it.
    ///
    /// # Arguments
    ///
    /// * `key`: A reference to the key to be inserted.
    /// * `value`: The value to be associated with the key.
    /// * `version`: The version number for the key-value pair.
    /// * `ts`: The timestamp for the insertion, used for versioning.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on success.
    ///
    /// # Errors
    ///
    /// Returns an error if the given version is older than the root's current version.
    pub fn insert(&mut self, key: &P, value: V, version: u64, ts: u64) -> Result<(), TrieError> {
        self.insert_common(key, value, version, ts, true, false)
    }

    /// Inserts or replaces a key-value pair in the trie.
    ///
    /// This function inserts a new key-value pair into the trie or replaces the existing value
    /// if the key already exists. It ensures that the insertion is checked, meaning it will
    /// validate the keys are inserted in increasing order of version numbers.
    ///
    /// # Parameters
    /// - `key`: A reference to the key to be inserted or replaced.
    /// - `value`: The value to be associated with the key.
    /// - `version`: The version number for the key-value pair.
    /// - `ts`: The timestamp for the key-value pair.
    ///
    /// # Returns
    /// - `Result<(), TrieError>`: Returns `Ok(())` if the insertion or replacement is successful,
    ///   or a `TrieError` if an error occurs during the operation.
    pub fn insert_or_replace(
        &mut self,
        key: &P,
        value: V,
        version: u64,
        ts: u64,
    ) -> Result<(), TrieError> {
        self.insert_common(key, value, version, ts, true, true)
    }

    /// Inserts a key-value pair into the trie without checking for existing keys.
    ///
    /// This function inserts a new key-value pair into the trie without checking if the key
    /// already exists. It is an unchecked insertion, meaning it will not check if the versions
    /// are incremental during insertion. This can be faster but may lead to inconsistencies
    /// if not used carefully.
    ///
    /// This function also avoids the Copy-on-Write overhead of the `Arc` type by using mutable
    /// references to the nodes. This can be useful when the caller knows that the root node
    /// is uniquely owned and can be mutated directly.
    ///
    /// # Parameters
    /// - `key`: A reference to the key to be inserted.
    /// - `value`: The value to be associated with the key.
    /// - `version`: The version number for the key-value pair.
    /// - `ts`: The timestamp for the key-value pair.
    ///
    /// # Returns
    /// - `Result<(), TrieError>`: Returns `Ok(())` if the insertion is successful,
    ///   or a `TrieError` if an error occurs during the operation.
    pub fn insert_unchecked(
        &mut self,
        key: &P,
        value: V,
        version: u64,
        ts: u64,
    ) -> Result<(), TrieError> {
        self.insert_common_mut(key, value, version, ts, false, false)
    }

    /// Inserts or replaces a key-value pair in the trie without checking for existing keys.
    ///
    /// This function inserts a new key-value pair into the trie or replaces the existing value
    /// if the key already exists. It is an unchecked insertion, meaning it will not check if the versions
    /// are incremental during insertion. This can be faster but may lead to inconsistencies
    /// if not used carefully.
    ///
    /// # Parameters
    /// - `key`: A reference to the key to be inserted or replaced.
    /// - `value`: The value to be associated with the key.
    /// - `version`: The version number for the key-value pair.
    /// - `ts`: The timestamp for the key-value pair.
    ///
    /// # Returns
    /// - `Result<(), TrieError>`: Returns `Ok(())` if the insertion or replacement is successful,
    ///   or a `TrieError` if an error occurs during the operation.
    pub fn insert_or_replace_unchecked(
        &mut self,
        key: &P,
        value: V,
        version: u64,
        ts: u64,
    ) -> Result<(), TrieError> {
        self.insert_common_mut(key, value, version, ts, false, true)
    }

    /// Removes the key from the current node or one of its child nodes
    /// while building an updated copy of the Tree on its way up the recursion.
    ///
    /// # Parameters
    ///
    /// - `cur_node`: A reference to the current node.
    /// - `key`: The key to be removed.
    /// - `depth`: The depth of the removal process.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing the updated node (or `None`) and a flag
    /// indicating if the key was removed.
    fn remove_recursive(
        cur_node: &Node<P, V>,
        key: &P,
        depth: usize,
    ) -> (Option<Arc<Node<P, V>>>, bool) {
        let key_prefix = key.prefix_after(depth);
        let prefix = cur_node.prefix();
        let lcp = prefix.longest_common_prefix(key_prefix);

        // Current node's prefix does not match the remainder of the
        // key. This means there's no key in the Tree, so recourse up
        // with nothing. This will keep the original Tree root unaffected.
        if lcp != prefix.len() {
            return (None, false);
        }

        // Current node's prefix completely matches the remainder of the key.
        // This must be the Twig node. It's copy-on-write removed by returning
        // (None, true). This will signal the caller to remove the associated
        // child link from the parent inner node.
        if prefix.len() == key_prefix.len() {
            if cur_node.is_twig() {
                return (None, true);
            } else if cur_node.get_inner_twig().is_some() {
                let mut node_without_leaf = cur_node.delete_inner_twig();
                if node_without_leaf.num_children() == 1 {
                    // If this inner node has only one child, then it must
                    // be Node4. Its shrink() implementation is special in
                    // that for a single child it will pull the child up
                    // and replace itself with it.
                    node_without_leaf.shrink();
                }
                return (Some(Arc::new(node_without_leaf)), true);
            } else {
                // This is an inner node without a leaf, so no match.
                return (None, false);
            }
        }

        // Current node's prefix matches the prefix of the remainder
        // of the key. Continue the search down the Tree while building
        // its copy.
        let new_depth = depth + prefix.len();
        let k = key.at(new_depth);
        if let Some(child) = cur_node.find_child(k) {
            match Self::remove_recursive(child, key, new_depth) {
                (Some(new_child), true) => {
                    let new_node = cur_node.replace_child(k, new_child);
                    return (Some(Arc::new(new_node)), true);
                }
                (None, true) => {
                    // The key has been found, so either remove the corresponding
                    // child link from the current node if that's not its
                    // last child, or pull up its inner Twig node into this
                    // position in the tree, or simply return (None, true)
                    // if there's nothing to occupy this position.
                    if cur_node.num_children() == 1 {
                        if cur_node.get_inner_twig().is_some() {
                            let cloned_twig = cur_node.node_type.clone_inner_twig();
                            return (cloned_twig, true);
                        } else {
                            return (None, true);
                        }
                    } else {
                        let new_node = cur_node.delete_child(k);
                        return (Some(Arc::new(new_node)), true);
                    }
                }
                _ => {}
            }
        }

        (None, false)
    }

    /// Removes a key with all the versions associated with it from the Trie.
    ///
    /// This function removes a key and all its associated versions from the Trie.
    ///
    /// # Arguments
    ///
    /// * `key`: A reference to the key to be removed.
    ///
    /// # Returns
    ///
    /// Returns `true` if the key was successfully removed, `false` otherwise.
    pub fn remove(&mut self, key: &P) -> bool {
        let root = match self.root.as_deref() {
            Some(root) => root,
            None => return false,
        };

        let (new_root, is_deleted) = Tree::remove_recursive(root, key, 0);

        // Update the root and return the deletion status.
        if is_deleted {
            self.root = new_root;
            self.size -= 1;
        }
        is_deleted
    }

    /// Retrieves the value associated with the given key at a given version from the Trie.
    ///
    /// This function searches for the value associated with the specified key at the specified
    /// version in the Trie. If the version is set to 0, it retrieves the latest version available
    /// for the key. The function uses a recursive search to find the value.
    ///
    /// # Arguments
    ///
    /// * `key`: A reference to the key to be searched.
    /// * `version`: The version number to be searched. If set to 0, the latest version is retrieved.
    ///
    /// # Returns
    ///
    /// Returns an `Option` containing a tuple `(V, u64, u64)` if the key and version are found:
    /// - `V`: The value associated with the key.
    /// - `u64`: The version number of the value.
    /// - `u64`: The timestamp of the value.
    ///
    /// Returns `None` if the key or version is not found.
    pub fn get(&self, key: &P, version: u64) -> Option<(V, u64, u64)> {
        let root = self.root.as_ref()?;
        let mut commit_version = version;
        if commit_version == 0 {
            commit_version = self.version;
        }

        Node::get_recurse(root, key, QueryType::LatestByVersion(commit_version))
    }

    /// Retrieves the latest version inserted in the Trie.
    ///
    /// This function returns the latest version inserted in the Trie. This is used internally
    /// for surrealkv for determining the transaction id. The version only moves forward in time
    /// and does not get updated upon any removals. This behavior ensures that deletions do not
    /// roll back version to read at an older snapshot, which is crucial for internal use in
    /// SurrealKV for snapshot reads.
    ///
    /// # Returns
    ///
    /// Returns the version of the latest version of the Trie, or `0` if the Trie is empty.    
    pub fn version(&self) -> u64 {
        self.version
    }

    /// Creates an iterator over the Trie's key-value pairs.
    ///
    /// This function creates and returns an iterator that can be used to traverse the key-value pairs
    /// stored in the Trie. The iterator starts from the root of the Trie.
    ///
    /// # Returns
    ///
    /// Returns an `Iter` instance that iterates over the key-value pairs in the Trie.
    ///
    pub fn iter(&self) -> Iter<P, V> {
        Iter::new(self.root.as_ref(), false)
    }

    /// Creates a versioned iterator over the Trie's key-value pairs.
    ///
    /// This function creates and returns an iterator that can be used to traverse all the versions
    /// for all the key-value pairs stored in the Trie. The iterator starts from the root of the Trie.
    pub fn iter_with_versions(&self) -> Iter<P, V> {
        Iter::new(self.root.as_ref(), true)
    }

    /// Returns an iterator over a range of key-value pairs within the Trie.
    ///
    /// This function creates and returns an iterator that iterates over key-value pairs in the Trie,
    /// starting from the provided `start_key` and following the specified `range` bounds. The iterator
    /// iterates within the specified key range.
    ///
    /// # Arguments
    ///
    /// * `range` - A range that specifies the bounds for iterating over key-value pairs.
    ///
    /// # Returns
    ///
    /// Returns a `Range` iterator instance that iterates over the key-value pairs within the given range.
    /// If the Trie is empty, an empty `Range` iterator is returned.
    ///
    pub fn range<'a, R>(
        &'a self,
        range: R,
    ) -> impl Iterator<Item = (&'a [u8], &'a V, &'a u64, &'a u64)>
    where
        R: RangeBounds<P> + 'a,
    {
        // If the Trie is empty, return an empty Range iterator
        if self.root.is_none() {
            return Range::empty(range);
        }

        let root = self.root.as_ref();
        Range::new(root, range)
    }

    /// Returns an iterator over the key-value pairs within the specified range, including all the
    /// versions of the key.
    ///
    /// This function returns an iterator that yields key-value pairs along with their version
    /// and timestamp within the specified range. If the Trie is empty, it returns an empty iterator.
    ///
    /// # Arguments
    ///
    /// * `range`: The range of keys to be iterated over.
    ///
    /// # Returns
    ///
    /// Returns an iterator over the key-value pairs, versions, and timestamps within the specified range.
    pub fn range_with_versions<'a, R>(
        &'a self,
        range: R,
    ) -> impl Iterator<Item = (&'a [u8], &'a V, &'a u64, &'a u64)>
    where
        R: RangeBounds<P> + 'a,
    {
        // If the Trie is empty, return an empty Range iterator
        if self.root.is_none() {
            return Range::empty(range);
        }

        let root = self.root.as_ref();
        Range::new_versioned(root, range)
    }

    /// Retrieves the value associated with the given key at the specified timestamp.
    ///
    /// This function searches for the value associated with the specified key at the given
    /// timestamp in the Trie. It uses a recursive search to find the value.
    ///
    /// # Arguments
    ///
    /// * `key`: A reference to the key to be searched.
    /// * `ts`: The timestamp to be searched.
    ///
    /// # Returns
    ///
    /// Returns an `Option` containing a tuple `(V, u64, u64)` if the key and timestamp are found:
    /// - `V`: The value associated with the key.
    /// - `u64`: The version number of the value.
    /// - `u64`: The timestamp of the value.
    ///
    /// Returns `None` if the key or timestamp is not found.
    pub fn get_at_ts(&self, key: &P, ts: u64) -> Option<(V, u64, u64)> {
        let root = self.root.as_ref()?;
        Node::get_recurse(root, key, QueryType::LatestByTs(ts))
    }

    /// Retrieves the version history of the given key.
    ///
    /// This function searches for all versions of the specified key in the Trie and returns
    /// a vector of tuples containing the value, version number, and timestamp for each version.
    ///
    /// # Arguments
    ///
    /// * `key`: A reference to the key to be searched.
    ///
    /// # Returns
    ///
    /// Returns an `Option` containing a vector of tuples `(V, u64, u64)` if the key is found:
    /// - `V`: The value associated with the key.
    /// - `u64`: The version number of the value.
    /// - `u64`: The timestamp of the value.
    ///
    /// Returns `None` if the key is not found.
    pub fn get_version_history(&self, key: &P) -> Option<Vec<(V, u64, u64)>> {
        let root = self.root.as_ref()?;
        Node::get_version_history(root, key)
    }

    /// Retrieves the value associated with the given key based on the specified query type.
    ///
    /// This function searches for the value associated with the specified key based on the
    /// provided query type in the Trie. It uses a recursive search to find the value.
    ///
    /// # Arguments
    ///
    /// * `key`: A reference to the key to be searched.
    /// * `query_type`: The type of query to be performed (e.g., latest by version, latest by timestamp).
    ///
    /// # Returns
    ///
    /// Returns an `Option` containing a tuple `(V, u64, u64)` if the key and query type are found:
    /// - `V`: The value associated with the key.
    /// - `u64`: The version number of the value.
    /// - `u64`: The timestamp of the value.
    ///
    /// Returns `None` if the key or query type is not found.
    pub fn get_value_by_query(&self, key: &P, query_type: QueryType) -> Option<(V, u64, u64)> {
        let root = self.root.as_ref()?;
        Node::get_recurse(root, key, query_type)
    }

    /// Checks if the Trie is empty.
    ///
    /// This function checks if the Trie contains any key-value pairs.
    ///
    /// # Returns
    ///
    /// Returns `true` if the Trie is empty, `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn scan_at_ts<'a, R>(
        &'a self,
        range: R,
        ts: u64,
    ) -> impl Iterator<Item = (Box<[u8]>, V)> + 'a
    where
        R: RangeBounds<P> + 'a,
    {
        scan_node(self.root.as_ref(), range, QueryType::LatestByTs(ts))
    }

    pub fn keys_at_ts<'a, R>(&'a self, range: R, ts: u64) -> impl Iterator<Item = Box<[u8]>> + 'a
    where
        R: RangeBounds<P> + 'a,
    {
        query_keys_at_node(self.root.as_ref(), range, QueryType::LatestByTs(ts))
    }

    /// Retrieves the maximum version inside the Trie.
    ///
    /// This function returns the maximum version found inside the Trie by traversing
    /// all the nodes. This version could be lesser than the current incremental version.
    pub fn max_version_in_trie(&self) -> u64 {
        self.iter()
            .map(|(_, _, version, _)| *version)
            .max()
            .unwrap_or(0)
    }
}

/*
    Test cases for Adaptive Radix Tree
*/

#[cfg(test)]
mod tests {
    use super::Tree;
    use crate::art::QueryType;
    use crate::{FixedSizeKey, VariableSizeKey};
    use rand::{seq::SliceRandom, thread_rng, Rng};
    use std::ops::RangeFull;
    use std::str::FromStr;

    use rand::distributions::Alphanumeric;
    use std::fs::File;
    use std::io::{self, BufRead, BufReader};

    fn read_words_from_file(file_path: &str) -> io::Result<Vec<String>> {
        let file = File::open(file_path)?;
        let reader = BufReader::new(file);
        let words: Vec<String> = reader.lines().map_while(Result::ok).collect();
        Ok(words)
    }

    #[test]
    fn insert_search_delete_words() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let file_path = "testdata/words.txt";

        if let Ok(words) = read_words_from_file(file_path) {
            // Insertion phase
            for word in &words {
                let key = &VariableSizeKey::from_str(word).unwrap();
                let _ = tree.insert(key, 1, 0, 0);
            }

            // Search phase
            for word in &words {
                let key = VariableSizeKey::from_str(word).unwrap();
                let (val, _, _) = tree.get(&key, 0).unwrap();
                assert_eq!(val, 1);
            }

            // Deletion phase
            for word in &words {
                let key = VariableSizeKey::from_str(word).unwrap();
                assert!(tree.remove(&key));
            }
        } else if let Err(err) = read_words_from_file(file_path) {
            eprintln!("Error reading file: {}", err);
        }
    }

    #[test]
    fn insert_search_delete_words_randomized() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let file_path = "testdata/words.txt";

        let mut words = read_words_from_file(file_path).expect("error reading file");

        // Shuffle the words
        words.shuffle(&mut thread_rng());

        // Insertion phase
        for word in &words {
            let key = &VariableSizeKey::from_str(word).unwrap();
            let _ = tree.insert(key, 1, 0, 0);
        }

        // Search phase
        for word in &words {
            let key = VariableSizeKey::from_str(word).unwrap();
            let (val, _, _) = tree.get(&key, 0).unwrap();
            assert_eq!(val, 1);
        }

        // Deletion phase
        for word in &words {
            let key = VariableSizeKey::from_str(word).unwrap();
            assert!(tree.remove(&key));
        }
    }

    #[test]
    fn insert_mut_search_delete_words_randomized() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let file_path = "testdata/words.txt";

        let mut words = read_words_from_file(file_path).expect("error reading file");

        // Shuffle the words
        words.shuffle(&mut thread_rng());

        // Insertion phase
        for word in &words {
            let key = &VariableSizeKey::from_str(word).unwrap();
            let _ = tree.insert_unchecked(key, 1, 0, 0);
        }

        // Search phase
        for word in &words {
            let key = VariableSizeKey::from_str(word).unwrap();
            let (val, _, _) = tree.get(&key, 0).unwrap();
            assert_eq!(val, 1);
        }

        // Deletion phase
        for word in &words {
            let key = VariableSizeKey::from_str(word).unwrap();
            assert!(tree.remove(&key));
        }
    }

    #[test]
    fn remove_with_one_child_and_inner_twig() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let k1 = VariableSizeKey::from_slice(b"aam");
        let k2 = VariableSizeKey::from_slice(b"aa");
        let k3 = VariableSizeKey::from_slice(b"aal");

        let _ = tree.insert(&k1, 1, 0, 0);
        let _ = tree.insert(&k2, 2, 0, 0);
        let _ = tree.insert(&k3, 3, 0, 0);

        assert_eq!(tree.get(&k1, 0).unwrap().0, 1);
        assert_eq!(tree.get(&k2, 0).unwrap().0, 2);
        assert_eq!(tree.get(&k3, 0).unwrap().0, 3);

        assert!(tree.remove(&k1));
        assert!(tree.remove(&k2));
        assert!(tree.remove(&k3));
    }

    #[test]
    fn descending_keys() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let ccc = VariableSizeKey::from_slice(b"ccc");
        let cc = VariableSizeKey::from_slice(b"cc");
        let c = VariableSizeKey::from_slice(b"c");

        let _ = tree.insert(&ccc, 1, 0, 0);
        let _ = tree.insert(&cc, 2, 0, 0);
        let _ = tree.insert(&c, 3, 0, 0);

        assert_eq!(tree.get(&ccc, 0).unwrap().0, 1);
        assert_eq!(tree.get(&cc, 0).unwrap().0, 2);
        assert_eq!(tree.get(&c, 0).unwrap().0, 3);

        assert!(tree.remove(&ccc));
        assert!(tree.remove(&cc));
        assert!(tree.remove(&c));
    }

    #[test]
    fn string_insert_delete() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion phase
        let insert_words = [
            "a", "aa", "aal", "aalii", "abc", "abcd", "abcde", "xyz", "axyz",
        ];

        for word in &insert_words {
            let _ = tree.insert(&VariableSizeKey::from_str(word).unwrap(), 1, 0, 0);
        }

        // Deletion phase
        for word in &insert_words {
            assert!(tree.remove(&VariableSizeKey::from_str(word).unwrap()));
        }
    }

    #[test]
    fn string_long() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion phase
        let words_to_insert = [
            ("amyelencephalia", 1),
            ("amyelencephalic", 2),
            ("amyelencephalous", 3),
        ];

        for (word, val) in &words_to_insert {
            let _ = tree.insert(&VariableSizeKey::from_str(word).unwrap(), *val, 0, 0);
        }

        // Verification phase
        for (word, expected_val) in &words_to_insert {
            let (val, _, _) = tree
                .get(&VariableSizeKey::from_str(word).unwrap(), 0)
                .unwrap();
            assert_eq!(val, *expected_val);
        }
    }

    #[test]
    fn root_set_get() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion phase
        let key = VariableSizeKey::from_str("abc").unwrap();
        let value = 1;
        let _ = tree.insert(&key, value, 0, 0);

        // Verification phase
        let (val, _ts, _) = tree.get(&key, 0).unwrap();
        assert_eq!(val, value);
    }

    #[test]
    fn string_duplicate_insert() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // First insertion
        let key = VariableSizeKey::from_str("abc").unwrap();
        let value = 1;
        tree.insert(&key, value, 0, 0).expect("Failed to insert");
        let (val, version, ts) = tree.get(&key, 0).unwrap();
        assert!(val == value);
        assert!(version == 1);
        assert!(ts == 0);

        // Second insertion (duplicate)
        let value = 2;
        tree.insert(&key, value, 0, 0).expect("Failed to insert");
        let (val, version, ts) = tree.get(&key, 0).unwrap();
        assert!(val == value);
        assert!(version == 2);
        assert!(ts == 0);
    }

    // Inserting a single value into the tree and removing it should result in a nil tree root.
    #[test]
    fn insert_and_remove_single_key() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        let key = VariableSizeKey::from_str("test").unwrap();
        let value = 1;
        let _ = tree.insert(&key, value, 0, 0);

        // Removal
        assert!(tree.remove(&key));

        // Verification
        assert!(tree.get(&key, 0).is_none());
    }

    #[test]
    fn inserting_keys_with_common_prefix() {
        let key1 = VariableSizeKey::from_str("foo").unwrap();
        let key2 = VariableSizeKey::from_str("foo2").unwrap();

        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        tree.insert(&key1, 1, 0, 0).unwrap();
        tree.insert(&key2, 1, 0, 0).unwrap();

        // Removal
        assert!(tree.remove(&key1));

        // Root verification
        if let Some(root) = &tree.root {
            assert_eq!(root.node_type_name(), "Twig");
        } else {
            panic!("Tree root is None");
        }
    }

    // Inserting Two values into the tree and removing one of them
    // should result in a tree root of type twig
    #[test]
    fn insert2_and_remove1_and_root_should_be_node1() {
        let key1 = VariableSizeKey::from_str("test1").unwrap();
        let key2 = VariableSizeKey::from_str("test2").unwrap();

        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        tree.insert(&key1, 1, 0, 0).unwrap();
        tree.insert(&key2, 1, 0, 0).unwrap();

        // Removal
        assert!(tree.remove(&key1));

        // Root verification
        if let Some(root) = &tree.root {
            assert_eq!(root.node_type_name(), "Twig");
        } else {
            panic!("Tree root is None");
        }
    }

    // Inserting Two values into a tree and deleting them both
    // should result in a nil tree root
    // This tests the expansion of the root into a NODE4 and
    // successfully collapsing into a twig and then nil upon successive removals
    #[test]
    fn insert2_and_remove2_and_root_should_be_nil() {
        let key1 = &VariableSizeKey::from_str("test1").unwrap();
        let key2 = &VariableSizeKey::from_str("test2").unwrap();

        let mut tree = Tree::<VariableSizeKey, i32>::new();
        tree.insert(key1, 1, 0, 0).unwrap();
        tree.insert(key2, 1, 0, 0).unwrap();

        assert!(tree.remove(key1));
        assert!(tree.remove(key2));

        assert!(tree.root.is_none());
    }

    // Inserting Five values into a tree and deleting one of them
    // should result in a tree root of type NODE4
    // This tests the expansion of the root into a NODE16 and
    // successfully collapsing into a NODE4 upon successive removals
    #[test]
    fn insert5_and_remove1_and_root_should_be_node4() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        for i in 0..5u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1, 0, 0).unwrap();
        }

        // Removal
        let key_to_remove = VariableSizeKey::from_slice(&1u32.to_be_bytes());
        assert!(tree.remove(&key_to_remove));

        // Root verification
        if let Some(root) = &tree.root {
            assert!(root.is_inner());
            assert_eq!(root.node_type_name(), "Node4");
        } else {
            panic!("Tree root is None");
        }
    }

    // Inserting Five values into a tree and deleting all of them
    // should result in a tree root of type nil
    // This tests the expansion of the root into a NODE16 and
    // successfully collapsing into a NODE4, twig, then nil
    #[test]
    fn insert5_and_remove5_and_root_should_be_nil() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        for i in 0..5u32 {
            let key = &VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1, 0, 0).unwrap();
        }

        for i in 0..5u32 {
            let key = &VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.remove(key);
        }

        assert!(tree.root.is_none());
    }

    // Inserting 17 values into a tree and deleting one of them should
    // result in a tree root of type NODE16
    // This tests the expansion of the root into a NODE48, and
    // successfully collapsing into a NODE16
    #[test]
    fn insert17_and_remove1_and_root_should_be_node16() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        for i in 0..17u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1, 0, 0).unwrap();
        }

        // Removal
        let key_to_remove = VariableSizeKey::from_slice(&2u32.to_be_bytes());
        assert!(tree.remove(&key_to_remove));

        // Root verification
        if let Some(root) = &tree.root {
            assert!(root.is_inner());
            assert_eq!(root.node_type_name(), "Node16");
        } else {
            panic!("Tree root is None");
        }
    }

    #[test]
    fn insert17_and_root_should_be_node48() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        for i in 0..17u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1, 0, 0).unwrap();
        }

        // Root verification
        if let Some(root) = &tree.root {
            assert!(root.is_inner());
            assert_eq!(root.node_type_name(), "Node48");
        } else {
            panic!("Tree root is None");
        }
    }

    // Inserting 17 values into a tree and removing them all should
    // result in a tree of root type nil
    // This tests the expansion of the root into a NODE48, and
    // successfully collapsing into a NODE16, NODE4, twig, and then nil
    #[test]
    fn insert17_and_remove17_and_root_should_be_nil() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        for i in 0..17u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1, 0, 0).unwrap();
        }

        for i in 0..17u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.remove(&key);
        }

        assert!(tree.root.is_none());
    }

    // Inserting 49 values into a tree and removing one of them should
    // result in a tree root of type NODE48
    // This tests the expansion of the root into a NODE256, and
    // successfully collapasing into a NODE48
    #[test]
    fn insert49_and_remove1_and_root_should_be_node48() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        for i in 0..49u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1, 0, 0).unwrap();
        }

        // Removal
        let key_to_remove = VariableSizeKey::from_slice(&2u32.to_be_bytes());
        assert!(tree.remove(&key_to_remove));

        // Root verification
        if let Some(root) = &tree.root {
            assert!(root.is_inner());
            assert_eq!(root.node_type_name(), "Node48");
        } else {
            panic!("Tree root is None");
        }
    }

    #[test]
    fn insert49_and_root_should_be_node248() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        for i in 0..49u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1, 0, 0).unwrap();
        }

        // Root verification
        if let Some(root) = &tree.root {
            assert!(root.is_inner());
            assert_eq!(root.node_type_name(), "Node256");
        } else {
            panic!("Tree root is None");
        }
    }

    // Inserting 49 values into a tree and removing all of them should
    // result in a nil tree root
    // This tests the expansion of the root into a NODE256, and
    // successfully collapsing into a Node48, Node16, Node4, twig, and finally nil
    #[test]
    fn insert49_and_remove49_and_root_should_be_nil() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        for i in 0..49u32 {
            let key = &VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(key, 1, 0, 0).unwrap();
        }

        for i in 0..49u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            assert!(tree.remove(&key));
        }

        assert!(tree.root.is_none());
    }

    #[derive(Debug, Clone, PartialEq)]
    struct Kvt {
        k: Vec<u8>,   // Key
        version: u64, // version
    }

    #[test]
    fn timed_insertion() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();

        let kvts = vec![
            Kvt {
                k: b"key1_0".to_vec(),
                version: 0,
            },
            Kvt {
                k: b"key2_0".to_vec(),
                version: 0,
            },
            Kvt {
                k: b"key3_0".to_vec(),
                version: 0,
            },
            Kvt {
                k: b"key4_0".to_vec(),
                version: 0,
            },
            Kvt {
                k: b"key5_0".to_vec(),
                version: 0,
            },
            Kvt {
                k: b"key6_0".to_vec(),
                version: 0,
            },
        ];

        // Insertion
        for (idx, kvt) in kvts.iter().enumerate() {
            let ts = if kvt.version == 0 {
                idx as u64 + 1
            } else {
                kvt.version
            };
            assert!(tree
                .insert(&VariableSizeKey::from(kvt.k.clone()), 1, ts, 0)
                .is_ok());
        }

        // Verification
        let mut curr_version = 1;
        for kvt in &kvts {
            let key = VariableSizeKey::from(kvt.k.clone());
            let (val, version, _ts) = tree.get(&key, 0).unwrap();
            assert_eq!(val, 1);

            if kvt.version == 0 {
                assert_eq!(curr_version, version);
            } else {
                assert_eq!(kvt.version, version);
            }

            curr_version += 1;
        }

        // Root's version should match the greatest inserted version
        assert_eq!(kvts.len() as u64, tree.version());
    }

    #[test]
    fn timed_insertion_update_same_key() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();

        let key1 = &VariableSizeKey::from_str("key_1").unwrap();

        // insert key1 with version 0
        assert!(tree.insert(key1, 1, 0, 1).is_ok());
        // update key1 with version 0
        assert!(tree.insert(key1, 1, 0, 3).is_ok());

        // get key1 should return version 2 as the same key was inserted and updated
        let (val, version, ts) = tree.get(key1, 0).unwrap();
        assert_eq!(val, 1);
        assert_eq!(version, 2);
        assert_eq!(ts, 3);

        // update key1 with older version should fail
        assert!(tree.insert(key1, 1, 1, 0).is_err());
        assert_eq!(tree.version(), 2);

        // update key1 with newer version should pass
        assert!(tree.insert(key1, 1, 8, 5).is_ok());
        let (val, version, ts) = tree.get(key1, 0).unwrap();
        assert_eq!(val, 1);
        assert_eq!(version, 8);
        assert_eq!(ts, 5);

        assert_eq!(tree.version(), 8);
    }

    #[test]
    fn timed_insertion_update_non_increasing_version() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();

        let key1 = VariableSizeKey::from_str("key_1").unwrap();
        let key2 = VariableSizeKey::from_str("key_2").unwrap();

        // Initial insertion
        assert!(tree.insert(&key1, 1, 10, 0).is_ok());
        let initial_version_key1 = tree.version();

        // Attempt update with non-increasing version
        assert!(tree.insert(&key1, 1, 2, 0).is_err());
        assert_eq!(initial_version_key1, tree.version());
        let (val, version, _) = tree.get(&key1, 0).unwrap();
        assert_eq!(val, 1);
        assert_eq!(version, 10);

        // Insert another key
        assert!(tree.insert(&key2, 1, 15, 0).is_ok());
        let initial_version_key2 = tree.version();

        // Attempt update with non-increasing version for the second key
        assert!(tree.insert(&key2, 1, 11, 0).is_err());
        assert_eq!(initial_version_key2, tree.version());
        let (val, version, _ts) = tree.get(&key2, 0).unwrap();
        assert_eq!(val, 1);
        assert_eq!(version, 15);

        // Check if the max version of the tree is the max of the two inserted versions
        assert_eq!(tree.version(), 15);
    }

    #[test]
    fn timed_deletion_check_root_ts() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let key1 = VariableSizeKey::from_str("key_1").unwrap();
        let key2 = VariableSizeKey::from_str("key_2").unwrap();

        // Initial insertions
        assert!(tree.insert(&key1, 1, 0, 0).is_ok());
        assert!(tree.insert(&key2, 1, 0, 0).is_ok());
        assert_eq!(tree.version(), 2);

        // Deletions
        assert!(tree.remove(&key1));
        assert!(tree.remove(&key2));

        // tree version should still be 2
        assert_eq!(tree.version(), 2);

        // max version in the tree should be 0 post deletions
        assert_eq!(tree.max_version_in_trie(), 0);
    }

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
    fn iter_seq_u16() {
        let mut tree = Tree::<FixedSizeKey<16>, u16>::new();

        // Insertion
        for i in 0..u16::MAX {
            let key: FixedSizeKey<16> = i.into();
            tree.insert(&key, i, 0, i as u64).unwrap();
        }

        // Iteration and verification
        let mut len = 0usize;
        let mut expected = 0u16;

        let tree_iter = tree.iter();
        for tree_entry in tree_iter {
            let k = from_be_bytes_key(tree_entry.0);
            assert_eq!(expected as u64, k);
            let ts = tree_entry.3;
            assert_eq!(expected as u64, *ts);
            expected = expected.wrapping_add(1);
            len += 1;
        }

        // Final assertion
        assert_eq!(len, u16::MAX as usize);
    }

    #[test]
    fn iter_seq_u8() {
        let mut tree: Tree<FixedSizeKey<32>, u8> = Tree::<FixedSizeKey<32>, u8>::new();

        // Insertion
        for i in 0..u8::MAX {
            let key: FixedSizeKey<32> = i.into();
            tree.insert(&key, i, 0, 0).unwrap();
        }

        // Iteration and verification
        let mut len = 0usize;
        let mut expected = 0u8;

        let tree_iter = tree.iter();
        for tree_entry in tree_iter {
            let k = from_be_bytes_key(tree_entry.0);
            assert_eq!(expected as u64, k);
            expected = expected.wrapping_add(1);
            len += 1;
        }

        // Final assertion
        assert_eq!(len, u8::MAX as usize);
    }

    #[test]
    fn range_seq_u8() {
        let mut tree: Tree<FixedSizeKey<8>, u8> = Tree::<FixedSizeKey<8>, u8>::new();

        let max = u8::MAX;
        // Insertion
        for i in 0..=max {
            let key: FixedSizeKey<8> = i.into();
            tree.insert(&key, i, 0, 0).unwrap();
        }

        // Test inclusive range
        let start_key: FixedSizeKey<8> = 5u8.into();
        let end_key: FixedSizeKey<8> = max.into();
        let mut len = 0usize;
        for _ in tree.range(start_key..=end_key) {
            len += 1;
        }
        assert_eq!(len, max as usize - 4);

        // Test exclusive range
        let start_key: FixedSizeKey<8> = 5u8.into();
        let end_key: FixedSizeKey<8> = max.into();
        let mut len = 0usize;
        for _ in tree.range(start_key..end_key) {
            len += 1;
        }
        assert_eq!(len, max as usize - 5);

        // Test range with different start and end keys
        let start_key: FixedSizeKey<8> = 3u8.into();
        let end_key: FixedSizeKey<8> = 7u8.into();
        let mut len = 0usize;
        for _ in tree.range(start_key..=end_key) {
            len += 1;
        }
        assert_eq!(len, 5);

        // Test range with all keys
        let start_key: FixedSizeKey<8> = 0u8.into();
        let end_key: FixedSizeKey<8> = max.into();
        let mut len = 0usize;
        for _ in tree.range(start_key..=end_key) {
            len += 1;
        }
        assert_eq!(len, 256);
    }

    #[test]
    fn range_seq_u16() {
        let mut tree: Tree<FixedSizeKey<16>, u16> = Tree::<FixedSizeKey<16>, u16>::new();

        let max = u16::MAX;
        // Insertion
        for i in 0..=max {
            let key: FixedSizeKey<16> = i.into();
            tree.insert(&key, i, 0, 0).unwrap();
        }

        let mut len = 0usize;
        let start_key: FixedSizeKey<16> = 0u8.into();
        let end_key: FixedSizeKey<16> = max.into();

        for _ in tree.range(start_key..=end_key) {
            len += 1;
        }
        assert_eq!(len, max as usize + 1);
    }

    #[test]
    fn same_key_with_versions() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertions
        let key1 = VariableSizeKey::from_str("abc").unwrap();
        let key2 = VariableSizeKey::from_str("efg").unwrap();
        tree.insert(&key1, 1, 0, 0).unwrap();
        tree.insert(&key1, 2, 10, 0).unwrap();
        tree.insert(&key2, 3, 11, 0).unwrap();

        // Versioned retrievals and assertions
        let (val, _, _) = tree.get(&key1, 1).unwrap();
        assert_eq!(val, 1);
        let (val, _, _) = tree.get(&key1, 10).unwrap();
        assert_eq!(val, 2);
        let (val, _, _) = tree.get(&key2, 11).unwrap();
        assert_eq!(val, 3);

        // Iteration and verification
        let mut len = 0;
        let tree_iter = tree.iter();
        for _ in tree_iter {
            len += 1;
        }
        assert_eq!(len, 2);
    }

    #[test]
    fn insert_and_remove() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let version = 0;

        // Keys to set
        let set_keys = vec![
            [107, 101, 121, 48, 48, 0],
            [107, 101, 121, 48, 49, 0],
            [107, 101, 121, 48, 50, 0],
            [107, 101, 121, 48, 51, 0],
            [107, 101, 121, 48, 52, 0],
            [107, 101, 121, 48, 53, 0],
            [107, 101, 121, 48, 54, 0],
            [107, 101, 121, 48, 55, 0],
            [107, 101, 121, 48, 56, 0],
            [107, 101, 121, 48, 57, 0],
            [107, 101, 121, 49, 48, 0],
            [107, 101, 121, 49, 49, 0],
            [107, 101, 121, 49, 50, 0],
            [107, 101, 121, 49, 51, 0],
            [107, 101, 121, 49, 52, 0],
            [107, 101, 121, 49, 53, 0],
            [107, 101, 121, 49, 54, 0],
            [107, 101, 121, 49, 55, 0],
            [107, 101, 121, 49, 56, 0],
            [107, 101, 121, 49, 57, 0],
            [107, 101, 121, 50, 48, 0],
            [107, 101, 121, 50, 49, 0],
            [107, 101, 121, 50, 50, 0],
            [107, 101, 121, 50, 51, 0],
            [107, 101, 121, 50, 52, 0],
            [107, 101, 121, 50, 53, 0],
        ];

        // Insert keys
        for key_data in &set_keys {
            let key = VariableSizeKey {
                data: key_data.to_vec(),
            };
            tree.insert(&key, 1, version, 0).unwrap();
        }

        // Delete one key at a time and check remaining keys
        for (index, key_data_to_delete) in set_keys.iter().enumerate() {
            let key_to_delete = VariableSizeKey {
                data: key_data_to_delete.to_vec(),
            };
            tree.remove(&key_to_delete);

            // Check remaining keys are still present
            for (remaining_index, remaining_key_data) in set_keys.iter().enumerate() {
                if remaining_index <= index {
                    // Check that the deleted key is no longer present
                    assert!(
                        tree.get(&key_to_delete, version).is_none(),
                        "Key {:?} should not exist after deletion",
                        key_data_to_delete
                    );
                    // This key has been deleted; skip
                    continue;
                }
                let remaining_key = VariableSizeKey {
                    data: remaining_key_data.to_vec(),
                };
                assert!(
                    tree.get(&remaining_key, version).is_some(),
                    "Key {:?} should exist",
                    remaining_key_data
                );
            }
        }
    }

    fn generate_sequential_keys(count: usize) -> Vec<Vec<u8>> {
        (0..count)
            .map(|i| {
                let mut key = i.to_le_bytes().to_vec();
                key.push(0); // Ensure each key ends with 0
                key
            })
            .collect()
    }

    fn generate_random_keys(count: usize) -> Vec<Vec<u8>> {
        let mut rng = thread_rng();
        (0..count)
            .map(|_| {
                let mut key: Vec<u8> = (0..5).map(|_| rng.gen()).collect(); // Generate a key of 5 random bytes
                key.push(0); // Ensure each key ends with 0
                key
            })
            .collect()
    }

    fn insert_remove_and_verify_keys(set_keys: Vec<Vec<u8>>) {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let version = 0;

        // Insert keys
        for key_data in &set_keys {
            let key = VariableSizeKey {
                data: key_data.to_vec(),
            };
            tree.insert(&key, 1, version, 0).unwrap();
        }

        // Delete one key at a time and check remaining keys
        for (index, key_data_to_delete) in set_keys.iter().enumerate() {
            let key_to_delete = VariableSizeKey {
                data: key_data_to_delete.to_vec(),
            };
            tree.remove(&key_to_delete);

            // Check remaining keys are still present
            for (remaining_index, remaining_key_data) in set_keys.iter().enumerate() {
                if remaining_index <= index {
                    // Check that the deleted key is no longer present
                    assert!(
                        tree.get(&key_to_delete, version).is_none(),
                        "Key {:?} should not exist after deletion",
                        key_data_to_delete
                    );
                    // This key has been deleted; skip
                    continue;
                }
                let remaining_key = VariableSizeKey {
                    data: remaining_key_data.to_vec(),
                };
                assert!(
                    tree.get(&remaining_key, version).is_some(),
                    "Key {:?} should exist",
                    remaining_key_data
                );
            }
        }
    }

    #[test]
    fn test_insert_remove_and_verify_keys_large_sequential() {
        insert_remove_and_verify_keys(generate_sequential_keys(1000)); // Generate 1000 sequential keys
    }

    #[test]
    fn test_insert_remove_and_verify_keys_large_random() {
        insert_remove_and_verify_keys(generate_random_keys(1000)); // Generate 1000 random keys
    }

    #[test]
    fn remove_non_existent_key() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("nonexistent").unwrap();
        let is_removed = tree.remove(&key);
        assert!(!is_removed);
    }

    #[test]
    fn remove_key_from_empty_tree() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("test").unwrap();
        let is_removed = tree.remove(&key);
        assert!(!is_removed);
    }

    #[test]
    fn sequential_removals() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let keys = vec!["first", "second", "third"]
            .into_iter()
            .map(|k| VariableSizeKey::from_str(k).unwrap())
            .collect::<Vec<_>>();

        // Insert keys
        for key in &keys {
            let _ = tree.insert(key, 1, 0, 0);
        }

        // Remove keys sequentially
        for key in &keys {
            assert!(tree.remove(key));
        }

        // Verify all keys are removed
        for key in keys {
            assert!(tree.get(&key, 0).is_none());
        }
    }

    #[test]
    fn remove_until_empty() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let keys = vec!["key1", "key2", "key3"]
            .into_iter()
            .map(|k| VariableSizeKey::from_str(k).unwrap())
            .collect::<Vec<_>>();

        // Insert keys
        for key in &keys {
            let _ = tree.insert(key, 1, 0, 0);
        }

        // Remove all keys
        for key in &keys {
            let is_removed = tree.remove(key);
            assert!(is_removed);
        }
    }

    #[test]
    fn remove_with_subsequent_inserts() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let key1 = VariableSizeKey::from_str("key1").unwrap();
        let key2 = VariableSizeKey::from_str("key2").unwrap();

        // Initial insert
        let _ = tree.insert(&key1, 1, 0, 0);
        // Remove
        assert!(tree.remove(&key1));
        // Insert another key
        let _ = tree.insert(&key2, 2, 0, 0);

        // Verify
        assert!(tree.get(&key1, 0).is_none());
        assert_eq!(tree.get(&key2, 0).unwrap().0, 2);
    }

    #[test]
    fn insert_with_random_versions_and_verify_count() {
        use rand::seq::SliceRandom;
        use rand::Rng;
        use std::collections::HashMap;

        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let num_keys = 1000; // Large number of keys
        let mut rng = rand::thread_rng();
        let mut expected_entries = 0;

        // Generate an array of increasing versions and shuffle it
        let mut versions: Vec<usize> = (1..=num_keys).collect();
        versions.shuffle(&mut rng);

        // HashMap to store key-version mapping
        let mut key_version_map = HashMap::new();

        for (i, &version) in versions.iter().enumerate().take(num_keys) {
            let id = format!("key{}", i + 1);
            let key = VariableSizeKey::from_str(&id).unwrap();
            if tree
                .insert_unchecked(&key, rng.gen::<i32>(), version as u64, 0)
                .is_ok()
            {
                expected_entries += 1;
                key_version_map.insert(id, version);
            }
        }

        // Verification
        for (key, version) in key_version_map.iter() {
            let key = VariableSizeKey::from_str(key).unwrap();
            assert!(
                tree.get(&key, *version as u64).is_some(),
                "The key {:?} at version {} should be present in the tree.",
                key,
                version
            );
        }

        // Iteration and verification
        let mut actual_entries = 0;
        let tree_iter = tree.iter();
        for _ in tree_iter {
            actual_entries += 1;
        }

        assert_eq!(
            actual_entries, expected_entries,
            "The number of entries in the tree does not match the expected number of insertions."
        );

        assert_eq!(tree.version(), num_keys as u64);
    }

    #[test]
    fn insert_keys_in_decreasing_order_and_verify_count() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let num_keys = 1000;

        for i in (0..num_keys).rev() {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            tree.insert_unchecked(&key, i as i32, i, 0).unwrap();
        }

        // Verify total entries
        let total_entries = tree.iter().count() as u64;
        assert_eq!(
            total_entries, num_keys,
            "The total entries should be equal to the number of inserted keys."
        );

        assert_eq!(tree.version(), { num_keys });
    }

    #[test]
    fn insert_same_key_different_versions_without_version_check_and_verify() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("key1").unwrap();

        // Insert the same key with two different versions
        tree.insert_unchecked(&key, 2, 2, 0).unwrap(); // Second version
        tree.insert_unchecked(&key, 1, 1, 0).unwrap(); // First version

        // Verify the order during iteration
        let mut iter = tree.iter();
        let (_, value, version, _) = iter.next().unwrap();
        assert_eq!(value, &2);
        assert_eq!(version, &2);

        // Verify get at version 0 gives the latest version
        let (value, version, _) = tree.get(&key, 0).unwrap();
        assert_eq!(value, 2);
        assert_eq!(version, 2);

        assert_eq!(tree.version(), 2);
    }

    #[test]
    fn insert_multiple_keys_different_versions_and_verify() {
        let mut tree = Tree::<VariableSizeKey, u64>::new();
        let num_keys = 1000; // Large number of keys for the test

        // Insert two versions for each key
        for i in 0..num_keys {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            tree.insert_unchecked(&key, i as u64 + 1000, 2, 0).unwrap(); // Second version
            tree.insert_unchecked(&key, i as u64, 1, 0).unwrap(); // First version
        }

        // Verify get at version 0 gives the latest version for each key
        for i in 0..num_keys {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            let (value, version, _) = tree.get(&key, 0).unwrap();
            assert_eq!(
                value,
                i as u64 + 1000,
                "get at version 0 should return the latest version value."
            );
            assert_eq!(
                version, 2,
                "get at version 0 should return the latest version number."
            );
        }
    }

    #[test]
    fn test_range_scan_order_with_random_keys() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Define keys in random order
        let insert_words = ["test3", "test1", "test5", "test4", "test2", "test11"];

        // Insert keys into the tree
        for word in &insert_words {
            tree.insert(&VariableSizeKey::from_str(word).unwrap(), 1, 1, 1)
                .unwrap()
        }

        // Define a range that encompasses all keys
        let range = VariableSizeKey::from_slice("test1".as_bytes())
            ..=VariableSizeKey::from_slice("test5".as_bytes());

        // Collect results of the range scan
        let results: Vec<_> = tree.range(range).collect();
        assert_eq!(results.len(), insert_words.len());

        // Expected order
        let expected_order = ["test1", "test11", "test2", "test3", "test4", "test5"];

        // Assert that results are in expected order
        for (i, result) in results.iter().enumerate() {
            let result_str = std::str::from_utf8(result.0).expect("Invalid UTF-8");
            assert_eq!(result_str, expected_order[i]);
        }
    }

    #[test]
    fn test_add_keys_and_then_delete_keys_which_dont_exist() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insert 75 keys
        for i in 1..=75 {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            tree.insert(&key, i, i as u64, 0).unwrap();
        }

        // Attempt to delete 25 keys (76 to 100), which do not exist
        for i in 76..=100 {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            // Since these keys do not exist, remove should return an Err or false depending on implementation
            assert!(!tree.remove(&key));
        }

        // Verify versions of a few keys
        // For example, check the version of key1 and key75
        let key1 = VariableSizeKey::from_str("key1").unwrap();
        let key75 = VariableSizeKey::from_str("key75").unwrap();

        assert_eq!(tree.get(&key1, 0).unwrap().1, 1); // Check version of key1
        assert_eq!(tree.get(&key75, 0).unwrap().1, 75); // Check version of key75
    }

    #[test]
    fn test_nonexistent_key_removal_does_not_empty_tree() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        for i in 1..=1 {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            let _ = tree.insert(&key, i, i as u64, 0);
        }

        for i in 2..=2 {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            // Since these keys do not exist, remove should return an Err or false depending on implementation
            assert!(!tree.remove(&key));
        }

        let key1 = VariableSizeKey::from_str("key1").unwrap();

        assert_eq!(tree.get(&key1, 0).unwrap().1, 1); // Check version of key1
    }

    #[test]
    fn test_tree_empty_after_removing_single_key() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insert a single key
        let key = VariableSizeKey::from_str("key1").unwrap();
        tree.insert(&key, 1, 1, 0).unwrap();

        // Remove the inserted key
        tree.remove(&key);

        // Verify the tree is empty
        assert!(tree.root.is_none());
    }

    #[test]
    fn verify_iter() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let mut rng = rand::thread_rng();
        let mut inserted_data = Vec::new();

        // Generate and insert random keys with versions
        for version in 1u64..=100 {
            let random_key: String = (0..10).map(|_| rng.sample(Alphanumeric) as char).collect();
            let key = VariableSizeKey::from_str(&random_key).unwrap();
            let value = rng.gen_range(1..100);
            let ts = rng.gen_range(1..100);
            tree.insert(&key, value, version, ts).unwrap();
            inserted_data.push((key.to_slice().to_vec(), value, version, ts));
        }

        // Iteration and verification
        let mut count = 0;
        let tree_iter = tree.iter();
        for (key, value, version, ts) in tree_iter {
            assert!(inserted_data.contains(&(key.to_vec(), *value, *version, *ts)));
            count += 1;
        }

        // Ensure all inserted items are iterated over
        assert_eq!(inserted_data.len(), count);
    }

    #[test]
    fn test_get_all_versions() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();

        // Scenario 1: Insert multiple values for the same key with different timestamps
        let key1 = VariableSizeKey::from_str("test_key1").unwrap();
        let value1_1 = 10;
        let value1_2 = 20;
        let ts1_1 = 100;
        let ts1_2 = 200;
        tree.insert(&key1, value1_1, 0, ts1_1).unwrap();
        tree.insert(&key1, value1_2, 0, ts1_2).unwrap();

        let history1 = tree.get_version_history(&key1).unwrap();
        assert_eq!(history1.len(), 2);

        let (retrieved_value1_1, v1_1, t1_1) = history1[0];
        assert_eq!(retrieved_value1_1, value1_1);
        assert_eq!(v1_1, 1);
        assert_eq!(t1_1, ts1_1);

        let (retrieved_value1_2, v1_2, t1_2) = history1[1];
        assert_eq!(retrieved_value1_2, value1_2);
        assert_eq!(v1_2, 2);
        assert_eq!(t1_2, ts1_2);

        // Scenario 2: Insert values for different keys
        let key2 = VariableSizeKey::from_str("test_key2").unwrap();
        let value2 = 30;
        let ts2 = 300;
        tree.insert(&key2, value2, 0, ts2).unwrap();

        let history2 = tree.get_version_history(&key2).unwrap();
        assert_eq!(history2.len(), 1);

        let (retrieved_value2, v2, t2) = history2[0];
        assert_eq!(retrieved_value2, value2);
        assert_eq!(v2, 3);
        assert_eq!(t2, ts2);

        // Scenario 3: Ensure no history for a non-existent key
        let key3 = VariableSizeKey::from_str("non_existent_key").unwrap();
        assert!(tree.get_version_history(&key3).is_none());
    }

    #[test]
    fn test_retrieving_value_at_future_timestamp() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value = 10;
        let ts_insert = 100;
        let ts_future = 200;
        tree.insert(&key, value, 0, ts_insert).unwrap();

        let (retrieved_value, version, ts) = tree.get_at_ts(&key, ts_future).unwrap();
        assert_eq!(retrieved_value, value);
        assert_eq!(version, 1);
        assert_eq!(ts, ts_insert);
    }

    #[test]
    fn test_inserting_and_retrieving_with_same_timestamp() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value1 = 10;
        let value2 = 20;
        let ts = 100;
        tree.insert_unchecked(&key, value1, 1, ts).unwrap();
        tree.insert_unchecked(&key, value2, 1, ts).unwrap();

        let (retrieved_value, version, t) = tree.get_at_ts(&key, ts).unwrap();
        assert_eq!(retrieved_value, value2);
        assert_eq!(version, 1);
        assert_eq!(t, ts);
    }

    #[test]
    fn test_get_at_ts_successful_retrieval() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value = 10;
        let version = 1;
        let ts = 100;
        tree.insert(&key, value, version, ts).unwrap();

        let (retrieved_value, retrieved_version, retrieved_ts) = tree.get_at_ts(&key, ts).unwrap();
        assert_eq!(retrieved_value, value);
        assert_eq!(retrieved_version, version);
        assert_eq!(retrieved_ts, ts);
    }

    #[test]
    fn test_get_at_ts_key_not_found() {
        let tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("nonexistent_key").unwrap();
        let result = tree.get_at_ts(&key, 100);
        assert!(result.is_none());
    }

    #[test]
    fn test_get_at_ts_timestamp_before_insertion() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value = 10;
        let version = 1;
        let ts = 100;
        tree.insert(&key, value, version, ts).unwrap();

        let result = tree.get_at_ts(&key, ts - 1);
        assert!(result.is_none());
    }

    #[test]
    fn test_get_at_ts_multiple_versions() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value1 = 10;
        let value2 = 11;
        let version1 = 1;
        let version2 = 2;
        let ts1 = 100;
        let ts2 = 200;
        tree.insert(&key, value1, version1, ts1).unwrap();
        tree.insert(&key, value2, version2, ts2).unwrap();

        let (retrieved_value, retrieved_version, retrieved_ts) = tree.get_at_ts(&key, ts2).unwrap();
        assert_eq!(retrieved_value, value2);
        assert_eq!(retrieved_version, version2);
        assert_eq!(retrieved_ts, ts2);
    }

    #[test]
    fn test_retrieving_value_at_timestamp_between_two_inserts() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value1 = 10;
        let value2 = 20;
        let version1 = 1;
        let version2 = 2;
        let ts1 = 100;
        let ts2 = 200;
        let ts_query = 150;
        tree.insert(&key, value1, version1, ts1).unwrap();
        tree.insert(&key, value2, version2, ts2).unwrap();

        let (retrieved_value, retrieved_version, retrieved_ts) =
            tree.get_at_ts(&key, ts_query).unwrap();
        assert_eq!(retrieved_value, value1);
        assert_eq!(retrieved_version, version1);
        assert_eq!(retrieved_ts, ts1);
    }

    #[test]
    fn test_inserting_values_with_decreasing_timestamps() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value1 = 10;
        let value2 = 20;
        let ts1 = 200;
        let ts2 = 100;
        tree.insert(&key, value1, 1, ts1).unwrap();
        tree.insert(&key, value2, 2, ts2).unwrap();

        let (retrieved_value_early, _, _) = tree.get_at_ts(&key, ts2).unwrap();
        let (retrieved_value_late, _, _) = tree.get_at_ts(&key, ts1).unwrap();
        assert_eq!(retrieved_value_early, value2);
        assert_eq!(retrieved_value_late, value1);
    }

    #[test]
    fn test_retrieving_value_after_deleting_it() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value = 10;
        let ts_insert = 100;
        let ts_query = 150;
        tree.insert(&key, value, 1, ts_insert).unwrap();
        tree.remove(&key);

        let result = tree.get_at_ts(&key, ts_query);
        assert!(result.is_none());
    }

    #[test]
    fn test_latest_by_version() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        tree.insert_unchecked(&key, 10, 1, 100).unwrap();
        tree.insert_unchecked(&key, 20, 2, 200).unwrap();
        tree.insert_unchecked(&key, 30, 3, 300).unwrap();

        let query_type = QueryType::LatestByVersion(3);
        let result = tree.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (30, 3, 300));
        assert_eq!(tree.version(), 3);
    }

    #[test]
    fn test_latest_by_ts() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        tree.insert_unchecked(&key, 10, 1, 100).unwrap();
        tree.insert_unchecked(&key, 20, 2, 200).unwrap();
        tree.insert_unchecked(&key, 30, 3, 300).unwrap();

        let query_type = QueryType::LatestByTs(300);
        let result = tree.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (30, 3, 300));
        assert_eq!(tree.version(), 3);
    }

    #[test]
    fn test_last_less_than_ts() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        tree.insert_unchecked(&key, 10, 1, 100).unwrap();
        tree.insert_unchecked(&key, 20, 2, 150).unwrap();
        tree.insert_unchecked(&key, 30, 3, 200).unwrap();

        let query_type = QueryType::LastLessThanTs(150);
        let result = tree.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (10, 1, 100));
        assert_eq!(tree.version(), 3);
    }

    #[test]
    fn test_last_less_or_equal_ts() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        tree.insert_unchecked(&key, 10, 1, 100).unwrap();
        tree.insert_unchecked(&key, 20, 2, 150).unwrap();
        tree.insert_unchecked(&key, 30, 3, 200).unwrap();

        let query_type = QueryType::LastLessOrEqualTs(150);
        let result = tree.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (20, 2, 150));
        assert_eq!(tree.version(), 3);
    }

    #[test]
    fn test_first_greater_than_ts() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        tree.insert_unchecked(&key, 10, 1, 100).unwrap();
        tree.insert_unchecked(&key, 20, 2, 150).unwrap();
        tree.insert_unchecked(&key, 30, 3, 200).unwrap();

        let query_type = QueryType::FirstGreaterThanTs(150);
        let result = tree.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (30, 3, 200));
        assert_eq!(tree.version(), 3);
    }

    #[test]
    fn test_first_greater_or_equal_ts() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        tree.insert_unchecked(&key, 10, 1, 100).unwrap();
        tree.insert_unchecked(&key, 20, 2, 150).unwrap();
        tree.insert_unchecked(&key, 30, 3, 200).unwrap();

        let query_type = QueryType::FirstGreaterOrEqualTs(150);
        let result = tree.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (20, 2, 150));
        assert_eq!(tree.version(), 3);
    }

    #[test]
    fn test_insert_or_replace() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("key").unwrap();

        tree.insert_or_replace(&key, 1, 10, 100).unwrap();
        tree.insert_or_replace(&key, 2, 20, 200).unwrap();

        let history = tree.get_version_history(&key).unwrap();
        assert_eq!(history.len(), 1);
        assert_eq!(history[0], (2, 20, 200));
    }

    #[test]
    fn test_insert_or_replace_unchecked() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("key").unwrap();

        // Scenario 1: the second value is more recent than the first one.
        tree.insert_or_replace_unchecked(&key, 1, 10, 100).unwrap();
        tree.insert_or_replace_unchecked(&key, 2, 20, 200).unwrap();

        let history = tree.get_version_history(&key).unwrap();
        assert_eq!(history.len(), 1);
        assert_eq!(history[0], (2, 20, 200));

        // Scenario 2: the new value has the smaller version and hence
        // is older than the one already in the tree. Discard the new
        // value.
        tree.insert_or_replace_unchecked(&key, 1, 1, 1).unwrap();

        let history = tree.get_version_history(&key).unwrap();
        assert_eq!(history.len(), 1);
        assert_eq!(history[0], (2, 20, 200));
    }

    #[test]
    fn scan_empty_range() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let result: Vec<_> = tree.scan_at_ts(RangeFull {}, 0).collect();
        assert!(result.is_empty());
    }

    #[test]
    fn scan_range_includes_some_keys() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys = ["key_1", "key_2", "key_3"];
        for key in keys.iter() {
            tree.insert(&VariableSizeKey::from_str(key).unwrap(), 1, 0, 0)
                .unwrap();
        }
        let range = VariableSizeKey::from_slice("key_1".as_bytes())
            ..=VariableSizeKey::from_slice("key_2".as_bytes());
        let values: Vec<_> = tree.scan_at_ts(range, 0).collect();
        assert_eq!(values.len(), 2);
    }

    #[test]
    fn scan_range_includes_all_keys() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys = ["key_1", "key_2", "key_3"];
        for key in keys.iter() {
            tree.insert(&VariableSizeKey::from_str(key).unwrap(), 1, 0, 0)
                .unwrap();
        }
        let values: Vec<_> = tree.scan_at_ts(RangeFull {}, 0).collect();
        assert_eq!(values.len(), keys.len());
    }

    #[test]
    fn scan_range_includes_no_keys() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys = ["key_1", "key_2", "key_3"];
        for key in keys.iter() {
            tree.insert(&VariableSizeKey::from_str(key).unwrap(), 1, 0, 0)
                .unwrap();
        }
        let range = VariableSizeKey::from_slice("key_4".as_bytes())
            ..VariableSizeKey::from_slice("key_5".as_bytes());
        let values: Vec<_> = tree.scan_at_ts(range, 0).collect();
        assert!(values.is_empty());
    }

    #[test]
    fn scan_at_different_timestamps() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys = ["key_1", "key_2", "key_3"];
        for (i, key) in keys.iter().enumerate() {
            tree.insert(
                &VariableSizeKey::from_str(key).unwrap(),
                i as i32,
                0,
                i as u64,
            )
            .unwrap();
        }
        for (i, _) in keys.iter().enumerate() {
            let values: Vec<_> = tree.scan_at_ts(RangeFull {}, i as u64).collect();
            assert_eq!(values.len(), i + 1);
        }
    }

    #[test]
    fn large_number_of_inserts() {
        let mut tree: Tree<VariableSizeKey, u64> = Tree::new();
        let num_keys = 10000u64; // Large number of keys
        for i in 0..num_keys {
            let key = format!("key_{}", i);
            // Insert with increasing values and timestamps
            tree.insert(&VariableSizeKey::from_str(&key).unwrap(), i, 0, i)
                .unwrap();
        }

        let values: Vec<_> = tree.scan_at_ts(RangeFull {}, num_keys).collect();
        assert_eq!(values.len(), num_keys as usize); // Expect all keys to be visible
    }

    #[test]
    fn scan_at_various_timestamps() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys = ["key_1", "key_2", "key_3"];
        for (i, key) in keys.iter().enumerate() {
            // Insert with non-sequential timestamps to test out-of-order handling
            let timestamp = ((i + 1) * 2) as u64;
            tree.insert(
                &VariableSizeKey::from_str(key).unwrap(),
                i as i32,
                0,
                timestamp,
            )
            .unwrap();
        }

        // Scan at a timestamp before any insertions
        let result_before: Vec<_> = tree.scan_at_ts(RangeFull {}, 0).collect();
        assert!(result_before.is_empty());

        // Scan between insertions
        let result_mid: Vec<_> = tree.scan_at_ts(RangeFull {}, 4).collect();
        assert_eq!(result_mid.len(), 2); // Expect first two keys to be visible

        // Scan after all insertions
        let result_after: Vec<_> = tree.scan_at_ts(RangeFull {}, 7).collect();
        assert_eq!(result_after.len(), keys.len()); // Expect all keys to be visible
    }

    #[test]
    fn scan_with_single_item() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        // Insert a single item into the tree
        tree.insert(&VariableSizeKey::from_str("key_1").unwrap(), 42, 0, 0)
            .unwrap();

        let values: Vec<_> = tree.scan_at_ts(RangeFull {}, 0).collect();
        assert_eq!(values.len(), 1);
        assert_eq!(values[0].1, 42);
    }

    #[test]
    fn keys_at_empty_range() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys: Vec<_> = tree.keys_at_ts(RangeFull {}, 0).collect();
        assert!(keys.is_empty());
    }

    #[test]
    fn keys_at_range_includes_some_keys() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys_to_insert = ["key_1", "key_2", "key_3"];
        for key in keys_to_insert.iter() {
            tree.insert(&VariableSizeKey::from_str(key).unwrap(), 1, 0, 0)
                .unwrap();
        }
        let range = VariableSizeKey::from_slice("key_1".as_bytes())
            ..=VariableSizeKey::from_slice("key_2".as_bytes());
        let keys: Vec<_> = tree.keys_at_ts(range, 0).collect();
        assert_eq!(keys.len(), 2);
    }

    #[test]
    fn keys_at_range_includes_all_keys() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys_to_insert = ["key_1", "key_2", "key_3"];
        for key in keys_to_insert.iter() {
            tree.insert(&VariableSizeKey::from_str(key).unwrap(), 1, 0, 0)
                .unwrap();
        }
        let keys: Vec<_> = tree.keys_at_ts(RangeFull {}, 0).collect();
        assert_eq!(keys.len(), keys_to_insert.len());
    }

    #[test]
    fn keys_at_range_includes_no_keys() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys_to_insert = ["key_1", "key_2", "key_3"];
        for key in keys_to_insert.iter() {
            tree.insert(&VariableSizeKey::from_str(key).unwrap(), 1, 0, 0)
                .unwrap();
        }
        let range = VariableSizeKey::from("key_4".as_bytes().to_vec())
            ..VariableSizeKey::from("key_5".as_bytes().to_vec());
        let keys: Vec<_> = tree.keys_at_ts(range, 0).collect();
        assert!(keys.is_empty());
    }

    #[test]
    fn keys_at_different_timestamps() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys_to_insert = ["key_1", "key_2", "key_3"];
        for (i, key) in keys_to_insert.iter().enumerate() {
            tree.insert(
                &VariableSizeKey::from_str(key).unwrap(),
                i as i32,
                0,
                i as u64,
            )
            .unwrap();
        }
        for (i, _) in keys_to_insert.iter().enumerate() {
            let keys: Vec<_> = tree.keys_at_ts(RangeFull {}, i as u64).collect();
            assert_eq!(keys.len(), i + 1);
        }
    }

    #[test]
    fn keys_at_large_number_of_inserts() {
        let mut tree: Tree<VariableSizeKey, u64> = Tree::new();
        let num_keys = 10000u64; // Large number of keys
        let mut expected_keys = Vec::new();
        for i in 0..num_keys {
            let key = format!("key_{}", i);
            expected_keys.push(VariableSizeKey::from_str(&key).unwrap());
            tree.insert(&VariableSizeKey::from_str(&key).unwrap(), i, 0, i)
                .unwrap();
        }

        let keys: Vec<_> = tree.keys_at_ts(RangeFull {}, num_keys).collect();
        assert_eq!(keys.len(), num_keys as usize); // Expect all keys to be visible

        // Sort the expected keys lexicographically
        expected_keys.sort();

        // Verify each key is proper
        for (expected_key, key) in expected_keys.iter().zip(keys.iter()) {
            assert_eq!(key.as_ref(), expected_key.to_slice());
        }
    }

    #[test]
    fn keys_at_various_timestamps() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys_to_insert = ["key_1", "key_2", "key_3"];
        for (i, key) in keys_to_insert.iter().enumerate() {
            let timestamp = ((i + 1) * 2) as u64;
            tree.insert(
                &VariableSizeKey::from_str(key).unwrap(),
                i as i32,
                0,
                timestamp,
            )
            .unwrap();
        }

        let keys_before: Vec<_> = tree.keys_at_ts(RangeFull {}, 0).collect();
        assert!(keys_before.is_empty());

        let keys_mid: Vec<_> = tree.keys_at_ts(RangeFull {}, 4).collect();
        assert_eq!(keys_mid.len(), 2); // Expect first two keys to be visible

        let keys_after: Vec<_> = tree.keys_at_ts(RangeFull {}, 7).collect();
        assert_eq!(keys_after.len(), keys_to_insert.len()); // Expect all keys to be visible
    }

    #[test]
    fn keys_at_with_single_item_in_snapshot() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        tree.insert(&VariableSizeKey::from_str("key_1").unwrap(), 42, 0, 0)
            .unwrap();

        let keys: Vec<_> = tree.keys_at_ts(RangeFull {}, 0).collect();
        assert_eq!(keys.len(), 1);
    }

    #[test]
    fn snapshot_isolation() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let key_1 = VariableSizeKey::from_str("key_1").unwrap();
        let key_2 = VariableSizeKey::from_str("key_2").unwrap();
        let key_3_snap1 = VariableSizeKey::from_str("key_3_snap1").unwrap();
        let key_3_snap2 = VariableSizeKey::from_str("key_3_snap2").unwrap();

        assert!(tree.insert(&key_1, 1, 0, 0).is_ok());

        // Keys inserted before snapshot creation should be visible
        let mut snap1 = tree.clone();
        assert_eq!(snap1.get(&key_1, 0).unwrap(), (1, 1, 0));

        let mut snap2 = tree.clone();
        assert_eq!(snap2.get(&key_1, 0).unwrap(), (1, 1, 0));

        // Keys inserted after snapshot creation should not be visible to other snapshots
        assert!(tree.insert(&key_2, 1, 0, 0).is_ok());
        assert!(snap1.get(&key_2, 0).is_none());
        assert!(snap2.get(&key_2, 0).is_none());

        // Keys inserted after snapshot creation should be visible to the snapshot that inserted them
        snap1.insert(&key_3_snap1, 2, 0, 0).unwrap();
        assert_eq!(snap1.get(&key_3_snap1, 0).unwrap(), (2, 2, 0));

        snap2.insert(&key_3_snap2, 3, 0, 0).unwrap();
        assert_eq!(snap2.get(&key_3_snap2, 0).unwrap(), (3, 2, 0));

        // Keys inserted after snapshot creation should not be visible to other snapshots
        assert!(snap1.get(&key_3_snap2, 0).is_none());
        assert!(snap2.get(&key_3_snap1, 0).is_none());
    }

    #[test]
    fn insert_with_prefix_match() {
        let key1 = VariableSizeKey::from_slice(b"key1");
        let key17 = VariableSizeKey::from_slice(b"key17");

        // Ascending order
        {
            let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
            tree.insert(&key1, 1, 1, 1).unwrap();
            tree.insert(&key17, 17, 17, 17).unwrap();

            assert_eq!(tree.get(&key1, 1).unwrap(), (1, 1, 1));
            assert_eq!(tree.get(&key17, 17).unwrap(), (17, 17, 17));

            assert!(tree.remove(&key1));
            assert!(tree.remove(&key17));
        }

        // Descending order
        {
            let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
            tree.insert(&key17, 17, 1, 1).unwrap();
            tree.insert(&key1, 1, 2, 2).unwrap();

            assert_eq!(tree.get(&key17, 1).unwrap(), (17, 1, 1));
            assert_eq!(tree.get(&key1, 2).unwrap(), (1, 2, 2));

            assert!(tree.remove(&key17));
            assert!(tree.remove(&key1));
        }
    }

    #[test]
    fn insert_mut_with_prefix_match() {
        let key1 = VariableSizeKey::from_slice(b"key1");
        let key17 = VariableSizeKey::from_slice(b"key17");

        // Ascending order
        {
            let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
            tree.insert_unchecked(&key1, 1, 1, 1).unwrap();
            tree.insert_unchecked(&key17, 17, 17, 17).unwrap();

            assert_eq!(tree.get(&key1, 1).unwrap(), (1, 1, 1));
            assert_eq!(tree.get(&key17, 17).unwrap(), (17, 17, 17));

            assert!(tree.remove(&key1));
            assert!(tree.remove(&key17));
        }

        // Descending order
        {
            let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
            tree.insert_unchecked(&key17, 17, 1, 1).unwrap();
            tree.insert_unchecked(&key1, 1, 2, 2).unwrap();

            assert_eq!(tree.get(&key17, 1).unwrap(), (17, 1, 1));
            assert_eq!(tree.get(&key1, 2).unwrap(), (1, 2, 2));

            assert!(tree.remove(&key17));
            assert!(tree.remove(&key1));
        }
    }
}
