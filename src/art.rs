use core::panic;
use std::cmp::min;
use std::ops::RangeBounds;
use std::sync::Arc;

use crate::iter::{Iter, Range, VersionedIter};
use crate::node::{FlatNode, LeafValue, Node256, Node48, NodeTrait, TwigNode, Version};
use crate::snapshot::Snapshot;
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
pub struct Node<P: KeyTrait, V: Clone> {
    pub(crate) node_type: NodeType<P, V>, // Type of the node
}

impl<P: KeyTrait, V: Clone> Version for Node<P, V> {
    fn version(&self) -> u64 {
        match &self.node_type {
            NodeType::Twig(twig) => twig.version(),
            NodeType::Node1(n) => n.version(),
            NodeType::Node4(n) => n.version(),
            NodeType::Node16(n) => n.version(),
            NodeType::Node48(n) => n.version(),
            NodeType::Node256(n) => n.version(),
        }
    }
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
    Node1(FlatNode<P, Node<P, V>, 1>), // Node with 1 key and 1 children
    Node4(FlatNode<P, Node<P, V>, 4>), // Node with 4 keys and 4 children
    Node16(FlatNode<P, Node<P, V>, 16>), // Node with 16 keys and 16 children
    Node48(Node48<P, Node<P, V>>),     // Node with 256 keys and 48 children
    Node256(Node256<P, Node<P, V>>),   // Node with 256 keys and 256 children
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
            NodeType::Node1(n) => n.num_children() >= n.size(),
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
        let mut cloned_node = match &self.node_type {
            NodeType::Node1(n) => Self {
                node_type: NodeType::Node1(n.clone()),
            },
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
        };

        if cloned_node.is_full() {
            cloned_node.grow();
        }

        match &cloned_node.node_type {
            NodeType::Node1(n) => {
                // Add the child node to the Node1 instance.
                let node = NodeType::Node1(n.add_child(key, child));

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
            }
            NodeType::Node4(n) => {
                // Add the child node to the Node4 instance.
                let node = NodeType::Node4(n.add_child(key, child));

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
            }
            NodeType::Node16(n) => {
                // Add the child node to the Node16 instance.
                let node = NodeType::Node16(n.add_child(key, child));

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
            }
            NodeType::Node48(n) => {
                // Add the child node to the Node48 instance.
                let node = NodeType::Node48(n.add_child(key, child));

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
            }
            NodeType::Node256(n) => {
                // Add the child node to the Node256 instance.
                let node = NodeType::Node256(n.add_child(key, child));

                // Create a new Node instance with the updated NodeType.
                Self { node_type: node }
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
    fn grow(&mut self) {
        match &mut self.node_type {
            NodeType::Node1(n) => {
                // Grow a Node4 to a Node16 by resizing.
                let n4 = NodeType::Node4(n.resize());
                self.node_type = n4;
            }
            NodeType::Node4(n) => {
                // Grow a Node4 to a Node16 by resizing.
                let n16 = NodeType::Node16(n.resize());
                self.node_type = n16;
            }
            NodeType::Node16(n) => {
                // Grow a Node16 to a Node48 by performing growth.
                let n48 = NodeType::Node48(n.grow());
                self.node_type = n48;
            }
            NodeType::Node48(n) => {
                // Grow a Node48 to a Node256 by performing growth.
                let n256 = NodeType::Node256(n.grow());
                self.node_type = n256;
            }
            NodeType::Node256 { .. } => {
                panic!("Node256 cannot be grown further");
            }
            NodeType::Twig(_) => panic!("Unexpected Twig node encountered in grow()"),
        }
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
            NodeType::Node1(n) => n.find_child(key),
            NodeType::Node4(n) => n.find_child(key),
            NodeType::Node16(n) => n.find_child(key),
            NodeType::Node48(n) => n.find_child(key),
            NodeType::Node256(n) => n.find_child(key),
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
            NodeType::Node1(n) => {
                // Replace the child node in the Node4 instance and update the NodeType.
                let node = NodeType::Node1(n.replace_child(key, node));
                Self { node_type: node }
            }
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
            NodeType::Node1(n) => {
                // Delete the child node from the Node1 instance and update the NodeType.
                let node = NodeType::Node1(n.delete_child(key));

                Self { node_type: node }
            }
            NodeType::Node4(n) => {
                // Delete the child node from the Node4 instance and update the NodeType.
                let node = NodeType::Node4(n.delete_child(key));
                let mut new_node = Self { node_type: node };

                // Check if the number of remaining children is below the threshold.
                if new_node.num_children() < NODE4MIN {
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
            NodeType::Node1(n) => &n.prefix,
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
        match &mut self.node_type {
            NodeType::Node1(n) => n.prefix = prefix,
            NodeType::Node4(n) => n.prefix = prefix,
            NodeType::Node16(n) => n.prefix = prefix,
            NodeType::Node48(n) => n.prefix = prefix,
            NodeType::Node256(n) => n.prefix = prefix,
            NodeType::Twig(n) => n.prefix = prefix,
        }
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
            NodeType::Node1(n) => {
                // Shrink Node1 to Node1 by resizing it.
                self.node_type = NodeType::Node1(n.resize());
            }
            NodeType::Node4(n) => {
                // Shrink Node4 to Node1 by resizing it.
                self.node_type = NodeType::Node1(n.resize());
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

    #[inline]
    pub fn num_children(&self) -> usize {
        match &self.node_type {
            NodeType::Node1(n) => n.num_children(),
            NodeType::Node4(n) => n.num_children(),
            NodeType::Node16(n) => n.num_children(),
            NodeType::Node48(n) => n.num_children(),
            NodeType::Node256(n) => n.num_children(),
            NodeType::Twig(_) => 0,
        }
    }

    #[inline]
    pub(crate) fn get_leaf_by_query(&self, query_type: QueryType) -> Option<Arc<LeafValue<V>>> {
        // Unwrap the NodeType::Twig to access the TwigNode instance.
        let NodeType::Twig(twig) = &self.node_type else {
            return None;
        };

        twig.get_leaf_by_query(query_type)
    }

    #[inline]
    pub fn get_all_versions(&self) -> Option<Vec<(V, u64, u64)>> {
        // Unwrap the NodeType::Twig to access the TwigNode instance.
        let NodeType::Twig(twig) = &self.node_type else {
            return None;
        };

        // Get the value from the TwigNode instance by the specified version.
        let val = twig.get_all_versions();

        // Return the retrieved key, value, and version as a tuple.
        Some(val)
    }

    pub fn node_type_name(&self) -> String {
        match &self.node_type {
            NodeType::Node1(_) => "Node1".to_string(),
            NodeType::Node4(_) => "Node4".to_string(),
            NodeType::Node16(_) => "Node16".to_string(),
            NodeType::Node48(_) => "Node48".to_string(),
            NodeType::Node256(_) => "Node256".to_string(),
            NodeType::Twig(_) => "twig".to_string(),
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

    /// Inserts a key-value pair recursively into the node.
    ///
    /// Recursively inserts a key-value pair into the current node and its child nodes.
    ///
    /// # Parameters
    ///
    /// - `cur_node`: A reference to the current node.
    /// - `key`: The key to be inserted.
    /// - `value`: The value associated with the key.
    /// - `commit_version`: The version when the value was inserted.
    /// - `depth`: The depth of the insertion process.
    ///
    /// # Returns
    ///
    /// Returns the updated node and the old value (if any) for the given key.
    ///
    pub(crate) fn insert_recurse(
        cur_node: &Arc<Node<P, V>>,
        key: &P,
        value: V,
        commit_version: u64,
        ts: u64,
        depth: usize,
    ) -> Result<(NodeArc<P, V>, Option<V>), TrieError> {
        // Obtain the current node's prefix and its length.
        let cur_node_prefix = cur_node.prefix().clone();
        let cur_node_prefix_len = cur_node.prefix().len();

        // Determine the prefix of the key after the current depth.
        let key_prefix = key.prefix_after(depth);
        let key_prefix = key_prefix.as_slice();
        // Find the longest common prefix between the current node's prefix and the key's prefix.
        let longest_common_prefix = cur_node_prefix.longest_common_prefix(key_prefix);

        // Create a new key that represents the remaining part of the current node's prefix after the common prefix.
        let new_key = cur_node_prefix.prefix_after(longest_common_prefix);
        // Extract the prefix of the current node up to the common prefix.
        let prefix = cur_node_prefix.prefix_before(longest_common_prefix);
        // Determine whether the current node's prefix and the key's prefix match up to the common prefix.
        let is_prefix_match = min(cur_node_prefix_len, key_prefix.len()) == longest_common_prefix;

        // If the current node is a Twig node and the prefixes match up to the end of both prefixes,
        // update the existing value in the Twig node.
        if let NodeType::Twig(ref twig) = &cur_node.node_type {
            if is_prefix_match && cur_node_prefix.len() == key_prefix.len() {
                let new_twig = twig.insert(value, commit_version, ts);
                if let Some(old_val) = twig.get_leaf_by_version(commit_version) {
                    return Ok((
                        Arc::new(Node {
                            node_type: NodeType::Twig(new_twig),
                        }),
                        Some(old_val.value.clone()),
                    ));
                } else {
                    return Ok((
                        Arc::new(Node {
                            node_type: NodeType::Twig(new_twig),
                        }),
                        None,
                    ));
                }
            }
        }

        // If the prefixes don't match, create a new Node4 with the old node and a new Twig as children.
        if !is_prefix_match {
            let mut old_node = cur_node.clone_node();
            old_node.set_prefix(new_key);
            let mut n4 = Node::new_node4(prefix);

            let k1 = cur_node_prefix.at(longest_common_prefix);
            let k2 = key_prefix[longest_common_prefix];
            let new_twig = Node::new_twig(
                key_prefix[longest_common_prefix..].into(),
                key.as_slice().into(),
                value,
                commit_version,
                ts,
            );
            n4 = n4.add_child(k1, old_node).add_child(k2, new_twig);
            return Ok((Arc::new(n4), None));
        }

        // Continue the insertion process by finding or creating the appropriate child node for the next character.
        let k = key_prefix[longest_common_prefix];
        let child_for_key = cur_node.find_child(k);
        if let Some(child) = child_for_key {
            match Node::insert_recurse(
                child,
                key,
                value,
                commit_version,
                ts,
                depth + longest_common_prefix,
            ) {
                Ok((new_child, old_value)) => {
                    let new_node = cur_node.replace_child(k, new_child);
                    return Ok((Arc::new(new_node), old_value));
                }
                Err(err) => {
                    return Err(err);
                }
            }
        };

        // If no child exists for the key's character, create a new Twig node and add it as a child.
        let new_twig = Node::new_twig(
            key_prefix[longest_common_prefix..].into(),
            key.as_slice().into(),
            value,
            commit_version,
            ts,
        );
        let new_node = cur_node.add_child(k, new_twig);
        Ok((Arc::new(new_node), None))
    }

    /// Removes a key recursively from the node and its children.
    ///
    /// Recursively removes a key from the current node and its child nodes.
    ///
    /// # Parameters
    ///
    /// - `cur_node`: A reference to the current node.
    /// - `key`: The key to be removed.
    /// - `depth`: The depth of the removal process.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing the updated node (or `None`) and a flag indicating if the key was removed.
    ///
    pub(crate) fn remove_recurse(
        cur_node: &Arc<Node<P, V>>,
        key: &P,
        depth: usize,
    ) -> (Option<Arc<Node<P, V>>>, bool) {
        let k = key.at(depth);

        // Search for a child node corresponding to the key's character.
        let child = cur_node.find_child(k);
        if let Some(child_node) = child {
            let prefix = child_node.prefix().clone();

            // Determine the prefix of the key after the current depth.
            let key_prefix = key.prefix_after(depth);
            let key_prefix = key_prefix.as_slice();

            // Find the longest common prefix between the current node's prefix and the key's prefix.
            let longest_common_prefix = prefix.longest_common_prefix(key_prefix);
            if longest_common_prefix != prefix.len() {
                return (None, false);
            }

            if child_node.is_twig() {
                let prefix_len = key.len() - depth;
                if child_node.prefix().len() != prefix_len {
                    return (None, false);
                }

                let new_node = cur_node.delete_child(k);
                return (Some(Arc::new(new_node)), true);
            }

            // Recursively attempt to remove the key from the child node.
            let (new_child, removed) =
                Node::remove_recurse(child_node, key, depth + longest_common_prefix);
            if removed {
                // If the key was successfully removed from the child node, update the current node's child pointer.
                let new_node = cur_node.replace_child(k, new_child.unwrap());
                return (Some(Arc::new(new_node)), true);
            }
        }

        // If the key was not found at this level, return the current node as-is.
        (Some(cur_node.clone()), false)
    }

    fn navigate_to_node<'a>(
        cur_node: &'a Node<P, V>,
        key: &P,
    ) -> Result<&'a Node<P, V>, TrieError> {
        let mut cur_node = cur_node;
        let mut depth = 0;

        loop {
            let key_prefix = key.prefix_after(depth);
            let key_prefix = key_prefix.as_slice();
            let prefix = cur_node.prefix();
            let lcp = prefix.longest_common_prefix(key_prefix);

            if lcp != prefix.len() {
                return Err(TrieError::KeyNotFound);
            }

            if prefix.len() == key_prefix.len() {
                return Ok(cur_node);
            }

            let k = key.at(depth + prefix.len());
            depth += prefix.len();

            match cur_node.find_child(k) {
                Some(child) => cur_node = child,
                None => return Err(TrieError::KeyNotFound),
            }
        }
    }

    /// Recursively searches for a key in the node and its children.
    ///
    /// Recursively searches for a key in the current node and its child nodes, considering versions.
    pub(crate) fn get_recurse(
        cur_node: &Node<P, V>,
        key: &P,
        query_type: QueryType,
    ) -> Result<(V, u64, u64), TrieError> {
        let cur_node = Self::navigate_to_node(cur_node, key)?;
        let val = cur_node
            .get_leaf_by_query(query_type)
            .ok_or(TrieError::KeyNotFound)?;
        Ok((val.value.clone(), val.version, val.ts))
    }

    pub fn get_version_history(
        cur_node: &Node<P, V>,
        key: &P,
    ) -> Result<Vec<(V, u64, u64)>, TrieError> {
        let cur_node = Self::navigate_to_node(cur_node, key)?;
        cur_node.get_all_versions().ok_or(TrieError::KeyNotFound)
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
    #[allow(dead_code)]
    pub fn iter(&self) -> Box<dyn Iterator<Item = (u8, &Arc<Self>)> + '_> {
        match &self.node_type {
            NodeType::Node1(n) => Box::new(n.iter()),
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
    /// A flag indicating whether the tree is closed.
    pub(crate) closed: bool,
}

pub struct KV<P, V> {
    pub key: P,
    pub value: V,
    pub version: u64,
    pub ts: u64,
}

// A type alias for a node reference.
type NodeArc<P, V> = Arc<Node<P, V>>;

impl<P: KeyTrait, V: Clone> KV<P, V> {
    pub fn new(key: P, value: V, version: u64, timestamp: u64) -> Self {
        KV {
            key,
            value,
            version,
            ts: timestamp,
        }
    }
}

impl<P: KeyTrait, V: Clone> NodeType<P, V> {
    fn clone(&self) -> Self {
        match self {
            // twig value not actually cloned
            NodeType::Twig(twig) => NodeType::Twig(twig.clone()),
            NodeType::Node1(n) => NodeType::Node1(n.clone()),
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

impl<P: KeyTrait, V: Clone> Tree<P, V> {
    pub fn new() -> Self {
        Tree {
            root: None,
            closed: false,
        }
    }

    fn insert_common(
        &mut self,
        key: &P,
        value: V,
        version: u64,
        ts: u64,
        check_version: bool,
    ) -> Result<Option<V>, TrieError> {
        self.check_if_closed()?;

        let (new_root, old_node) = match &self.root {
            None => {
                let commit_version = if version == 0 { 1 } else { version };
                (
                    Arc::new(Node::new_twig(
                        key.as_slice().into(),
                        key.as_slice().into(),
                        value,
                        commit_version,
                        ts,
                    )),
                    None,
                )
            }
            Some(root) => {
                let curr_version = root.version();
                let mut commit_version = version;
                if version == 0 {
                    commit_version = curr_version + 1;
                } else if check_version && curr_version >= version {
                    return Err(TrieError::Other(
                        "given version is older than root's current version".to_string(),
                    ));
                }
                Node::insert_recurse(root, key, value, commit_version, ts, 0)?
            }
        };

        self.root = Some(new_root);
        Ok(old_node)
    }

    /// Inserts a new key-value pair with the specified version into the Trie.
    ///
    /// This function inserts a new key-value pair into the Trie. If the key already exists,
    /// the previous value associated with the key is returned. The version `ts` is used to
    /// ensure proper ordering of values for versioning.
    ///
    /// # Arguments
    ///
    /// * `key`: A reference to the key to be inserted.
    /// * `value`: The value to be associated with the key.
    /// * `ts`: The version for the insertion, used for versioning.
    ///
    /// # Returns
    ///
    /// Returns `Ok(None)` if the key did not exist previously. If the key already existed,
    /// `Ok(Some(old_value))` is returned, where `old_value` is the previous value associated with the key.
    ///
    /// # Errors
    ///
    /// Returns an error if the given version is older than the root's current version.
    ///
    pub fn insert(
        &mut self,
        key: &P,
        value: V,
        version: u64,
        ts: u64,
    ) -> Result<Option<V>, TrieError> {
        self.insert_common(key, value, version, ts, true)
    }

    pub fn insert_unchecked(
        &mut self,
        key: &P,
        value: V,
        version: u64,
        ts: u64,
    ) -> Result<Option<V>, TrieError> {
        self.insert_common(key, value, version, ts, false)
    }

    pub fn bulk_insert(
        &mut self,
        kv_pairs: &[KV<P, V>],
        check_version: bool,
    ) -> Result<(), TrieError> {
        // Check if the tree is already closed
        self.check_if_closed()?;

        let curr_version = self.version();
        let mut new_version = 0;

        for kv in kv_pairs {
            let k = kv.key.clone(); // Clone the key
            let v = kv.value.clone(); // Clone the value
            let mut t = kv.version;

            if t == 0 {
                // Zero-valued timestamps are associated with current time plus one
                t = curr_version + 1;
            } else if check_version && (curr_version >= kv.version) {
                return Err(TrieError::Other(
                    "given version is older than root's current version".to_string(),
                ));
            }

            // Create a new KV instance
            let new_kv = KV {
                key: k,
                value: v,
                version: t,
                ts: kv.ts,
            };

            // Insert the new KV instance using the insert function
            match &self.root {
                None => {
                    self.root = Some(Arc::new(Node::new_twig(
                        new_kv.key.as_slice().into(),
                        new_kv.key.as_slice().into(),
                        new_kv.value,
                        new_kv.version,
                        new_kv.ts,
                    )))
                }
                Some(root) => {
                    match Node::insert_recurse(
                        root,
                        &new_kv.key,
                        new_kv.value,
                        new_kv.version,
                        new_kv.ts,
                        0,
                    ) {
                        Ok((new_node, _)) => {
                            self.root = Some(new_node);
                        }
                        Err(err) => {
                            return Err(err);
                        }
                    }
                }
            }

            // Update new_version if necessary
            if t > new_version {
                new_version = t;
            }
        }

        Ok(())
    }

    pub(crate) fn remove_from_node(
        node: Option<&Arc<Node<P, V>>>,
        key: &P,
    ) -> (Option<Arc<Node<P, V>>>, bool) {
        // Directly match on the root to simplify logic
        let (new_root, is_deleted) = match &node {
            Some(root) if !root.is_twig() => {
                // Determine the prefix of the key after the current depth.
                let prefix_after = key.prefix_after(0);
                let key_prefix = prefix_after.as_slice(); // Find the longest common prefix between the current node's prefix and the key's prefix.
                let longest_common_prefix = root.prefix().longest_common_prefix(key_prefix);

                if longest_common_prefix != root.prefix().len() {
                    // If the longest common prefix doesn't match the root's prefix length, no deletion occurs.
                    (Some(Arc::clone(root)), false)
                } else {
                    // Proceed with recursive removal if the prefixes match.
                    let (new_root, removed) =
                        Node::remove_recurse(root, key, longest_common_prefix);

                    if removed && new_root.as_ref().unwrap().num_children() == 0 {
                        // If the node was deleted and it has no children, return None as the new root.
                        (None, removed)
                    } else {
                        (new_root, removed)
                    }
                }
            }
            Some(root) => {
                // case where the root is a twig.
                // Determine the prefix of the key after the current depth.
                let prefix_after = key.prefix_after(0);
                let key_prefix = prefix_after.as_slice(); // Find the longest common prefix between the current node's prefix and the key's prefix.
                let longest_common_prefix = root.prefix().longest_common_prefix(key_prefix);

                if longest_common_prefix != root.prefix().len() {
                    (None, false)
                } else {
                    (None, true)
                }
            }
            None => (None, false), // case where there is no root.
        };

        (new_root, is_deleted)
    }

    pub fn remove(&mut self, key: &P) -> Result<bool, TrieError> {
        // Check if the tree is already closed
        self.check_if_closed()?;

        // Directly match on the root to simplify logic
        let (new_root, is_deleted) = Tree::remove_from_node(self.root.as_ref(), key);

        // Update the root and return the deletion status.
        if is_deleted {
            self.root = new_root;
        }
        Ok(is_deleted)
    }

    pub fn get(&self, key: &P, version: u64) -> Result<(V, u64, u64), TrieError> {
        // Check if the tree is already closed
        self.check_if_closed()?;

        if self.root.is_none() {
            return Err(TrieError::Other("cannot read from empty tree".to_string()));
        }

        let root = self.root.as_ref().unwrap();
        let mut commit_version = version;
        if commit_version == 0 {
            commit_version = root.version();
        }

        Node::get_recurse(root, key, QueryType::LatestByVersion(commit_version))
    }

    /// Retrieves the latest version of the Trie.
    ///
    /// This function returns the version of the latest version of the Trie. If the Trie is empty,
    /// it returns `0`.
    ///
    /// # Returns
    ///
    /// Returns the version of the latest version of the Trie, or `0` if the Trie is empty.
    ///
    pub fn version(&self) -> u64 {
        match &self.root {
            None => 0,
            Some(root) => root.version(),
        }
    }

    /// Creates a new snapshot of the Trie.
    ///
    /// This function creates a snapshot of the current state of the Trie. If successful, it returns
    /// a `Snapshot` that can be used to interact with the newly created snapshot.
    ///
    /// # Returns
    ///
    /// Returns a `Result` containing the `Snapshot` if the snapshot is created successfully,
    /// or an `Err` with an appropriate error message if creation fails.
    ///
    pub fn create_snapshot(&self) -> Result<Snapshot<P, V>, TrieError> {
        // Check if the tree is already closed
        self.check_if_closed()?;

        let root = self.root.as_ref().cloned();
        let version = self.root.as_ref().map_or(1, |root| root.version() + 1);
        let new_snapshot = Snapshot::new(root, version);

        Ok(new_snapshot)
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
        Iter::new(self.root.as_ref())
    }

    /// Creates a versioned iterator over the Trie's key-value pairs.
    ///
    /// This function creates and returns an iterator that can be used to traverse all the versions
    /// for all the key-value pairs stored in the Trie. The iterator starts from the root of the Trie.
    pub fn iter_with_versions(&self) -> VersionedIter<P, V> {
        VersionedIter::new(self.root.as_ref())
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
    ) -> impl Iterator<Item = (Vec<u8>, &'a V, &'a u64, &'a u64)>
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

    pub fn range_with_versions<'a, R>(
        &'a self,
        range: R,
    ) -> impl Iterator<Item = (Vec<u8>, &'a V, &'a u64, &'a u64)>
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

    fn check_if_closed(&self) -> Result<(), TrieError> {
        if self.closed {
            return Err(TrieError::TreeAlreadyClosed);
        }
        Ok(())
    }

    /// Closes the tree, preventing further modifications, and releases associated resources.
    pub fn close(&mut self) -> Result<(), TrieError> {
        // Check if the tree is already closed
        self.check_if_closed()?;

        self.closed = true;

        Ok(())
    }

    pub fn get_at_ts(&self, key: &P, ts: u64) -> Result<(V, u64, u64), TrieError> {
        // Check if the tree is already closed
        self.check_if_closed()?;

        if self.root.is_none() {
            return Err(TrieError::Other("cannot read from empty tree".to_string()));
        }

        let root = self.root.as_ref().unwrap();
        Node::get_recurse(root, key, QueryType::LatestByTs(ts))
    }

    pub fn get_version_history(&self, key: &P) -> Result<Vec<(V, u64, u64)>, TrieError> {
        // Check if the tree is already closed
        self.check_if_closed()?;

        if self.root.is_none() {
            return Err(TrieError::Other("cannot read from empty tree".to_string()));
        }

        match self.root.as_ref() {
            Some(root) => {
                // Directly return the Result from Node::get_all_versions
                Node::get_version_history(root, key)
            }
            None => Err(TrieError::KeyNotFound),
        }
    }

    pub fn get_value_by_query(
        &self,
        key: &P,
        query_type: QueryType,
    ) -> Result<(V, u64, u64), TrieError> {
        // Check if the tree is already closed
        self.check_if_closed()?;

        if self.root.is_none() {
            return Err(TrieError::Other("cannot read from empty tree".to_string()));
        }

        let root = self.root.as_ref().unwrap();
        Node::get_recurse(root, key, query_type)
    }
}

/*
    Test cases for Adaptive Radix Tree
*/

#[cfg(test)]
mod tests {
    use super::{Tree, KV};
    use crate::art::QueryType;
    use crate::{FixedSizeKey, VariableSizeKey};
    use rand::{thread_rng, Rng};
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
                assert!(tree.remove(&key).unwrap());
            }
        } else if let Err(err) = read_words_from_file(file_path) {
            eprintln!("Error reading file: {}", err);
        }

        assert_eq!(tree.version(), 0);
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
            assert!(tree
                .remove(&VariableSizeKey::from_str(word).unwrap())
                .unwrap());
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
        let result = tree.insert(&key, value, 0, 0).expect("Failed to insert");
        assert!(result.is_none());

        // Second insertion (duplicate)
        let result = tree.insert(&key, value, 0, 0).expect("Failed to insert");
        assert!(result.is_some());
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
        assert!(tree.remove(&key).unwrap());

        // Verification
        assert!(tree.get(&key, 0).is_err());
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
        assert!(tree.remove(&key1).unwrap());

        // Root verification
        if let Some(root) = &tree.root {
            assert_eq!(root.node_type_name(), "Node1");
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
        assert!(tree.remove(&key1).unwrap());

        // Root verification
        if let Some(root) = &tree.root {
            assert_eq!(root.node_type_name(), "Node1");
        } else {
            panic!("Tree root is None");
        }
    }

    // // Inserting Two values into a tree and deleting them both
    // // should result in a nil tree root
    // // This tests the expansion of the root into a NODE4 and
    // // successfully collapsing into a twig and then nil upon successive removals
    // #[test]
    // fn insert2_and_remove2_and_root_should_be_nil() {
    //     let key1 = &VariableSizeKey::from_str("test1");
    //     let key2 = &VariableSizeKey::from_str("test2");

    //     let mut tree = Tree::<VariableSizeKey, i32>::new();
    //     tree.insert(key1, 1, 0, 0);
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
    fn insert5_and_remove1_and_root_should_be_node4() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insertion
        for i in 0..5u32 {
            let key = VariableSizeKey::from_slice(&i.to_be_bytes());
            tree.insert(&key, 1, 0, 0).unwrap();
        }

        // Removal
        let key_to_remove = VariableSizeKey::from_slice(&1u32.to_be_bytes());
        assert!(tree.remove(&key_to_remove).unwrap());

        // Root verification
        if let Some(root) = &tree.root {
            assert!(root.is_inner());
            assert_eq!(root.node_type_name(), "Node4");
        } else {
            panic!("Tree root is None");
        }
    }

    //     // Inserting Five values into a tree and deleting all of them
    //     // should result in a tree root of type nil
    //     // This tests the expansion of the root into a NODE16 and
    //     // successfully collapsing into a NODE4, twig, then nil
    //     #[test]
    //     fn insert5_and_remove5_and_root_should_be_nil() {
    //         let mut tree = Tree::<VariableSizeKey, i32>::new();

    //         for i in 0..5u32 {
    //             let key = &VariableSizeKey::from_slice(&i.to_be_bytes());
    //             tree.insert(key, 1);
    //         }

    //         for i in 0..5u32 {
    //             let key = &VariableSizeKey::from_slice(&i.to_be_bytes());
    //             tree.remove(key);
    //         }

    //         assert!(tree.root.is_none());
    //     }

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
        assert!(tree.remove(&key_to_remove).unwrap());

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

    // // Inserting 17 values into a tree and removing them all should
    // // result in a tree of root type nil
    // // This tests the expansion of the root into a NODE48, and
    // // successfully collapsing into a NODE16, NODE4, twig, and then nil
    // #[test]
    // fn insert17_and_remove17_and_root_should_be_nil() {
    //     let mut tree = Tree::<VariableSizeKey, i32>::new();

    //     for i in 0..17u32 {
    //         let key = VariableSizeKey::from_slice(&i.to_be_bytes());
    //         tree.insert(&key, 1);
    //     }

    //     for i in 0..17u32 {
    //         let key = VariableSizeKey::from_slice(&i.to_be_bytes());
    //         tree.remove(&key);
    //     }

    //     assert!(tree.root.is_none());
    // }

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
        assert!(tree.remove(&key_to_remove).unwrap());

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

    //     // // Inserting 49 values into a tree and removing all of them should
    //     // // result in a nil tree root
    //     // // This tests the expansion of the root into a NODE256, and
    //     // // successfully collapsing into a Node48, Node16, Node4, twig, and finally nil
    //     // #[test]
    //     // fn insert49_and_remove49_and_root_should_be_nil() {
    //     //     let mut tree = Tree::<VariableSizeKey, i32>::new();

    //     //     for i in 0..49u32 {
    //     //         let key = &VariableSizeKey::from_slice(&i.to_be_bytes());
    //     //         tree.insert(key, 1);
    //     //     }

    //     //     for i in 0..49u32 {
    //     //         let key = VariableSizeKey::from_slice(&i.to_be_bytes());
    //     //         assert_eq!(tree.remove(&key), true);
    //     //     }

    //     //     assert!(tree.root.is_none());
    //     // }

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
    fn timed_insertion_update_equal_to_root_version() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();

        let key1 = VariableSizeKey::from_str("key_1").unwrap();
        let key2 = VariableSizeKey::from_str("key_2").unwrap();

        // Initial insertion
        assert!(tree.insert(&key1, 1, 10, 0).is_ok());
        let initial_version = tree.version();

        // Attempt update with version equal to root's version
        assert!(tree.insert(&key2, 1, initial_version, 0).is_err());
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
        assert!(tree.remove(&key1).unwrap());
        assert!(tree.remove(&key2).unwrap());
        assert_eq!(tree.version(), 0);
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
            let k = from_be_bytes_key(&tree_entry.0);
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
            let k = from_be_bytes_key(&tree_entry.0);
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
    fn bulk_insert() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let curr_version = tree.version();
        // Create a vector of KV<P, V>
        let kv_pairs = vec![
            KV {
                key: VariableSizeKey::from_str("key_1").unwrap(),
                value: 1,
                version: 0,
                ts: 0,
            },
            KV {
                key: VariableSizeKey::from_str("key_2").unwrap(),
                value: 1,
                version: 2,
                ts: 0,
            },
            KV {
                key: VariableSizeKey::from_str("key_3").unwrap(),
                value: 1,
                version: curr_version + 1,
                ts: 0,
            },
            KV {
                key: VariableSizeKey::from_str("key_4").unwrap(),
                value: 1,
                version: curr_version + 1,
                ts: 0,
            },
            KV {
                key: VariableSizeKey::from_str("key_5").unwrap(),
                value: 1,
                version: curr_version + 2,
                ts: 0,
            },
            KV {
                key: VariableSizeKey::from_str("key_6").unwrap(),
                value: 1,
                version: 0,
                ts: 0,
            },
        ];

        assert!(tree.bulk_insert(&kv_pairs, true).is_ok());
        assert!(tree.version() == curr_version + 2);

        for kv in kv_pairs {
            let (val, version, _) = tree.get(&kv.key, 0).unwrap();
            assert_eq!(val, kv.value);
            if kv.version == 0 {
                assert_eq!(version, curr_version + 1);
            } else {
                assert_eq!(version, kv.version);
            }
        }
        assert!(tree
            .insert(&VariableSizeKey::from_str("key_7").unwrap(), 1, 0, 0)
            .is_ok());
        assert!(tree.version() == curr_version + 3);
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
            tree.remove(&key_to_delete).unwrap();

            // Check remaining keys are still present
            for (remaining_index, remaining_key_data) in set_keys.iter().enumerate() {
                if remaining_index <= index {
                    // Check that the deleted key is no longer present
                    assert!(
                        tree.get(&key_to_delete, version).is_err(),
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
                    tree.get(&remaining_key, version).is_ok(),
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
            tree.remove(&key_to_delete).unwrap();

            // Check remaining keys are still present
            for (remaining_index, remaining_key_data) in set_keys.iter().enumerate() {
                if remaining_index <= index {
                    // Check that the deleted key is no longer present
                    assert!(
                        tree.get(&key_to_delete, version).is_err(),
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
                    tree.get(&remaining_key, version).is_ok(),
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
    fn test_bulk_insert_with_mixed_versions() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let curr_version = tree.version();
        let kv_pairs = vec![
            KV::new(VariableSizeKey::from_str("key_1").unwrap(), 1, 0, 0), // Version 0, should adopt curr_version + 1
            KV::new(
                VariableSizeKey::from_str("key_2").unwrap(),
                2,
                curr_version + 1,
                0,
            ), // Explicit version
            KV::new(VariableSizeKey::from_str("key_3").unwrap(), 3, 0, 0), // Version 0, should adopt curr_version + 1
        ];

        assert!(tree.bulk_insert(&kv_pairs, true).is_ok());
        assert_eq!(tree.version(), curr_version + 1);

        // Verify each key's version and value
        for kv in kv_pairs {
            let (val, version, _) = tree.get(&kv.key, 0).unwrap();
            assert_eq!(val, kv.value);
            assert_eq!(version, curr_version + 1);
        }
    }

    #[test]
    fn test_bulk_insert_version_conflict() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let curr_version = tree.version();
        // Insert a key with a future version
        assert!(tree
            .insert(
                &VariableSizeKey::from_str("key_0").unwrap(),
                0,
                curr_version + 2,
                0
            )
            .is_ok());
        let curr_version = tree.version();

        let kv_pairs = vec![
            KV::new(
                VariableSizeKey::from_str("key_1").unwrap(),
                1,
                curr_version,
                0,
            ), // Version conflict, older than current
            KV::new(
                VariableSizeKey::from_str("key_2").unwrap(),
                2,
                curr_version + 1,
                0,
            ), // Correct version
        ];

        // Expecting an error due to version conflict
        assert!(tree.bulk_insert(&kv_pairs, true).is_err());
        // Verify tree version hasn't changed due to failed insert
        assert_eq!(tree.version(), curr_version);
    }

    #[test]
    fn remove_non_existent_key() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("nonexistent").unwrap();
        let is_removed = tree.remove(&key).unwrap();
        assert!(!is_removed);
    }

    #[test]
    fn remove_key_from_empty_tree() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();
        let key = VariableSizeKey::from_str("test").unwrap();
        let is_removed = tree.remove(&key).unwrap();
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
            assert!(tree.remove(key).unwrap());
        }

        // Verify all keys are removed
        for key in keys {
            assert!(tree.get(&key, 0).is_err());
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
            let is_removed = tree.remove(key).unwrap();
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
        assert!(tree.remove(&key1).unwrap());
        // Insert another key
        let _ = tree.insert(&key2, 2, 0, 0);

        // Verify
        assert!(tree.get(&key1, 0).is_err());
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
                tree.get(&key, *version as u64).is_ok(),
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
        let insert_words = ["test3", "test1", "test5", "test4", "test2"];

        // Insert keys into the tree
        let entries: Vec<KV<VariableSizeKey, i32>> = insert_words
            .iter()
            .map(|word| KV {
                key: VariableSizeKey::from_str(word).unwrap(),
                value: 1,
                version: 1,
                ts: 1,
            })
            .collect();

        tree.bulk_insert(&entries, false).unwrap();

        // Define a range that encompasses all keys
        let range = VariableSizeKey::from_slice_with_termination("test1".as_bytes())
            ..=VariableSizeKey::from_slice_with_termination("test5".as_bytes());

        // Collect results of the range scan
        let results: Vec<_> = tree.range(range).collect();
        assert_eq!(results.len(), insert_words.len());

        // Expected order
        let expected_order = ["test1", "test2", "test3", "test4", "test5"];

        // Assert that results are in expected order
        for (i, result) in results.iter().enumerate() {
            let result_str = std::str::from_utf8(result.0.as_slice()).expect("Invalid UTF-8");
            // The variable size key has a trailing null byte, so we need to trim it
            let result_str_trimmed = &result_str[..result_str.len() - 1];
            assert_eq!(result_str_trimmed, expected_order[i]);
        }
    }

    #[test]
    fn test_add_keys_and_then_delete_keys_which_dont_exist() {
        let mut tree = Tree::<VariableSizeKey, i32>::new();

        // Insert 75 keys
        for i in 1..=75 {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            let _ = tree.insert(&key, i, i as u64, 0);
        }

        // Attempt to delete 25 keys (76 to 100), which do not exist
        for i in 76..=100 {
            let key = VariableSizeKey::from_str(&format!("key{}", i)).unwrap();
            // Since these keys do not exist, remove should return an Err or false depending on implementation
            assert!(tree.remove(&key).is_err() || !tree.remove(&key).unwrap());
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
            assert!(tree.remove(&key).is_err() || !tree.remove(&key).unwrap());
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
        tree.remove(&key).unwrap();

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
            assert!(inserted_data.contains(&(key, *value, *version, *ts)));
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
        assert!(tree.get_version_history(&key3).is_err());
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
    fn test_latest_by_version() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        tree.insert_unchecked(&key, 10, 1, 100).unwrap();
        tree.insert_unchecked(&key, 20, 2, 200).unwrap();
        tree.insert_unchecked(&key, 30, 3, 300).unwrap();

        let query_type = QueryType::LatestByVersion(3);
        let result = tree.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (30, 3, 300));
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
    }
}
