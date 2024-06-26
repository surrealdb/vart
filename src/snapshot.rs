//! This module defines the Snapshot struct for managing snapshots within a Trie structure.
use std::sync::Arc;

use crate::art::{Node, Tree};
use crate::iter::IterationPointer;
use crate::node::Version;
use crate::{KeyTrait, TrieError};

/// Represents a snapshot of the data within the Trie.
pub struct Snapshot<P: KeyTrait, V: Clone> {
    pub(crate) ts: u64,
    pub(crate) root: Option<Arc<Node<P, V>>>,
    pub(crate) closed: bool,
}

impl<P: KeyTrait, V: Clone> Snapshot<P, V> {
    /// Creates a new Snapshot instance with the provided snapshot_id and root node.
    pub(crate) fn new(root: Option<Arc<Node<P, V>>>, ts: u64) -> Self {
        Snapshot {
            ts,
            root,
            closed: false,
        }
    }

    /// Inserts a key-value pair into the snapshot.
    pub fn insert(&mut self, key: &P, value: V, ts: u64) -> Result<(), TrieError> {
        // Check if the snapshot is already closed
        self.is_closed()?;

        // Insert the key-value pair into the root node using a recursive function
        match &self.root {
            Some(root) => {
                let (new_node, _) = match Node::insert_recurse(root, key, value, self.ts, ts, 0) {
                    Ok((new_node, old_node)) => (new_node, old_node),
                    Err(err) => {
                        return Err(err);
                    }
                };

                // Update the root node with the new node after insertion
                self.root = Some(new_node);
            }
            None => {
                self.root = Some(Arc::new(Node::new_twig(
                    key.as_slice().into(),
                    key.as_slice().into(),
                    value,
                    self.ts,
                    ts,
                )))
            }
        };

        Ok(())
    }

    /// Retrieves the value and timestamp associated with the given key from the snapshot.
    pub fn get(&self, key: &P) -> Result<(V, u64, u64), TrieError> {
        // Check if the snapshot is already closed
        self.is_closed()?;

        // Use a recursive function to get the value and timestamp from the root node
        match self.root.as_ref() {
            Some(root) => Node::get_recurse(root, key, root.version())
                .map(|(_, value, version, ts)| (value, version, ts)),
            None => Err(TrieError::KeyNotFound),
        }
    }

    /// Returns the version of the snapshot.
    pub fn version(&self) -> u64 {
        self.root.as_ref().map_or(0, |root| root.version())
    }

    fn is_closed(&self) -> Result<(), TrieError> {
        if self.closed {
            return Err(TrieError::SnapshotAlreadyClosed);
        }
        Ok(())
    }

    /// Closes the snapshot, preventing further modifications, and releases associated resources.
    pub fn close(&mut self) -> Result<(), TrieError> {
        // Check if the snapshot is already closed
        self.is_closed()?;

        // Mark the snapshot as closed
        self.closed = true;

        Ok(())
    }

    pub fn new_reader(&mut self) -> Result<IterationPointer<P, V>, TrieError> {
        // Check if the snapshot is already closed
        self.is_closed()?;

        if self.root.is_none() {
            return Err(TrieError::SnapshotEmpty);
        }

        Ok(IterationPointer::new(self.root.as_ref().unwrap().clone()))
    }

    pub fn remove(&mut self, key: &P) -> Result<bool, TrieError> {
        // Check if the tree is already closed
        self.is_closed()?;

        let (new_root, is_deleted) = Tree::remove_from_node(self.root.as_ref(), key);

        self.root = new_root;
        Ok(is_deleted)
    }

    pub fn ts(&self) -> u64 {
        self.ts
    }
}

#[cfg(test)]
mod tests {
    use crate::art::Tree;
    use crate::iter::IterationPointer;
    use crate::VariableSizeKey;
    use std::str::FromStr;

    #[test]
    fn snapshot_creation() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let keys = ["key_1", "key_2", "key_3"];

        for key in keys.iter() {
            assert!(tree
                .insert(&VariableSizeKey::from_str(key).unwrap(), 1, 0, 0)
                .is_ok());
        }

        let mut snap1 = tree.create_snapshot().unwrap();
        let key_to_insert = "key_1";
        assert!(snap1
            .insert(&VariableSizeKey::from_str(key_to_insert).unwrap(), 1, 0)
            .is_ok());

        let expected_snap_ts = keys.len() as u64 + 1;
        assert_eq!(snap1.version(), expected_snap_ts);

        let expected_tree_ts = keys.len() as u64;
        assert_eq!(tree.version(), expected_tree_ts);
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
        let mut snap1 = tree.create_snapshot().unwrap();
        assert_eq!(snap1.get(&key_1).unwrap(), (1, 1, 0));

        let mut snap2 = tree.create_snapshot().unwrap();
        assert_eq!(snap2.get(&key_1).unwrap(), (1, 1, 0));

        // Keys inserted after snapshot creation should not be visible to other snapshots
        assert!(tree.insert(&key_2, 1, 0, 0).is_ok());
        assert!(snap1.get(&key_2).is_err());
        assert!(snap2.get(&key_2).is_err());

        // Keys inserted after snapshot creation should be visible to the snapshot that inserted them
        assert!(snap1.insert(&key_3_snap1, 2, 0).is_ok());
        assert_eq!(snap1.get(&key_3_snap1).unwrap(), (2, 2, 0));

        assert!(snap2.insert(&key_3_snap2, 3, 0).is_ok());
        assert_eq!(snap2.get(&key_3_snap2).unwrap(), (3, 2, 0));

        // Keys inserted after snapshot creation should not be visible to other snapshots
        assert!(snap1.get(&key_3_snap2).is_err());
        assert!(snap2.get(&key_3_snap1).is_err());

        assert!(snap1.close().is_ok());
        assert!(snap2.close().is_ok());
    }

    #[test]
    fn snapshot_readers() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let key_1 = VariableSizeKey::from_str("key_1").unwrap();
        let key_2 = VariableSizeKey::from_str("key_2").unwrap();
        let key_3 = VariableSizeKey::from_str("key_3").unwrap();
        let key_4 = VariableSizeKey::from_str("key_4").unwrap();

        assert!(tree.insert(&key_1, 1, 0, 0).is_ok());
        assert!(tree.insert(&key_2, 1, 0, 0).is_ok());
        assert!(tree.insert(&key_3, 1, 0, 0).is_ok());

        let mut snap = tree.create_snapshot().unwrap();
        assert!(snap.insert(&key_4, 1, 0).is_ok());

        // Reader 1
        let reader1 = snap.new_reader().unwrap();
        assert_eq!(count_items(&reader1), 4);

        // Reader 2
        let reader2 = snap.new_reader().unwrap();
        assert_eq!(count_items(&reader2), 4);

        // Close snapshot
        assert!(snap.close().is_ok());
    }

    fn count_items(reader: &IterationPointer<VariableSizeKey, i32>) -> usize {
        let mut len = 0;
        for _ in reader.iter() {
            len += 1;
        }
        len
    }

    #[test]
    fn test_insert_and_remove() {
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

        let mut snap = tree.create_snapshot().unwrap();

        // Delete one key at a time and check remaining keys
        for (index, key_data_to_delete) in set_keys.iter().enumerate() {
            let key_to_delete = VariableSizeKey {
                data: key_data_to_delete.to_vec(),
            };
            snap.remove(&key_to_delete).unwrap();

            // Check remaining keys are still present
            for (remaining_index, remaining_key_data) in set_keys.iter().enumerate() {
                if remaining_index <= index {
                    // This key has been deleted; skip
                    // Check that the deleted key is no longer present
                    assert!(
                        snap.get(&key_to_delete).is_err(),
                        "Key {:?} should not exist after deletion",
                        key_data_to_delete
                    );
                    continue;
                }
                let remaining_key = VariableSizeKey {
                    data: remaining_key_data.to_vec(),
                };
                assert!(
                    snap.get(&remaining_key).is_ok(),
                    "Key {:?} should exist",
                    remaining_key_data
                );
            }
        }
    }
}
