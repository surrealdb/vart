//! This module defines the SnapshotPointer and Snapshot structs for managing snapshots within a Trie structure.

use crate::art::{Node, Tree, TrieError};
use crate::iter::IterationPointer;
use crate::node::Timestamp;
use crate::KeyTrait;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// Represents a pointer to a specific snapshot within the Trie structure.
pub struct SnapshotPointer<'a, P: KeyTrait, V: Clone> {
    id: u64,
    tree: &'a mut Tree<P, V>,
}

impl<'a, P: KeyTrait, V: Clone> SnapshotPointer<'a, P, V> {
    /// Creates a new SnapshotPointer instance pointing to a specific snapshot in the Tree.
    pub fn new(tree: &'a mut Tree<P, V>, snapshot_id: u64) -> Self {
        SnapshotPointer {
            id: snapshot_id,
            tree,
        }
    }

    /// Returns the timestamp of the snapshot referred to by this SnapshotPointer.
    pub fn ts(&self) -> Result<u64, TrieError> {
        self.tree
            .snapshots
            .get(&self.id)
            .ok_or(TrieError::SnapshotNotFound)
            .map(|snapshot| snapshot.ts())
    }

    /// Inserts a key-value pair into the snapshot referred to by this SnapshotPointer.
    pub fn insert(&mut self, key: &P, value: V) -> Result<(), TrieError> {
        self.tree
            .snapshots
            .get_mut(&self.id)
            .ok_or(TrieError::SnapshotNotFound)
            .and_then(|snapshot| snapshot.insert(key, value))
    }

    /// Retrieves the value associated with the given key from the snapshot referred to by this SnapshotPointer.
    pub fn get(&self, key: &P, ts: u64) -> Result<(V, u64), TrieError> {
        self.tree
            .snapshots
            .get(&self.id)
            .ok_or(TrieError::SnapshotNotFound)
            .and_then(|snapshot| snapshot.get(key, ts))
            .map_err(|err| err.into()) // Convert the inner TrieError to the outer Result type
    }

    pub fn new_reader(&mut self) -> Result<IterationPointer<P, V>, TrieError> {
        self.tree
            .snapshots
            .get_mut(&self.id)
            .ok_or(TrieError::SnapshotNotFound)
            .and_then(|snapshot| snapshot.new_reader())
    }

    pub fn close_reader(&mut self, reader_id: u64) -> Result<(), TrieError> {
        self.tree
            .snapshots
            .get_mut(&self.id)
            .ok_or(TrieError::SnapshotNotFound)
            .and_then(|snapshot| snapshot.close_reader(reader_id))
    }

    pub fn active_readers(&self) -> Result<u64, TrieError> {
        self.tree
            .snapshots
            .get(&self.id)
            .ok_or(TrieError::SnapshotNotFound)
            .map(|snapshot| snapshot.max_active_readers.load(Ordering::SeqCst))
    }

    /// Closes the snapshot referred to by this SnapshotPointer, releasing resources associated with it.
    pub fn close(&mut self) -> Result<(), TrieError> {
        self.tree.close(self.id)
    }
}

/// Represents a snapshot of the data within the Trie.
pub struct Snapshot<P: KeyTrait, V: Clone> {
    id: u64,
    ts: u64,
    root: Arc<Node<P, V>>,
    readers: HashMap<u64, ()>,
    max_active_readers: AtomicU64,
    closed: bool,
}

impl<P: KeyTrait, V: Clone> Snapshot<P, V> {
    pub(crate) fn new(id: u64, root: Arc<Node<P, V>>, ts: u64) -> Self {
        Snapshot {
            id,
            ts: ts,
            root: root,
            readers: HashMap::new(),
            max_active_readers: AtomicU64::new(0),
            closed: false,
        }
    }

    /// Creates a new reader for the snapshot, allowing for concurrent read access.
    ///
    /// # Returns
    ///
    /// A new IterationPointer instance that can be used for reading the snapshot.
    pub fn new_reader(&mut self) -> Result<IterationPointer<P, V>, TrieError> {
        let reader_id = self.max_active_readers.fetch_add(1, Ordering::SeqCst);
        self.readers.insert(reader_id, ());
        Ok(IterationPointer::new(self, self.root.clone(), reader_id))
    }

    /// Closes the reader with the given reader_id.
    pub fn close_reader(&mut self, reader_id: u64) -> Result<(), TrieError> {
        self.readers.remove(&reader_id);
        self.max_active_readers.fetch_sub(1, Ordering::SeqCst);
        Ok(())
    }

    /// Inserts a key-value pair into the snapshot.
    pub fn insert(&mut self, key: &P, value: V) -> Result<(), TrieError> {
        let (new_node, _) = Node::insert_recurse(&self.root, key, value, self.ts, 0)?;
        self.root = new_node;
        Ok(())
    }

    /// Retrieves the value and timestamp associated with the given key from the snapshot.
    pub fn get(&self, key: &P, ts: u64) -> Result<(V, u64), TrieError> {
        Node::get_recurse(self.root.as_ref(), key, ts).map(|(_, value, ts)| (value, ts))
    }

    /// Returns the timestamp of the snapshot.
    pub fn ts(&self) -> u64 {
        self.root.ts()
    }

    /// Closes the snapshot, preventing further modifications, and releases associated resources.
    pub fn close(&mut self) -> Result<(), TrieError> {
        if self.closed {
            return Err(TrieError::SnapshotAlreadyClosed);
        }

        if self.max_active_readers.load(Ordering::SeqCst) > 0 {
            return Err(TrieError::SnapshotReadersNotClosed);
        }

        self.closed = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Tree;
    use crate::iter::IterationPointer;
    use crate::VectorKey;

    #[test]
    fn test_snapshot_creation() {
        let mut tree: Tree<VectorKey, i32> = Tree::<VectorKey, i32>::new();
        let keys = ["key_1", "key_2", "key_3"];

        for key in keys.iter() {
            assert!(tree.insert(&VectorKey::from_str(key), 1, 0).is_ok());
        }

        let mut snap1 = tree.create_snapshot().unwrap();
        let key_to_insert = "key_1";
        assert!(snap1.insert(&VectorKey::from_str(key_to_insert), 1).is_ok());

        let expected_snap_ts = keys.len() as u64 + 1;
        assert_eq!(snap1.ts().unwrap(), expected_snap_ts);
        assert_eq!(tree.snapshot_count().unwrap(), 1);

        let expected_tree_ts = keys.len() as u64;
        assert_eq!(tree.ts(), expected_tree_ts);
    }

    #[test]
    fn test_snapshot_isolation() {
        let mut tree: Tree<VectorKey, i32> = Tree::<VectorKey, i32>::new();
        let key_1 = VectorKey::from_str("key_1");
        let key_2 = VectorKey::from_str("key_2");
        let key_3_snap1 = VectorKey::from_str("key_3_snap1");
        let key_3_snap2 = VectorKey::from_str("key_3_snap2");

        assert!(tree.insert(&key_1, 1, 0).is_ok());
        let initial_ts = tree.ts();

        // Keys inserted before snapshot creation should be visible
        let snap1 = tree.create_snapshot().unwrap();
        let snap1_id = snap1.id;
        assert_eq!(snap1.id, 0);
        assert_eq!(snap1.get(&key_1, initial_ts).unwrap(), (1, 1));

        let snap2 = tree.create_snapshot().unwrap();
        let snap2_id = snap2.id;
        assert_eq!(snap2.id, 1);
        assert_eq!(snap2.get(&key_1, initial_ts).unwrap(), (1, 1));

        assert_eq!(tree.snapshot_count().unwrap(), 2);

        // Keys inserted after snapshot creation should not be visible to other snapshots
        assert!(tree.insert(&key_2, 1, 0).is_ok());
        let snap1 = tree.get_snapshot(snap1_id).unwrap();
        assert!(snap1.get(&key_2, snap1.ts().unwrap()).is_err());

        let snap2 = tree.get_snapshot(snap2_id).unwrap();
        assert!(snap2.get(&key_2, snap2.ts().unwrap()).is_err());

        // Keys inserted after snapshot creation should be visible to the snapshot that inserted them
        let mut snap1 = tree.get_snapshot(snap1_id).unwrap();
        assert!(snap1.insert(&key_3_snap1, 2).is_ok());
        assert_eq!(
            snap1.get(&key_3_snap1, snap1.ts().unwrap()).unwrap(),
            (2, 2)
        );

        let mut snap2 = tree.get_snapshot(snap2_id).unwrap();
        assert!(snap2.insert(&key_3_snap2, 3).is_ok());
        assert_eq!(
            snap2.get(&key_3_snap2, snap2.ts().unwrap()).unwrap(),
            (3, 2)
        );

        // Keys inserted after snapshot creation should not be visible to other snapshots
        let snap1 = tree.get_snapshot(snap1_id).unwrap();
        assert!(snap1.get(&key_3_snap2, snap1.ts().unwrap()).is_err());

        let snap2 = tree.get_snapshot(snap2_id).unwrap();
        assert!(snap2.get(&key_3_snap1, snap2.ts().unwrap()).is_err());

        let mut snap1 = tree.get_snapshot(snap1_id).unwrap();
        assert!(snap1.close().is_ok());

        let mut snap2 = tree.get_snapshot(snap2_id).unwrap();
        assert!(snap2.close().is_ok());

        assert_eq!(tree.snapshot_count().unwrap(), 0);
    }

    #[test]
    fn test_snapshot_readers() {
        let mut tree: Tree<VectorKey, i32> = Tree::<VectorKey, i32>::new();
        let key_1 = VectorKey::from_str("key_1");
        let key_2 = VectorKey::from_str("key_2");
        let key_3 = VectorKey::from_str("key_3");
        let key_4 = VectorKey::from_str("key_4");

        assert!(tree.insert(&key_1, 1, 0).is_ok());
        assert!(tree.insert(&key_2, 1, 0).is_ok());
        assert!(tree.insert(&key_3, 1, 0).is_ok());

        let mut snap = tree.create_snapshot().unwrap();
        assert!(snap.insert(&key_4, 1).is_ok());

        // Reader 1
        let reader1 = snap.new_reader().unwrap();
        let reader1_id = reader1.id;
        assert_eq!(count_items(&reader1), 4);

        // Reader 2
        let reader2 = snap.new_reader().unwrap();
        let reader2_id = reader2.id;
        assert_eq!(count_items(&reader2), 4);

        // Active readers
        assert_eq!(snap.active_readers().unwrap(), 2);
        assert!(snap.close().is_err());

        // Close readers
        assert!(snap.close_reader(reader1_id).is_ok());
        assert!(snap.close_reader(reader2_id).is_ok());
        assert!(snap.close().is_ok());
    }

    fn count_items(reader: &IterationPointer<VectorKey, i32>) -> usize {
        let mut len = 0;
        for _ in reader.iter() {
            len += 1;
        }
        len
    }
}
