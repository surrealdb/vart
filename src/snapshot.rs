use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, RwLock};

use crate::art::{Node, Tree, TrieError};
use crate::iter::IterationPointer;
use crate::node::Timestamp;
use crate::{Key, PrefixTrait};

/// Represents a pointer to a specific snapshot within the Trie structure.
pub struct SnapshotPointer<'a, P: PrefixTrait, V: Clone> {
    id: u64,
    tree: &'a Tree<P, V>,
}

impl<'a, P: PrefixTrait, V: Clone> SnapshotPointer<'a, P, V> {
    /// Creates a new SnapshotPointer instance pointing to a specific snapshot in the Tree.
    pub fn new(tree: &'a Tree<P, V>, snapshot_id: u64) -> SnapshotPointer<'a, P, V> {
        SnapshotPointer {
            id: snapshot_id,
            tree,
        }
    }

    /// Returns the timestamp of the snapshot referred to by this SnapshotPointer.
    pub fn ts(&self) -> Result<u64, TrieError> {
        // Acquire a lock on the snapshot vector to access the desired snapshot
        let snapshots = self
            .tree
            .snapshots
            .read()
            .map_err(|_| TrieError::SnapshotMutexError)?;

        // Try to get the snapshot at the specified id, returning `SnapshotNotFound` if not found
        let snapshot = snapshots.get(&self.id).ok_or(TrieError::SnapshotNotFound)?;

        // Return the timestamp of the snapshot
        Ok(snapshot.ts())
    }

    /// Inserts a key-value pair into the snapshot referred to by this SnapshotPointer.
    pub fn insert<K: Key>(&mut self, key: &K, value: V) -> Result<(), TrieError> {
        // Acquire a lock on the snapshot vector to access the desired snapshot
        let mut snapshots = self
            .tree
            .snapshots
            .write()
            .map_err(|_| TrieError::SnapshotMutexError)?;

        // Try to get the mutable reference to the snapshot, returning `SnapshotNotFound` if not found
        let snapshot = snapshots
            .get_mut(&self.id)
            .ok_or(TrieError::SnapshotNotFound)?;

        // Insert the key-value pair into the snapshot
        snapshot.insert(key, value)?;

        Ok(())
    }

    pub fn get<K: Key>(&self, key: &K, ts: u64) -> Result<Option<(V, u64)>, TrieError> {
        // Acquire a lock on the snapshot vector to access the desired snapshot
        let snapshots = self
            .tree
            .snapshots
            .read()
            .map_err(|_| TrieError::SnapshotMutexError)?;

        // Try to get the snapshot at the specified id, returning `SnapshotNotFound` if not found
        let snapshot = snapshots.get(&self.id).ok_or(TrieError::SnapshotNotFound)?;

        Ok(snapshot.get(key, ts))
    }

    /// Closes the snapshot referred to by this SnapshotPointer, releasing resources associated with it.
    pub fn close(&mut self) -> Result<(), TrieError> {
        // Call the close method of the Tree with the id of the snapshot to close it
        self.tree.close(self.id)?;
        Ok(())
    }
}

/// Represents a snapshot of the data within the Trie.
pub struct Snapshot<P: PrefixTrait, V: Clone> {
    pub(crate) id: u64,
    pub(crate) ts: u64,
    pub(crate) root: RwLock<Arc<Node<P, V>>>,
    pub(crate) readers: RwLock<HashMap<u64, ()>>,
    pub(crate) max_active_readers: AtomicU64,
    pub(crate) closed: bool,
}

impl<P: PrefixTrait, V: Clone> Snapshot<P, V> {
    /// Creates a new Snapshot instance with the provided snapshot_id and root node.
    pub fn new_snapshot(snapshot_id: u64, root: Arc<Node<P, V>>) -> Snapshot<P, V> {
        Snapshot {
            id: snapshot_id,
            ts: root.ts() + 1,
            root: RwLock::new(root),
            readers: RwLock::new(HashMap::new()),
            max_active_readers: AtomicU64::new(0),
            closed: false,
        }
    }

    pub fn new_reader(&self) -> Result<IterationPointer<P, V>, TrieError> {
        let reader_id = self.max_active_readers.fetch_add(1, Ordering::SeqCst);
        let mut readers = self.readers.write().map_err(|_| TrieError::MutexError)?;
        readers.insert(reader_id, ());
        let root = self.root.read().unwrap();
        Ok(IterationPointer::new(self, root.clone(), reader_id))
    }

    pub fn close_reader(&self, reader_id: u64) -> Result<(), TrieError> {
        let mut readers = self.readers.write().map_err(|_| TrieError::MutexError)?;
        readers.remove(&reader_id);
        self.max_active_readers.fetch_sub(1, Ordering::SeqCst);
        Ok(())
    }

    /// Inserts a key-value pair into the snapshot.
    pub fn insert<K: Key>(&mut self, key: &K, value: V) -> Result<(), TrieError> {
        // Acquire a lock on the snapshot mutex to ensure exclusive access to the snapshot
        let mut root = self.root.write().map_err(|_| TrieError::MutexError)?;

        // Insert the key-value pair into the root node using a recursive function
        let (new_node, _) = match Node::insert_recurse(&root, key, value, self.ts, 0) {
            Ok((new_node, old_node)) => (new_node, old_node),
            Err(err) => {
                return Err(err);
            }
        };

        // Update the root node with the new node after insertion
        *root = new_node;

        Ok(())
    }

    /// Retrieves the value and timestamp associated with the given key from the snapshot.
    pub fn get<K: Key>(&self, key: &K, ts: u64) -> Option<(V, u64)> {
        // Acquire a read lock on the snapshot mutex to ensure shared access to the snapshot
        let root = self.root.read().unwrap();

        // Use a recursive function to get the value and timestamp from the root node
        let (_, value, ts) = Node::get_recurse(root.as_ref(), key, ts)?;

        // Return the value and timestamp wrapped in an Option
        Some((value, ts))
    }

    /// Returns the timestamp of the snapshot.
    pub fn ts(&self) -> u64 {
        // Acquire a read lock on the snapshot mutex to ensure shared access to the snapshot
        let root = self.root.read().unwrap();
        root.ts()
    }

    /// Closes the snapshot, preventing further modifications, and releases associated resources.
    pub fn close(&mut self) -> Result<(), TrieError> {
        // Check if the snapshot is already closed
        if self.closed {
            return Err(TrieError::SnapshotAlreadyClosed);
        }

        // Check if there are any active readers for the snapshot
        if self.max_active_readers.load(Ordering::SeqCst) > 0 {
            return Err(TrieError::SnapshotReadersNotClosed);
        }

        // Mark the snapshot as closed
        self.closed = true;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering;

    use super::Tree;
    use crate::ArrayPrefix;
    use crate::VectorKey;

    #[test]
    fn test_snapshot_creation() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();
        assert!(tree.insert(&VectorKey::from_str("key_1"), 1, 0).is_ok());
        assert!(tree.insert(&VectorKey::from_str("key_2"), 1, 0).is_ok());
        assert!(tree.insert(&VectorKey::from_str("key_3"), 1, 0).is_ok());

        let mut snap1 = tree.create_snapshot().unwrap();
        assert!(snap1.insert(&VectorKey::from_str("key_1"), 1).is_ok());

        assert_eq!(tree.snapshot_count().unwrap(), 1);
        assert_eq!(tree.ts(), 3);
        assert_eq!(snap1.ts().unwrap(), 4);
    }

    #[test]
    fn test_snapshot_isolation() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();
        assert!(tree.insert(&VectorKey::from_str("key_1"), 1, 0).is_ok());

        // keys inserted before snapshot creation should be visible
        {
            let snap1 = tree.create_snapshot().unwrap();
            let snap2 = tree.create_snapshot().unwrap();

            assert_eq!(tree.snapshot_count().unwrap(), 2);
            assert_eq!(snap1.id, 0);
            assert_eq!(snap2.id, 1);

            assert_eq!(
                snap1
                    .get(&VectorKey::from_str("key_1"), tree.ts())
                    .unwrap()
                    .unwrap(),
                (1, 1)
            );
            assert_eq!(
                snap2
                    .get(&VectorKey::from_str("key_1"), tree.ts())
                    .unwrap()
                    .unwrap(),
                (1, 1)
            );
        }

        let snap1_id = &0u64;
        let snap2_id = &1u64;

        // keys inserted after snapshot creation should not be visible to other snapshots
        assert!(tree.insert(&VectorKey::from_str("key_2"), 1, 0).is_ok());
        {
            let mut snapshots = tree.snapshots.write().unwrap();

            {
                let snap1 = snapshots.get(snap1_id).unwrap();
                assert!(snap1
                    .get(&VectorKey::from_str("key_2"), snap1.ts())
                    .is_none());

                let snap2 = snapshots.get(snap2_id).unwrap();
                assert!(snap2
                    .get(&VectorKey::from_str("key_2"), snap2.ts())
                    .is_none());
            }

            // keys inserted after snapshot creation should be visible to the snapshot that inserted them
            {
                let snap1 = snapshots.get_mut(snap1_id).unwrap();
                assert!(snap1.insert(&VectorKey::from_str("key_3_snap1"), 2).is_ok());
                assert_eq!(
                    snap1
                        .get(&VectorKey::from_str("key_3_snap1"), snap1.ts())
                        .unwrap(),
                    (2, 2)
                );

                let snap2 = snapshots.get_mut(snap2_id).unwrap();
                assert!(snap2.insert(&VectorKey::from_str("key_3_snap2"), 3).is_ok());
                assert_eq!(
                    snap2
                        .get(&VectorKey::from_str("key_3_snap2"), snap2.ts())
                        .unwrap(),
                    (3, 2)
                );
            }

            // keys inserted after snapshot creation should not be visible to other snapshots
            {
                let snap1 = snapshots.get(snap1_id).unwrap();
                assert!(snap1
                    .get(&VectorKey::from_str("key_3_snap2"), snap1.ts())
                    .is_none());

                let snap2 = snapshots.get(snap2_id).unwrap();
                assert!(snap2
                    .get(&VectorKey::from_str("key_3_snap1"), snap2.ts())
                    .is_none());
            }
        }

        {
            let mut snap1 = tree.get_snapshot(*snap1_id).unwrap();
            assert!(snap1.close().is_ok());

            let mut snap2 = tree.get_snapshot(*snap2_id).unwrap();
            assert!(snap2.close().is_ok());
        }

        assert_eq!(tree.snapshot_count().unwrap(), 0);
    }

    #[test]
    fn test_snapshot_readers() {
        let mut tree: Tree<ArrayPrefix<32>, i32> = Tree::<ArrayPrefix<32>, i32>::new();
        assert!(tree.insert(&VectorKey::from_str("key_1"), 1, 0).is_ok());
        assert!(tree.insert(&VectorKey::from_str("key_2"), 1, 0).is_ok());
        assert!(tree.insert(&VectorKey::from_str("key_3"), 1, 0).is_ok());

        let mut snap1 = tree.create_snapshot().unwrap();
        assert!(snap1.insert(&VectorKey::from_str("key_4"), 1).is_ok());

        let snapshots = tree.snapshots.read().unwrap();
        let snap1 = snapshots.get(&snap1.id).unwrap();

        let mut len = 0;
        let mut reader = snap1.new_reader().unwrap();
        for _ in reader.iter() {
            len += 1;
        }
        assert_eq!(len, 4);
        assert!(reader.close().is_ok());

        assert_eq!(snap1.max_active_readers.load(Ordering::SeqCst), 0);
    }
}
