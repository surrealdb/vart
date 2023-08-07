use std::collections::HashMap;
use std::sync::Arc;
use std::sync::RwLock;

use crate::art::{Node, Tree, TrieError};
use crate::node::Timestamp;
use crate::{Key, PrefixTrait};

/// Represents a Reader trait, which provides read access to data.
pub trait Reader {
    fn read(&self) -> Option<Vec<u8>>;
    fn close(&mut self);
}

/// Represents a pointer to a specific snapshot within the Trie structure.
pub struct SnapshotPointer<'a, P: PrefixTrait, V: Clone> {
    id: usize,
    tree: &'a Tree<P, V>,
}

impl<'a, P: PrefixTrait, V: Clone> SnapshotPointer<'a, P, V> {
    /// Creates a new SnapshotPointer instance pointing to a specific snapshot in the Tree.
    pub fn new(tree: &'a Tree<P, V>, snapshot_id: usize) -> SnapshotPointer<'a, P, V> {
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
            .lock()
            .map_err(|_| TrieError::SnapshotMutexError)?;

        // Try to get the snapshot at the specified id, returning `SnapshotNotFound` if not found
        let snapshot = snapshots.get(self.id).ok_or(TrieError::SnapshotNotFound)?;

        // Try to get the immutable reference to the snapshot, returning `SnapshotNotFound` if not found
        let snapshot = snapshot.as_ref().ok_or(TrieError::SnapshotNotFound)?;

        // Return the timestamp of the snapshot
        Ok(snapshot.ts())
    }

    /// Inserts a key-value pair into the snapshot referred to by this SnapshotPointer.
    pub fn insert<K: Key>(&mut self, key: &K, value: V) -> Result<(), TrieError> {
        // Acquire a lock on the snapshot vector to access the desired snapshot
        let mut snapshots = self
            .tree
            .snapshots
            .lock()
            .map_err(|_| TrieError::SnapshotMutexError)?;

        // Try to get the mutable reference to the snapshot, returning `SnapshotNotFound` if not found
        let snapshot = snapshots
            .get_mut(self.id)
            .ok_or(TrieError::SnapshotNotFound)?;

        // Try to get the mutable reference to the snapshot, returning `SnapshotNotFound` if not found
        let snapshot = snapshot.as_mut().ok_or(TrieError::SnapshotNotFound)?;

        // Insert the key-value pair into the snapshot
        snapshot.insert(key, value)?;

        Ok(())
    }

    pub fn get<K: Key>(&self, key: &K) -> Result<Option<(V, u64)>, TrieError> {
        // Acquire a lock on the snapshot vector to access the desired snapshot
        let snapshots = self
            .tree
            .snapshots
            .lock()
            .map_err(|_| TrieError::SnapshotMutexError)?;

        // Try to get the snapshot at the specified id, returning `SnapshotNotFound` if not found
        let snapshot = snapshots.get(self.id).ok_or(TrieError::SnapshotNotFound)?;

        // Try to get the immutable reference to the snapshot, returning `SnapshotNotFound` if not found
        let snapshot = snapshot.as_ref().ok_or(TrieError::SnapshotNotFound)?;
        Ok(snapshot.get(key))
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
    pub(crate) id: usize,
    pub(crate) ts: u64,
    pub(crate) root: Arc<Node<P, V>>,
    pub(crate) readers: HashMap<u32, Box<dyn Reader>>,
    pub(crate) max_reader_id: u32,
    pub(crate) closed: bool,
    pub(crate) mutex: RwLock<()>,
}

impl<P: PrefixTrait, V: Clone> Snapshot<P, V> {
    /// Creates a new Snapshot instance with the provided snapshot_id and root node.
    pub fn new_snapshot(snapshot_id: usize, root: Arc<Node<P, V>>) -> Snapshot<P, V> {
        Snapshot {
            id: snapshot_id,
            ts: root.ts() + 1,
            root,
            readers: HashMap::new(),
            max_reader_id: 0,
            closed: false,
            mutex: RwLock::new(()),
        }
    }

    /// Inserts a key-value pair into the snapshot.
    pub fn insert<K: Key>(&mut self, key: &K, value: V) -> Result<(), TrieError> {
        // Acquire a lock on the snapshot mutex to ensure exclusive access to the snapshot
        let _guard = self.mutex.write().map_err(|_| TrieError::MutexError)?;

        // Insert the key-value pair into the root node using a recursive function
        let (new_node, _) = match Node::insert_recurse(&self.root, key, value, self.ts, 0) {
            Ok((new_node, old_node)) => (new_node, old_node),
            Err(err) => {
                return Err(err);
            }
        };

        // Update the root node with the new node after insertion
        self.root = new_node;

        Ok(())
    }

    /// Retrieves the value and timestamp associated with the given key from the snapshot.
    pub fn get<K: Key>(&self, key: &K) -> Option<(V, u64)> {
        // Acquire a read lock on the snapshot mutex to ensure shared access to the snapshot
        let _guard = self.mutex.read().unwrap();

        // Use a recursive function to get the value and timestamp from the root node
        let (_, value, ts) = Node::get_recurse(self.root.as_ref(), key)?;

        // Return the value and timestamp wrapped in an Option
        Some((value.clone(), ts.clone()))
    }

    /// Returns the timestamp of the snapshot.
    pub fn ts(&self) -> u64 {
        // Acquire a read lock on the snapshot mutex to ensure shared access to the snapshot
        let _guard = self.mutex.read().unwrap();
        self.root.ts()
    }

    /// Closes the snapshot, preventing further modifications, and releases associated resources.
    pub fn close(&mut self) -> Result<(), TrieError> {
        // Acquire a write lock on the snapshot mutex to ensure exclusive access to the snapshot
        let _guard = self.mutex.write().map_err(|_| TrieError::MutexError)?;

        // Check if the snapshot is already closed
        if self.closed {
            return Err(TrieError::SnapshotAlreadyClosed);
        }

        // Check if there are any active readers for the snapshot
        if !self.readers.is_empty() {
            return Err(TrieError::SnapshotReadersNotClosed);
        }

        // Mark the snapshot as closed
        self.closed = true;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
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
                snap1.get(&VectorKey::from_str("key_1")).unwrap().unwrap(),
                (1, 1)
            );
            assert_eq!(
                snap2.get(&VectorKey::from_str("key_1")).unwrap().unwrap(),
                (1, 1)
            );
        }

        // keys inserted after snapshot creation should not be visible to other snapshots
        assert!(tree.insert(&VectorKey::from_str("key_2"), 1, 0).is_ok());
        let mut snapshots = tree.snapshots.lock().unwrap();

        {
            let snap1 = snapshots.get(0).unwrap().as_ref().unwrap();
            assert!(snap1.get(&VectorKey::from_str("key_2")).is_none());

            let snap2 = snapshots.get(1).unwrap().as_ref().unwrap();
            assert!(snap2.get(&VectorKey::from_str("key_2")).is_none());
        }

        // keys inserted after snapshot creation should be visible to the snapshot that inserted them
        {
            let snap1 = snapshots.get_mut(0).unwrap().as_mut().unwrap();
            assert!(snap1.insert(&VectorKey::from_str("key_3_snap1"), 2).is_ok());
            assert_eq!(
                snap1.get(&VectorKey::from_str("key_3_snap1")).unwrap(),
                (2, 2)
            );

            let snap2 = snapshots.get_mut(1).unwrap().as_mut().unwrap();
            assert!(snap2.insert(&VectorKey::from_str("key_3_snap2"), 3).is_ok());
            assert_eq!(
                snap2.get(&VectorKey::from_str("key_3_snap2")).unwrap(),
                (3, 2)
            );
        }

        // keys inserted after snapshot creation should not be visible to other snapshots
        {
            let snap1 = snapshots.get(0).unwrap().as_ref().unwrap();
            assert!(snap1.get(&VectorKey::from_str("key_3_snap2")).is_none());

            let snap2 = snapshots.get(1).unwrap().as_ref().unwrap();
            assert!(snap2.get(&VectorKey::from_str("key_3_snap1")).is_none());
        }

        // solve this using hashmap
        // assert!(snap1.close().is_ok());
        // assert!(snap2.close().is_ok());
        // assert_eq!(snap1.get(&VectorKey::from_str("key_1_snap1")).unwrap().unwrap(), (2, 2));

        // assert_eq!(tree.snapshot_count().unwrap(), 0);
    }
}
