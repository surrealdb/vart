use std::sync::Arc;
use std::sync::RwLock;
use std::collections::HashMap;


use crate::{Key, PrefixTrait};
use crate::node::Timestamp;
use crate::art::{Node, Tree, TrieError};

pub trait Reader {
    fn read(&self) -> Option<Vec<u8>>;
    fn close(&mut self);
}


pub struct SnapshotPointer<'a, P: PrefixTrait, V: Clone> {
    index: usize,
    tree: &'a Tree<P, V>,
}

impl <'a, P: PrefixTrait, V: Clone> SnapshotPointer<'a, P, V> {
    pub fn new(tree: &'a Tree<P, V>, snapshot_id: usize) -> SnapshotPointer<'a, P, V> {
        SnapshotPointer {
            index: snapshot_id,
            tree: tree,
        }
    }

    pub fn ts(&self) -> Result<u64, TrieError> {
        let snapshots = self.tree.snapshots.lock().map_err(|_| TrieError::SnapshotMutexError)?;
        let snapshot = snapshots.get(self.index);
        if snapshot.is_none() {
            return Err(TrieError::SnapshotNotFound);
        }
        let snapshot = snapshot.unwrap().as_ref();
        if snapshot.is_none() {
            return Err(TrieError::SnapshotNotFound);
        }
        let snapshot = snapshot.unwrap();
        Ok(snapshot.ts())
    }


    pub fn insert<K: Key>(&mut self, key: &K, value: V) -> Result<(), TrieError> {
        let mut snapshots = self.tree.snapshots.lock().map_err(|_| TrieError::SnapshotMutexError)?;
        let snapshot = snapshots.get_mut(self.index);
        if snapshot.is_none() {
            return Err(TrieError::SnapshotNotFound);
        }
        let snapshot = snapshot.unwrap().as_mut();
        if snapshot.is_none() {
            return Err(TrieError::SnapshotNotFound);
        }
        let snapshot = snapshot.unwrap();
        snapshot.insert(key, value)?;
        Ok(())
    }


    pub fn close(&mut self) -> Result<(), TrieError>{
        self.tree.close(self.index)?;
        Ok(())
    }
}


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
    pub fn new_snapshot(snapshot_id: usize, root: Arc<Node<P, V>>) -> Snapshot<P, V> {
        Snapshot {
            id: snapshot_id,
            ts: root.ts() + 1,
            root: root,
            readers: HashMap::new(),
            max_reader_id: 0,
            closed: false,
            mutex: RwLock::new(()),
    }
    }


    pub fn insert<K: Key>(&mut self, key: &K, value: V) -> Result<(), TrieError> {
        let _guard = self.mutex.write().map_err(|_| TrieError::MutexError)?;

        // Create copies of the key and value to ensure immutability
        let k = &key.clone();
        let v = value.clone();

        // Insert the key-value pair into the root node
        let (new_node, _) = match Node::insert_recurse(&self.root, k, v, self.ts, 0) {
            Ok((new_node, old_node)) => (new_node, old_node),
            Err(err) => {
                return Err(err);
            }
        };

        // Update the root node
        self.root = new_node;

        Ok(())
    }

    pub fn get<K: Key>(&self, key: &K) -> Option<(V, &u64)> {
        let _guard = self.mutex.read().unwrap();
        let (value, ts) = Node::get_recurse(self.root.as_ref(), key)?;
        Some((value.clone(), ts))
    }

    pub fn ts(&self) -> u64 {
        let _guard = self.mutex.read().unwrap();
        self.root.ts()
    }

    pub fn close(&mut self) -> Result<(), TrieError> {
        let _guard = self.mutex.write().map_err(|_| TrieError::MutexError)?;

        if self.closed {
            return Err(TrieError::SnapshotAlreadyClosed);
        }

        if !self.readers.is_empty() {
            return Err(TrieError::SnapshotReadersNotClosed);
        }

        self.closed = true;

        Ok(())
    }
}