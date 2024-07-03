//! This module defines the Snapshot struct for managing snapshots within a Trie structure.
use std::ops::RangeBounds;
use std::sync::Arc;

use crate::art::{Node, QueryType, Tree};
use crate::iter::{query_keys_at_node, scan_node, Iter, Range, VersionedIter};
use crate::node::Version;
use crate::{KeyTrait, TrieError};

#[derive(Clone)]
/// Represents a snapshot of the data within the Trie.
pub struct Snapshot<P: KeyTrait, V: Clone> {
    pub(crate) ts: u64,
    pub(crate) root: Option<Arc<Node<P, V>>>,
}

impl<P: KeyTrait, V: Clone> Snapshot<P, V> {
    /// Creates a new Snapshot instance with the provided snapshot_id and root node.
    pub(crate) fn new(root: Option<Arc<Node<P, V>>>, ts: u64) -> Self {
        Snapshot { ts, root }
    }

    /// Inserts a key-value pair into the snapshot.
    pub fn insert(&mut self, key: &P, value: V, ts: u64) -> Result<(), TrieError> {
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

    /// Retrieves the value, version and timestamp associated with the given key from the snapshot.
    pub fn get(&self, key: &P) -> Result<(V, u64, u64), TrieError> {
        // Use a recursive function to get the value and timestamp from the root node
        match self.root.as_ref() {
            Some(root) => Node::get_recurse(root, key, QueryType::LatestByVersion(root.version())),
            None => Err(TrieError::KeyNotFound),
        }
    }

    /// Retrieves the value, version associated with the given key from the snapshot at the specified timestamp.
    pub fn get_at_ts(&self, key: &P, ts: u64) -> Result<(V, u64), TrieError> {
        match self.root.as_ref() {
            Some(root) => Node::get_recurse(root, key, QueryType::LatestByTs(ts))
                .map(|(value, version, _)| (value, version)),
            None => Err(TrieError::KeyNotFound),
        }
    }

    /// Retrieves the version history of the key from the snapshot.
    pub fn get_version_history(&self, key: &P) -> Result<Vec<(V, u64, u64)>, TrieError> {
        match self.root.as_ref() {
            Some(root) => {
                // Directly return the Result from Node::get_all_versions
                Node::get_version_history(root, key)
            }
            None => Err(TrieError::KeyNotFound),
        }
    }

    /// Returns the version of the snapshot.
    pub fn version(&self) -> u64 {
        self.root.as_ref().map_or(0, |root| root.version())
    }

    pub fn remove(&mut self, key: &P) -> Result<bool, TrieError> {
        let (new_root, is_deleted) = Tree::remove_from_node(self.root.as_ref(), key);

        self.root = new_root;
        Ok(is_deleted)
    }

    pub fn ts(&self) -> u64 {
        self.ts
    }

    pub fn iter(&self) -> Result<Iter<P, V>, TrieError> {
        Ok(Iter::new(self.root.as_ref()))
    }

    /// Returns an iterator over all versions of the key-value pairs within the Trie.
    pub fn iter_with_versions(&self) -> Result<VersionedIter<P, V>, TrieError> {
        Ok(VersionedIter::new(self.root.as_ref()))
    }

    /// Returns a range query iterator over the Trie.
    pub fn range<'a, R>(
        &'a self,
        range: R,
    ) -> Result<impl Iterator<Item = (Vec<u8>, &'a V, &'a u64, &'a u64)>, TrieError>
    where
        R: RangeBounds<P> + 'a,
    {
        Ok(Range::new(self.root.as_ref(), range))
    }

    /// Returns a versioned range query iterator over the Trie.
    pub fn range_with_versions<'a, R>(
        &'a self,
        range: R,
    ) -> Result<impl Iterator<Item = (Vec<u8>, &'a V, &'a u64, &'a u64)>, TrieError>
    where
        R: RangeBounds<P> + 'a,
    {
        Ok(Range::new_versioned(self.root.as_ref(), range))
    }

    pub fn get_value_by_query(
        &self,
        key: &P,
        query_type: QueryType,
    ) -> Result<(V, u64, u64), TrieError> {
        match self.root.as_ref() {
            Some(root) => Node::get_recurse(root, key, query_type),
            None => Err(TrieError::KeyNotFound),
        }
    }

    pub fn scan_at_ts<R>(&self, range: R, ts: u64) -> Result<Vec<(Vec<u8>, V)>, TrieError>
    where
        R: RangeBounds<P>,
    {
        Ok(scan_node(
            self.root.as_ref(),
            range,
            QueryType::LatestByTs(ts),
        ))
    }

    pub fn keys_at_ts<R>(&self, range: R, ts: u64) -> Result<Vec<Vec<u8>>, TrieError>
    where
        R: RangeBounds<P>,
    {
        Ok(query_keys_at_node(
            self.root.as_ref(),
            range,
            QueryType::LatestByTs(ts),
        ))
    }
}

#[cfg(test)]
mod tests {
    use crate::art::QueryType;
    use crate::art::Tree;
    use crate::iter::Iter;
    use crate::KeyTrait;
    use crate::TrieError;
    use crate::VariableSizeKey;

    use std::ops::RangeFull;
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

        {
            // Reader
            let mut reader = snap.iter().unwrap();
            assert_eq!(count_items(&mut reader), 4);
        }
    }

    fn count_items<P: KeyTrait, V: Clone>(reader: &mut Iter<P, V>) -> usize {
        let mut len = 0;
        for _ in reader {
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

    #[test]
    fn test_get_at_ts_successful_retrieval() {
        let tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value = 10;
        let ts = 100;
        snapshot.insert(&key, value, ts).unwrap();

        let (retrieved_value, retrieved_version) = snapshot.get_at_ts(&key, ts).unwrap();
        assert_eq!(retrieved_value, value);
        assert_eq!(retrieved_version, 1);
    }

    #[test]
    fn test_get_at_ts_key_not_found() {
        let tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("nonexistent_key").unwrap();
        let result = snapshot.get_at_ts(&key, 100);
        assert!(matches!(result, Err(TrieError::KeyNotFound)));
    }

    #[test]
    fn test_get_at_ts_timestamp_before_insertion() {
        let tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value = 10;
        let ts = 100;
        snapshot.insert(&key, value, ts).unwrap();

        let result = snapshot.get_at_ts(&key, ts - 1);
        assert!(matches!(result, Err(TrieError::KeyNotFound)));
    }

    #[test]
    fn test_get_at_ts_multiple_versions() {
        let tree: Tree<VariableSizeKey, i32> = Tree::<VariableSizeKey, i32>::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value1 = 10;
        let value2 = 11;
        let ts1 = 100;
        let ts2 = 200;
        snapshot.insert(&key, value1, ts1).unwrap();
        snapshot.insert(&key, value2, ts2).unwrap();

        let (retrieved_value, _) = snapshot.get_at_ts(&key, ts2).unwrap();
        assert_eq!(retrieved_value, value2);
    }

    #[test]
    fn test_retrieving_value_at_timestamp_between_two_inserts() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value1 = 10;
        let value2 = 20;
        let ts1 = 100;
        let ts2 = 200;
        let ts_query = 150;
        snapshot.insert(&key, value1, ts1).unwrap();
        snapshot.insert(&key, value2, ts2).unwrap();

        let (retrieved_value, _) = snapshot.get_at_ts(&key, ts_query).unwrap();
        assert_eq!(retrieved_value, value1);
    }

    #[test]
    fn test_inserting_and_retrieving_with_same_timestamp() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value1 = 10;
        let value2 = 20;
        let ts = 100;
        snapshot.insert(&key, value1, ts).unwrap();
        snapshot.insert(&key, value2, ts).unwrap();

        let (retrieved_value, _) = snapshot.get_at_ts(&key, ts).unwrap();
        assert_eq!(retrieved_value, value2);
    }

    #[test]
    fn test_retrieving_value_at_future_timestamp() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value = 10;
        let ts_insert = 100;
        let ts_future = 200;
        snapshot.insert(&key, value, ts_insert).unwrap();

        let (retrieved_value, _) = snapshot.get_at_ts(&key, ts_future).unwrap();
        assert_eq!(retrieved_value, value);
    }

    #[test]
    fn test_inserting_values_with_decreasing_timestamps() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value1 = 10;
        let value2 = 20;
        let ts1 = 200;
        let ts2 = 100;
        snapshot.insert(&key, value1, ts1).unwrap();
        snapshot.insert(&key, value2, ts2).unwrap();

        let (retrieved_value_early, _) = snapshot.get_at_ts(&key, ts2).unwrap();
        let (retrieved_value_late, _) = snapshot.get_at_ts(&key, ts1).unwrap();
        assert_eq!(retrieved_value_early, value2);
        assert_eq!(retrieved_value_late, value1);
    }

    #[test]
    fn test_retrieving_value_after_deleting_it() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        let value = 10;
        let ts_insert = 100;
        let ts_query = 150;
        snapshot.insert(&key, value, ts_insert).unwrap();
        snapshot.remove(&key).unwrap();

        let result = snapshot.get_at_ts(&key, ts_query);
        assert!(result.is_err());
    }

    #[test]
    fn test_get_all_versions() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();

        // Scenario 1: Insert multiple values for the same key with different timestamps
        let key1 = VariableSizeKey::from_str("test_key1").unwrap();
        let value1_1 = 10;
        let value1_2 = 20;
        let ts1_1 = 100;
        let ts1_2 = 200;
        snapshot.insert(&key1, value1_1, ts1_1).unwrap();
        snapshot.insert(&key1, value1_2, ts1_2).unwrap();

        let history1 = snapshot.get_version_history(&key1).unwrap();
        assert_eq!(history1.len(), 2);

        let (retrieved_value1_1, v1_1, t1_1) = history1[0];
        assert_eq!(retrieved_value1_1, value1_1);
        assert_eq!(v1_1, 1);
        assert_eq!(t1_1, ts1_1);

        let (retrieved_value1_2, v1_2, t1_2) = history1[1];
        assert_eq!(retrieved_value1_2, value1_2);
        assert_eq!(v1_2, 1);
        assert_eq!(t1_2, ts1_2);

        // Scenario 2: Insert values for different keys
        let key2 = VariableSizeKey::from_str("test_key2").unwrap();
        let value2 = 30;
        let ts2 = 300;
        snapshot.insert(&key2, value2, ts2).unwrap();

        let history2 = snapshot.get_version_history(&key2).unwrap();
        assert_eq!(history2.len(), 1);

        let (retrieved_value2, v2, t2) = history2[0];
        assert_eq!(retrieved_value2, value2);
        assert_eq!(v2, 1);
        assert_eq!(t2, ts2);

        // Scenario 3: Ensure no history for a non-existent key
        let key3 = VariableSizeKey::from_str("non_existent_key").unwrap();
        assert!(snapshot.get_version_history(&key3).is_err());
    }

    #[test]
    fn test_latest_by_version() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        snapshot.insert(&key, 10, 1).unwrap();
        snapshot.insert(&key, 20, 2).unwrap();
        snapshot.insert(&key, 30, 3).unwrap();

        let query_type = QueryType::LatestByVersion(3);
        let result = snapshot.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (30, 1, 3));
    }

    #[test]
    fn test_latest_by_ts() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        snapshot.insert(&key, 10, 1).unwrap();
        snapshot.insert(&key, 20, 2).unwrap();
        snapshot.insert(&key, 30, 3).unwrap();

        let query_type = QueryType::LatestByTs(300);
        let result = snapshot.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (30, 1, 3));
    }

    #[test]
    fn test_last_less_than_ts() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        snapshot.insert(&key, 10, 100).unwrap();
        snapshot.insert(&key, 20, 150).unwrap();
        snapshot.insert(&key, 30, 300).unwrap();

        let query_type = QueryType::LastLessThanTs(150);
        let result = snapshot.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (10, 1, 100));
    }

    #[test]
    fn test_last_less_or_equal_ts() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        snapshot.insert(&key, 10, 100).unwrap();
        snapshot.insert(&key, 20, 150).unwrap();
        snapshot.insert(&key, 30, 300).unwrap();

        let query_type = QueryType::LastLessOrEqualTs(150);
        let result = snapshot.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (20, 1, 150));
    }

    #[test]
    fn test_first_greater_than_ts() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        snapshot.insert(&key, 10, 100).unwrap();
        snapshot.insert(&key, 20, 150).unwrap();
        snapshot.insert(&key, 30, 300).unwrap();

        let query_type = QueryType::FirstGreaterThanTs(150);
        let result = snapshot.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (30, 1, 300));
    }

    #[test]
    fn test_first_greater_or_equal_ts() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let mut snapshot = tree.create_snapshot().unwrap();
        let key = VariableSizeKey::from_str("test_key").unwrap();
        snapshot.insert(&key, 10, 100).unwrap();
        snapshot.insert(&key, 20, 150).unwrap();
        snapshot.insert(&key, 30, 300).unwrap();

        let query_type = QueryType::FirstGreaterOrEqualTs(150);
        let result = snapshot.get_value_by_query(&key, query_type).unwrap();
        assert_eq!(result, (20, 1, 150));
    }

    #[test]
    fn scan_empty_range() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let snap = tree.create_snapshot().unwrap();
        let result = snap.scan_at_ts(RangeFull {}, 0);
        assert!(result.is_ok());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn scan_range_includes_some_keys() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        let keys = ["key_1", "key_2", "key_3"];
        for key in keys.iter() {
            tree.insert(&VariableSizeKey::from_str(key).unwrap(), 1, 0, 0)
                .unwrap();
        }
        let snap = tree.create_snapshot().unwrap();
        let range = VariableSizeKey::from_slice_with_termination("key_1".as_bytes())
            ..=VariableSizeKey::from_slice_with_termination("key_2".as_bytes());
        let result = snap.scan_at_ts(range, 0);
        assert!(result.is_ok());
        let values = result.unwrap();
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
        let snap = tree.create_snapshot().unwrap();
        let result = snap.scan_at_ts(RangeFull {}, 0);
        assert!(result.is_ok());
        let values = result.unwrap();
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
        let snap = tree.create_snapshot().unwrap();
        let range = VariableSizeKey::from_slice_with_termination("key_4".as_bytes())
            ..VariableSizeKey::from_slice_with_termination("key_5".as_bytes());
        let result = snap.scan_at_ts(range, 0);
        assert!(result.is_ok());
        let values = result.unwrap();
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
        let snap = tree.create_snapshot().unwrap();
        for (i, _) in keys.iter().enumerate() {
            let result = snap.scan_at_ts(RangeFull {}, i as u64);
            assert!(result.is_ok());
            let values = result.unwrap();
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

        let snap = tree.create_snapshot().unwrap();
        let result = snap.scan_at_ts(RangeFull {}, num_keys);
        assert!(result.is_ok());
        let values = result.unwrap();
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

        let snap = tree.create_snapshot().unwrap();
        // Scan at a timestamp before any insertions
        let result_before = snap.scan_at_ts(RangeFull {}, 0);
        assert!(result_before.is_ok());
        assert!(result_before.unwrap().is_empty());

        // Scan between insertions
        let result_mid = snap.scan_at_ts(RangeFull {}, 4);
        assert!(result_mid.is_ok());
        assert_eq!(result_mid.unwrap().len(), 2); // Expect first two keys to be visible

        // Scan after all insertions
        let result_after = snap.scan_at_ts(RangeFull {}, 7);
        assert!(result_after.is_ok());
        assert_eq!(result_after.unwrap().len(), keys.len()); // Expect all keys to be visible
    }

    #[test]
    fn scan_with_single_item_in_snapshot() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        // Insert a single item into the tree
        tree.insert(&VariableSizeKey::from_str("key_1").unwrap(), 42, 0, 0)
            .unwrap();

        let snap = tree.create_snapshot().unwrap();
        let result = snap.scan_at_ts(RangeFull {}, 0);
        assert!(result.is_ok());
        let values = result.unwrap();

        assert_eq!(values.len(), 1);
        assert_eq!(values[0].1, 42);
    }

    #[test]
    fn keys_at_empty_range() {
        let tree: Tree<VariableSizeKey, i32> = Tree::new();
        let snap = tree.create_snapshot().unwrap();
        let keys = snap.keys_at_ts(RangeFull {}, 0).unwrap();
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
        let snap = tree.create_snapshot().unwrap();
        let range = VariableSizeKey::from_slice_with_termination("key_1".as_bytes())
            ..=VariableSizeKey::from_slice_with_termination("key_2".as_bytes());
        let keys = snap.keys_at_ts(range, 0).unwrap();
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
        let snap = tree.create_snapshot().unwrap();
        let keys = snap.keys_at_ts(RangeFull {}, 0).unwrap();
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
        let snap = tree.create_snapshot().unwrap();
        let range = VariableSizeKey::from("key_4".as_bytes().to_vec())
            ..VariableSizeKey::from("key_5".as_bytes().to_vec());
        let keys = snap.keys_at_ts(range, 0).unwrap();
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
        let snap = tree.create_snapshot().unwrap();
        for (i, _) in keys_to_insert.iter().enumerate() {
            let keys = snap.keys_at_ts(RangeFull {}, i as u64).unwrap();
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

        let snap = tree.create_snapshot().unwrap();
        let keys = snap.keys_at_ts(RangeFull {}, num_keys).unwrap();
        assert_eq!(keys.len(), num_keys as usize); // Expect all keys to be visible

        // Sort the expected keys lexicographically
        expected_keys.sort();

        // Verify each key is proper
        for (expected_key, key) in expected_keys.iter().zip(keys.iter()) {
            assert_eq!(key, expected_key.to_slice());
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

        let snap = tree.create_snapshot().unwrap();
        let keys_before = snap.keys_at_ts(RangeFull {}, 0).unwrap();
        assert!(keys_before.is_empty());

        let keys_mid = snap.keys_at_ts(RangeFull {}, 4).unwrap();
        assert_eq!(keys_mid.len(), 2); // Expect first two keys to be visible

        let keys_after = snap.keys_at_ts(RangeFull {}, 7).unwrap();
        assert_eq!(keys_after.len(), keys_to_insert.len()); // Expect all keys to be visible
    }

    #[test]
    fn keys_at_with_single_item_in_snapshot() {
        let mut tree: Tree<VariableSizeKey, i32> = Tree::new();
        tree.insert(&VariableSizeKey::from_str("key_1").unwrap(), 42, 0, 0)
            .unwrap();

        let snap = tree.create_snapshot().unwrap();
        let keys = snap.keys_at_ts(RangeFull {}, 0).unwrap();
        assert_eq!(keys.len(), 1);
    }
}
