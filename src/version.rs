use std::sync::Arc;

use crate::node::LeafValue;

const B: usize = 6; // B-tree degree (max children = 2B)

#[derive(Clone)]
pub(crate) struct BTree<V: Clone> {
    root: Option<Arc<BNode<V>>>,
}

#[derive(Clone)]
pub(crate) struct BNode<V: Clone> {
    entries: Vec<Arc<LeafValue<V>>>,
    children: Vec<Arc<BNode<V>>>,
    is_leaf: bool,
}

impl<V: Clone> BNode<V> {
    fn new(is_leaf: bool) -> Self {
        BNode {
            entries: Vec::with_capacity(2 * B - 1),
            children: if is_leaf {
                Vec::new()
            } else {
                Vec::with_capacity(2 * B)
            },
            is_leaf,
        }
    }

    fn is_full(&self) -> bool {
        self.entries.len() >= 2 * B - 1
    }
}

impl<V: Clone> BTree<V> {
    pub fn new() -> Self {
        BTree { root: None }
    }

    pub fn insert(&mut self, value: V, version: u64, ts: u64) {
        let leaf_value = Arc::new(LeafValue::new(value, version, ts));
        match self.root.take() {
            None => {
                let mut root = BNode::new(true);
                root.entries.push(leaf_value);
                self.root = Some(Arc::new(root));
            }
            Some(root) => {
                if root.is_full() {
                    let mut new_root = BNode::new(false);
                    new_root.children.push(root);
                    self.split_child(&mut new_root, 0);
                    self.insert_non_full(&mut new_root, leaf_value);
                    self.root = Some(Arc::new(new_root));
                } else {
                    let mut root = (*root).clone();
                    self.insert_non_full(&mut root, leaf_value);
                    self.root = Some(Arc::new(root));
                }
            }
        }
    }

    fn split_child(&self, parent: &mut BNode<V>, index: usize) {
        let child = Arc::clone(&parent.children[index]);
        let mut new_child = BNode::new(child.is_leaf);

        let mid = (child.entries.len() - 1) / 2;
        new_child.entries = child.entries[mid + 1..].to_vec();
        let middle_entry = child.entries[mid].clone();
        let mut child = (*child).clone();
        child.entries.truncate(mid);

        if !child.is_leaf {
            let mid_child = (child.children.len() + 1) / 2;
            new_child.children = child.children[mid_child..].to_vec();
            child.children.truncate(mid_child);
        }

        parent.entries.insert(index, middle_entry);
        parent.children[index] = Arc::new(child);
        parent.children.insert(index + 1, Arc::new(new_child));
    }

    fn insert_non_full(&self, node: &mut BNode<V>, leaf_value: Arc<LeafValue<V>>) {
        let mut i = node.entries.len();

        if node.is_leaf {
            while i > 0
                && !self.should_go_right(&node.entries[i - 1], leaf_value.version, leaf_value.ts)
            {
                i -= 1;
            }
            node.entries.insert(i, leaf_value);
        } else {
            while i > 0
                && !self.should_go_right(&node.entries[i - 1], leaf_value.version, leaf_value.ts)
            {
                i -= 1;
            }

            let child = Arc::clone(&node.children[i]);
            if child.is_full() {
                self.split_child(node, i);
                if self.should_go_right(&node.entries[i], leaf_value.version, leaf_value.ts) {
                    i += 1;
                }
            }

            let mut child = (*node.children[i]).clone();
            self.insert_non_full(&mut child, leaf_value);
            node.children[i] = Arc::new(child);
        }
    }

    fn should_go_right(&self, entry: &LeafValue<V>, version: u64, ts: u64) -> bool {
        if version != entry.version {
            version > entry.version
        } else {
            ts > entry.ts
        }
    }

    pub fn search(&self, version: u64, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        let root = self.root.as_ref()?;
        self.search_node(root, version, ts)
    }

    fn search_node<'a>(
        &'a self,
        node: &'a BNode<V>,
        version: u64,
        ts: u64,
    ) -> Option<&'a Arc<LeafValue<V>>> {
        let mut i = 0;

        while i < node.entries.len() && self.should_go_right(&node.entries[i], version, ts) {
            i += 1;
        }

        if i < node.entries.len() && version == node.entries[i].version && ts == node.entries[i].ts
        {
            Some(&node.entries[i])
        } else if node.is_leaf {
            None
        } else {
            self.search_node(&node.children[i], version, ts)
        }
    }

    pub fn last_less_or_equal_ts(&self, ts: u64) -> Option<&Arc<LeafValue<V>>> {
        let root = self.root.as_ref()?;
        self.last_less_or_equal_ts_node(root, ts, None)
    }

    fn last_less_or_equal_ts_node<'a>(
        &'a self,
        node: &'a BNode<V>,
        ts: u64,
        mut best_so_far: Option<&'a Arc<LeafValue<V>>>,
    ) -> Option<&'a Arc<LeafValue<V>>> {
        for entry in &node.entries {
            if entry.ts <= ts {
                match best_so_far {
                    None => best_so_far = Some(entry),
                    Some(best) if entry.ts > best.ts => best_so_far = Some(entry),
                    _ => {}
                }
            }
        }

        if !node.is_leaf {
            for child in &node.children {
                best_so_far = self.last_less_or_equal_ts_node(child, ts, best_so_far);
            }
        }

        best_so_far
    }

    // Add an iterator that yields Arc<LeafValue<V>> references
    pub fn iter(&self) -> Box<dyn DoubleEndedIterator<Item = &Arc<LeafValue<V>>> + '_> {
        match &self.root {
            None => Box::new(std::iter::empty()),
            Some(root) => Box::new(BNodeIterator::new(root)),
        }
    }

    pub fn clear(&mut self) {
        self.root = None;
    }
}

// Iterator for BNode
struct BNodeIterator<'a, V: Clone> {
    stack: Vec<(&'a BNode<V>, usize)>,
    reverse_stack: Vec<(&'a BNode<V>, usize)>,
}

impl<'a, V: Clone> BNodeIterator<'a, V> {
    fn new(root: &'a Arc<BNode<V>>) -> Self {
        let mut iter = BNodeIterator {
            stack: Vec::new(),
            reverse_stack: Vec::new(),
        };
        iter.push_left(root);
        iter.push_right(root);
        iter
    }

    fn push_left(&mut self, node: &'a Arc<BNode<V>>) {
        let mut current = node;
        while let Some(first_child) = current.children.first() {
            self.stack.push((current, 0));
            current = first_child;
        }
        self.stack.push((current, 0));
    }

    fn push_right(&mut self, node: &'a Arc<BNode<V>>) {
        let mut current = node;
        while let Some(last_child) = current.children.last() {
            self.reverse_stack.push((current, current.entries.len()));
            current = last_child;
        }
        self.reverse_stack.push((current, current.entries.len()));
    }
}

impl<'a, V: Clone> Iterator for BNodeIterator<'a, V> {
    type Item = &'a Arc<LeafValue<V>>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, index)) = self.stack.pop() {
            if index < node.entries.len() {
                if index + 1 < node.entries.len() {
                    self.stack.push((node, index + 1));
                } else if let Some(next_child) = node.children.get(index + 1) {
                    self.push_left(next_child);
                }
                return Some(&node.entries[index]);
            }
        }
        None
    }
}

impl<'a, V: Clone> DoubleEndedIterator for BNodeIterator<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((node, index)) = self.reverse_stack.pop() {
            if index > 0 {
                if index - 1 > 0 {
                    self.reverse_stack.push((node, index - 1));
                } else if let Some(prev_child) = node.children.get(index - 1) {
                    self.push_right(prev_child);
                }
                return Some(&node.entries[index - 1]);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_btree_basic_insert() {
        let mut tree = BTree::<i32>::new();
        tree.insert(42, 1, 100);

        let result = tree.search(1, 100);
        assert_eq!(result.map(|leaf| &leaf.value), Some(&42));
    }

    #[test]
    fn test_btree_multiple_versions() {
        let mut tree = BTree::<i32>::new();
        tree.insert(10, 1, 100);
        tree.insert(20, 2, 200);
        tree.insert(30, 3, 300);

        assert_eq!(tree.search(1, 100).map(|leaf| &leaf.value), Some(&10));
        assert_eq!(tree.search(2, 200).map(|leaf| &leaf.value), Some(&20));
        assert_eq!(tree.search(3, 300).map(|leaf| &leaf.value), Some(&30));
    }

    #[test]
    fn test_btree_same_version_different_ts() {
        let mut tree = BTree::<i32>::new();
        tree.insert(10, 1, 200);
        tree.insert(20, 1, 100);

        let result = tree.last_less_or_equal_ts(150);
        assert_eq!(
            result.map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((20, 1, 100))
        );

        let result = tree.last_less_or_equal_ts(300);
        assert_eq!(
            result.map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((10, 1, 200))
        );
    }

    #[test]
    fn test_btree_full_node_split() {
        let mut tree = BTree::<i32>::new();
        // Insert 2*B entries to force splits
        for i in 0..2 * B {
            tree.insert(i as i32, i as u64, i as u64);
        }

        // Verify all entries are still accessible
        for i in 0..2 * B {
            assert_eq!(
                tree.search(i as u64, i as u64).map(|leaf| leaf.value),
                Some(i as i32)
            );
        }
    }

    #[test]
    fn test_btree_timestamp_queries() {
        let mut tree = BTree::<i32>::new();
        tree.insert(10, 1, 100);
        tree.insert(20, 1, 200);
        tree.insert(30, 1, 300);
        tree.insert(40, 1, 400);

        // Test last_less_or_equal_ts
        assert!(tree.last_less_or_equal_ts(50).is_none());
        assert_eq!(
            tree.last_less_or_equal_ts(150)
                .map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((10, 1, 100))
        );
        assert_eq!(
            tree.last_less_or_equal_ts(250)
                .map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((20, 1, 200))
        );
        assert_eq!(
            tree.last_less_or_equal_ts(350)
                .map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((30, 1, 300))
        );
        assert_eq!(
            tree.last_less_or_equal_ts(500)
                .map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((40, 1, 400))
        );
    }

    #[test]
    fn test_btree_copy_on_write() {
        let mut tree1 = BTree::<i32>::new();
        tree1.insert(10, 1, 100);

        let tree2 = tree1.clone();
        tree1.insert(20, 2, 200);

        // Original version should be preserved in tree2
        assert_eq!(tree2.search(1, 100).map(|leaf| leaf.value), Some(10));
        assert!(tree2.search(2, 200).is_none());

        // New version should be available in tree1
        assert_eq!(tree1.search(1, 100).map(|leaf| leaf.value), Some(10));
        assert_eq!(tree1.search(2, 200).map(|leaf| leaf.value), Some(20));
    }

    #[test]
    fn test_btree_decreasing_timestamps() {
        let mut tree = BTree::<i32>::new();
        tree.insert(10, 1, 200);
        tree.insert(20, 2, 100);

        let result = tree.last_less_or_equal_ts(100);
        assert_eq!(
            result.map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((20, 2, 100))
        );

        let result = tree.last_less_or_equal_ts(200);
        assert_eq!(
            result.map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((10, 1, 200))
        );
    }

    #[test]
    fn test_btree_large_dataset() {
        let mut tree = BTree::<i32>::new();
        for i in 0..1000 {
            tree.insert(i, i as u64, (i * 2) as u64);
        }

        // Test random access
        assert_eq!(tree.search(500, 1000).map(|leaf| leaf.value), Some(500));

        // Test timestamp queries
        assert_eq!(
            tree.last_less_or_equal_ts(1500)
                .map(|leaf| (leaf.value, leaf.version, leaf.ts)),
            Some((750, 750, 1500))
        );
    }

    #[test]
    fn test_btree_empty() {
        let tree: BTree<i32> = BTree::new();
        assert!(tree.search(1, 100).is_none());
        assert!(tree.last_less_or_equal_ts(100).is_none());
    }

    #[test]
    fn test_btree_overwrite_version_ts() {
        let mut tree = BTree::<i32>::new();
        tree.insert(10, 1, 100);
        tree.insert(20, 1, 100); // Same version and timestamp

        assert_eq!(tree.search(1, 100).map(|leaf| leaf.value), Some(20)); // Should have latest value
    }

    #[test]
    fn test_btree_concurrent_versions() {
        use std::thread;

        let tree = Arc::new(std::sync::Mutex::new(BTree::<i32>::new()));
        let mut handles = vec![];

        for i in 0..10 {
            let tree_clone = Arc::clone(&tree);
            let handle = thread::spawn(move || {
                let mut tree = tree_clone.lock().unwrap();
                tree.insert(i, i as u64, (i * 10) as u64);
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let final_tree = tree.lock().unwrap();
        for i in 0..10 {
            assert!(final_tree.search(i as u64, (i * 10) as u64).is_some());
        }
    }

    #[test]
    fn test_btree_insert_at_same_version() {
        let mut tree = BTree::<i32>::new();

        let ts = 100;
        tree.insert(10, 1, ts);
        tree.insert(20, 1, ts);

        let val = tree
        .iter()
        .filter(|value| {
            let should_include = value.ts <= ts;
            if should_include {
                println!("Version: {:?}, TS: {}", value.version, value.ts);
            }
            should_include
        })
        .max_by_key(|value| value.ts).unwrap();
        println!("Max value: {:?}", val.value);


        assert_eq!(tree.search(1, ts).map(|leaf| &leaf.value), Some(&20));
    }

}
