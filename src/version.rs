use crate::node::LeafValue;
use std::sync::Arc;

const B: usize = 8;

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

#[allow(unused)]
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

    #[inline]
    fn is_full(&self) -> bool {
        self.entries.len() >= 2 * B - 1
    }
}

#[allow(unused)]
impl<V: Clone> BTree<V> {
    pub fn new() -> Self {
        BTree { root: None }
    }

    #[inline]
    pub fn insert(&mut self, value: V, version: u64, ts: u64) {
        let leaf_value = Arc::new(LeafValue::new(value, version, ts));

        if let Some(root) = self.root.take() {
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
        } else {
            let mut root = BNode::new(true);
            root.entries.push(leaf_value);
            self.root = Some(Arc::new(root));
        }
    }

    fn split_child(&self, parent: &mut BNode<V>, index: usize) {
        let (parent_entries, parent_children) = (&mut parent.entries, &mut parent.children);
        let child = Arc::make_mut(&mut parent_children[index]);
        let mut new_child = BNode::new(child.is_leaf);

        // Calculate split points
        let mid = (child.entries.len() - 1) / 2;
        let mid_child = if child.is_leaf {
            0
        } else {
            (child.children.len() + 1) / 2
        };

        // Move entries and children in one go
        new_child.entries = child.entries.split_off(mid + 1);
        if !child.is_leaf {
            new_child.children = child.children.split_off(mid_child);
        }

        // Insert middle entry into parent
        let middle_entry = child.entries.pop().unwrap();
        parent_entries.insert(index, middle_entry);
        parent_children.insert(index + 1, Arc::new(new_child));
    }

    #[inline]
    fn should_go_right(&self, entry: &LeafValue<V>, version: u64, ts: u64) -> bool {
        if version != entry.version {
            version > entry.version
        } else {
            ts > entry.ts
        }
    }

    fn insert_non_full(&self, node: &mut BNode<V>, leaf_value: Arc<LeafValue<V>>) {
        let mut pos = node.entries.partition_point(|entry| {
            self.should_go_right(entry, leaf_value.version, leaf_value.ts)
        });

        if node.is_leaf {
            node.entries.insert(pos, leaf_value);
            return;
        }

        let child = Arc::make_mut(&mut node.children[pos]);
        if child.is_full() {
            self.split_child(node, pos);
            if self.should_go_right(&node.entries[pos], leaf_value.version, leaf_value.ts) {
                pos += 1;
            }
        }

        let child = Arc::make_mut(&mut node.children[pos]);
        self.insert_non_full(child, leaf_value);
    }

    #[allow(unused)]
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
        let pos = node
            .entries
            .partition_point(|entry| self.should_go_right(entry, version, ts));

        if pos < node.entries.len()
            && version == node.entries[pos].version
            && ts == node.entries[pos].ts
        {
            Some(&node.entries[pos])
        } else if node.is_leaf {
            None
        } else {
            self.search_node(&node.children[pos], version, ts)
        }
    }

    #[inline]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Arc<LeafValue<V>>> + '_ {
        BNodeIterator::new(self.root.as_ref())
    }

    pub fn clear(&mut self) {
        self.root = None;
    }
}

struct BNodeIterator<'a, V: Clone> {
    forward_stack: Vec<(&'a BNode<V>, usize)>,
    reverse_stack: Vec<(&'a BNode<V>, usize)>,
}

impl<'a, V: Clone> BNodeIterator<'a, V> {
    fn new(root: Option<&'a Arc<BNode<V>>>) -> Self {
        let mut iter = BNodeIterator {
            forward_stack: Vec::new(),
            reverse_stack: Vec::new(),
        };
        if let Some(root) = root {
            iter.push_leftmost(root);
            iter.push_rightmost(root);
        }
        iter
    }

    fn push_leftmost(&mut self, node: &'a BNode<V>) {
        let mut current = node;
        loop {
            self.forward_stack.push((current, 0));
            if current.is_leaf || current.children.is_empty() {
                break;
            }
            current = &current.children[0];
        }
    }

    fn push_rightmost(&mut self, node: &'a BNode<V>) {
        let mut current = node;
        loop {
            self.reverse_stack.push((current, current.entries.len()));
            if current.is_leaf || current.children.is_empty() {
                break;
            }
            current = &current.children[current.children.len() - 1];
        }
    }
}

impl<'a, V: Clone> Iterator for BNodeIterator<'a, V> {
    type Item = &'a Arc<LeafValue<V>>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, idx)) = self.forward_stack.last_mut() {
            if *idx < node.entries.len() {
                let entry = &node.entries[*idx];
                *idx += 1;

                if *idx == node.entries.len() && !node.is_leaf {
                    if let Some(next_child) = node.children.get(*idx) {
                        self.push_leftmost(next_child);
                    }
                }

                return Some(entry);
            }
            self.forward_stack.pop();
        }
        None
    }
}

impl<V: Clone> DoubleEndedIterator for BNodeIterator<'_, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((node, idx)) = self.reverse_stack.last_mut() {
            if *idx > 0 {
                *idx -= 1;
                let entry = &node.entries[*idx];

                if *idx == 0 && !node.is_leaf {
                    if let Some(prev_child) = node.children.get(*idx) {
                        self.push_rightmost(prev_child);
                    }
                }

                return Some(entry);
            }
            self.reverse_stack.pop();
        }
        None
    }
}

pub(crate) trait VersionStore<V: Clone> {
    fn new() -> Self;
    fn insert(&mut self, value: V, version: u64, ts: u64);
    fn clear(&mut self);
    fn iter(&self) -> Box<dyn DoubleEndedIterator<Item = &Arc<LeafValue<V>>> + '_>;
}

// Implement for Vec
#[cfg(feature = "vec_store")]
#[derive(Clone)]
pub(crate) struct VecStore<V: Clone> {
    values: Vec<Arc<LeafValue<V>>>,
}

#[cfg(feature = "vec_store")]
impl<V: Clone> VersionStore<V> for VecStore<V> {
    fn new() -> Self {
        Self { values: Vec::new() }
    }

    fn insert(&mut self, value: V, version: u64, ts: u64) {
        let new_leaf_value = LeafValue::new(value, version, ts);
        match self
            .values
            .binary_search_by(|v| v.version.cmp(&new_leaf_value.version))
        {
            Ok(index) => {
                if self.values[index].ts == ts {
                    self.values[index] = Arc::new(new_leaf_value);
                } else {
                    let mut insert_position = index;
                    if self.values[index].ts < ts {
                        insert_position += self.values[index..]
                            .iter()
                            .take_while(|v| v.ts <= ts)
                            .count();
                    } else {
                        insert_position -= self.values[..index]
                            .iter()
                            .rev()
                            .take_while(|v| v.ts >= ts)
                            .count();
                    }
                    self.values
                        .insert(insert_position, Arc::new(new_leaf_value));
                }
            }
            Err(index) => {
                self.values.insert(index, Arc::new(new_leaf_value));
            }
        }
    }

    fn clear(&mut self) {
        self.values.clear();
    }

    fn iter(&self) -> Box<dyn DoubleEndedIterator<Item = &Arc<LeafValue<V>>> + '_> {
        Box::new(self.values.iter())
    }
}

// Implement for BTree
#[cfg(feature = "btree_store")]
#[derive(Clone)]
pub(crate) struct BTreeStore<V: Clone> {
    values: BTree<V>,
}

#[cfg(feature = "btree_store")]
impl<V: Clone> VersionStore<V> for BTreeStore<V> {
    fn new() -> Self {
        Self {
            values: BTree::new(),
        }
    }

    fn insert(&mut self, value: V, version: u64, ts: u64) {
        self.values.insert(value, version, ts);
    }

    fn clear(&mut self) {
        self.values.clear();
    }

    fn iter(&self) -> Box<dyn DoubleEndedIterator<Item = &Arc<LeafValue<V>>> + '_> {
        Box::new(self.values.iter())
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

        let max_val = tree
            .iter()
            .filter(|value| value.ts <= ts)
            .max_by(|a, b| {
                a.ts.cmp(&b.ts).then_with(|| std::cmp::Ordering::Greater) // Always prefer the second entry
            })
            .unwrap();

        assert_eq!(max_val.value, 20);
        assert_eq!(tree.search(1, ts).map(|leaf| &leaf.value), Some(&20));
    }
}
