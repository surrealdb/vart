use std::collections::{Bound, VecDeque};
use std::sync::Arc;

use crate::art::{Node, NodeType, TrieError};
use crate::snapshot::Snapshot;
use crate::{Key, Prefix, PrefixTrait};

pub struct Leaf<'a, K: Prefix + Clone, V: Clone> {
    pub(crate) key: &'a K,
    pub(crate) value: &'a V,
    pub(crate) ts: &'a u64,
}

impl<'a, K: Prefix + Clone, V: Clone> Leaf<'a, K, V> {
    pub fn new(key: &'a K, value: &'a V, ts: &'a u64) -> Self {
        Self { key, value, ts }
    }
}

// TODO: need to add more tests for snapshot readers
pub struct IterationPointer<'a, P: PrefixTrait, V: Clone> {
    id: u64,
    root: Arc<Node<P, V>>,
    snap: &'a Snapshot<P, V>,
}

impl<'a, P: PrefixTrait, V: Clone> IterationPointer<'a, P, V> {
    pub fn new(
        snap: &'a Snapshot<P, V>,
        root: Arc<Node<P, V>>,
        id: u64,
    ) -> IterationPointer<'a, P, V> {
        IterationPointer { id, root, snap }
    }

    pub fn iter(&self) -> Iter<P, V> {
        Iter::new(Some(&self.root))
    }

    pub fn close(&mut self) -> Result<(), TrieError> {
        // Call the close method of the Tree with the id of the snapshot to close it
        self.snap.close_reader(self.id)?;
        Ok(())
    }
}

pub struct NodeIter<'a, P: PrefixTrait, V: Clone> {
    node: Box<dyn Iterator<Item = (u8, &'a Arc<Node<P, V>>)> + 'a>,
}

impl<'a, P: PrefixTrait, V: Clone> NodeIter<'a, P, V> {
    fn new<I>(iter: I) -> Self
    where
        I: Iterator<Item = (u8, &'a Arc<Node<P, V>>)> + 'a,
    {
        Self {
            node: Box::new(iter),
        }
    }
}

impl<'a, P: PrefixTrait, V: Clone> Iterator for NodeIter<'a, P, V> {
    type Item = (u8, &'a Arc<Node<P, V>>);

    fn next(&mut self) -> Option<Self::Item> {
        self.node.next()
    }
}

pub struct Iter<'a, P: PrefixTrait + 'a, V: Clone> {
    inner: Box<dyn Iterator<Item = (Vec<u8>, &'a V, &'a u64)> + 'a>,
    _marker: std::marker::PhantomData<P>,
}

impl<'a, P: PrefixTrait + 'a, V: Clone> Iter<'a, P, V> {
    pub(crate) fn new(node: Option<&'a Arc<Node<P, V>>>) -> Self {
        if let Some(node) = node {
            Self {
                inner: Box::new(IterState::new(node)),
                _marker: Default::default(),
            }
        } else {
            Self {
                inner: Box::new(std::iter::empty()),
                _marker: Default::default(),
            }
        }
    }
}

impl<'a, P: PrefixTrait + 'a, V: Clone> Iterator for Iter<'a, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

struct IterState<'a, P: PrefixTrait + 'a, V: Clone> {
    node_iter: Vec<NodeIter<'a, P, V>>,
    leafs: VecDeque<Leaf<'a, P, V>>,
}

impl<'a, P: PrefixTrait + 'a, V: Clone> IterState<'a, P, V> {
    pub fn new(node: &'a Node<P, V>) -> Self {
        let mut node_iter = Vec::new();
        node_iter.push(NodeIter::new(node.iter()));

        Self {
            node_iter,
            leafs: VecDeque::new(),
        }
    }
}

impl<'a, P: PrefixTrait + 'a, V: Clone> Iterator for IterState<'a, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        'outer: while let Some(node) = self.node_iter.last_mut() {
            let e = node.next();
            loop {
                match e {
                    None => {
                        self.node_iter.pop().unwrap();
                        break;
                    }
                    Some(other) => {
                        if other.1.is_twig() {
                            let NodeType::Twig(twig) = &other.1.node_type else {
                                panic!("should not happen");
                            };

                            for v in twig.iter() {
                                let new_leaf = Leaf::new(&twig.key, &v.value, &v.ts);
                                self.leafs.push_back(new_leaf);
                            }
                            break 'outer;
                        } else {
                            self.node_iter.push(NodeIter::new(other.1.iter()));
                            break;
                        }
                    }
                }
            }
        }

        self.leafs
            .pop_front()
            .map(|leaf| (leaf.key.as_byte_slice().to_vec(), leaf.value, leaf.ts))
    }
}

enum RangeResult<'a, V: Clone> {
    Continue,
    Yield(Option<(Vec<u8>, &'a V, &'a u64)>),
}

struct RangeIterator<'a, K: Key + 'a, P: PrefixTrait, V: Clone> {
    iter: Iter<'a, P, V>,
    end_bound: Bound<K>,
    _marker: std::marker::PhantomData<P>,
}

struct EmptyRangeIterator;

trait RangeIteratorTrait<'a, K: Key + 'a, P: PrefixTrait, V: Clone> {
    fn next(&mut self) -> RangeResult<'a, V>;
}

pub struct Range<'a, K: Key + 'a, P: PrefixTrait, V: Clone> {
    inner: Box<dyn RangeIteratorTrait<'a, K, P, V> + 'a>,
}

impl<'a, K: Key + 'a, P: PrefixTrait, V: Clone> RangeIteratorTrait<'a, K, P, V>
    for EmptyRangeIterator
{
    fn next(&mut self) -> RangeResult<'a, V> {
        RangeResult::Yield(None)
    }
}

impl<'a, K: Key, P: PrefixTrait, V: Clone> RangeIterator<'a, K, P, V> {
    pub fn new(iter: Iter<'a, P, V>, end_bound: Bound<K>) -> Self {
        Self {
            iter,
            end_bound,
            _marker: Default::default(),
        }
    }
}

impl<'a, K: Key + 'a, P: PrefixTrait, V: Clone> RangeIteratorTrait<'a, K, P, V>
    for RangeIterator<'a, K, P, V>
{
    fn next(&mut self) -> RangeResult<'a, V> {
        let next_item = self.iter.next();
        match next_item {
            Some((key, value, ts)) => {
                let next_key_slice = key.as_slice();
                match &self.end_bound {
                    Bound::Included(k) if next_key_slice == k.as_slice() => RangeResult::Continue,
                    Bound::Excluded(k) if next_key_slice == k.as_slice() => {
                        RangeResult::Yield(None)
                    }
                    Bound::Unbounded => RangeResult::Yield(Some((key, value, ts))),
                    _ => RangeResult::Yield(Some((key, value, ts))),
                }
            }
            None => RangeResult::Yield(None),
        }
    }
}

impl<'a, K: Key, P: PrefixTrait + 'a, V: Clone + 'a> Iterator for Range<'a, K, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64);

    fn next(&mut self) -> Option<(Vec<u8>, &'a V, &'a u64)> {
        match self.inner.next() {
            RangeResult::Continue => {
                let res = self.next();
                self.inner = Box::new(EmptyRangeIterator);
                res
            }
            RangeResult::Yield(item) => item,
        }
    }
}

impl<'a, K: Key + 'a, P: PrefixTrait + 'a, V: Clone> Range<'a, K, P, V> {
    pub fn empty() -> Self {
        Self {
            inner: Box::new(EmptyRangeIterator),
        }
    }

    pub fn for_iter(iter: Iter<'a, P, V>, end_bound: Bound<K>) -> Self {
        Self {
            inner: Box::new(RangeIterator::new(iter, end_bound)),
        }
    }
}
