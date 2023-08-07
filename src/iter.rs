use std::collections::Bound;
use std::sync::Arc;

use crate::art::Node;
use crate::{Key, PrefixTrait};

pub struct NodeIter<'a, V> {
    node: Box<dyn DoubleEndedIterator<Item = &'a V> + 'a>,
}

impl<'a, V> NodeIter<'a, V> {
    fn new<I>(iter: I) -> Self
    where
        I: DoubleEndedIterator<Item = &'a V> + 'a,
    {
        Self {
            node: Box::new(iter),
        }
    }
}

impl<'a, V> DoubleEndedIterator for NodeIter<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.node.next_back()
    }
}

impl<'a, V> Iterator for NodeIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.node.next()
    }
}



pub struct Iter<'a, P: PrefixTrait + 'a, V: Clone> {
    inner: Box<dyn Iterator<Item = (Vec<u8>, &'a V, &'a u64)> + 'a>,
    _marker: std::marker::PhantomData<P>,
}

struct IterInner<'a, P: PrefixTrait + 'a, V: Clone> {
    node_iter_stack: Vec<Box<dyn Iterator<Item = (u8, &'a Arc<Node<P, V>>)> + 'a>>,

    // Pushed and popped with prefix portions as we descend the tree,
    cur_key: Vec<u8>,
    cur_prefix_length: usize,
}

impl<'a, P: PrefixTrait + 'a, V: Clone> IterInner<'a, P, V> {
    pub fn new(node: &'a Node<P, V>) -> Self {
        let mut node_iter_stack = Vec::new();
        node_iter_stack.push(node.iter());

        Self {
            node_iter_stack,
            cur_key: Vec::new(),
            cur_prefix_length: 0,
        }
    }
}

impl<'a, P: PrefixTrait + 'a, V: Clone> Iter<'a, P, V> {
    pub(crate) fn new(node: Option<&'a Arc<Node<P, V>>>) -> Self {
        if node.is_none() {
            return Self {
                inner: Box::new(std::iter::empty()),
                _marker: Default::default(),
            };
        }

        Self {
            inner: Box::new(IterInner::new(node.unwrap())),
            _marker: Default::default(),
        }
    }
}

impl<'a, P: PrefixTrait + 'a, V: Clone> Iterator for Iter<'a, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, P: PrefixTrait + 'a, V: Clone> Iterator for IterInner<'a, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        // Grab the last iterator from the stack, and see if there's more to iterate off of it.
        // If not, pop it off, and continue the loop.
        // If there is, loop through it looking for nodes; if the node is a leaf, return its value.
        // If it's a node, grab its child iterator, and push it onto the stack and continue the loop.
        loop {
            let Some(last_iter) = self.node_iter_stack.last_mut() else {
                return None;
            };

            let Some((_k, node)) = last_iter.next() else {
                self.node_iter_stack.pop();
                self.cur_key.truncate(self.cur_prefix_length);
                continue;
            };

            if let Some(v) = node.get_value() {
                let mut key = self.cur_key.clone();
                key.extend_from_slice(node.prefix().as_byte_slice());
                return Some((key, v.0, v.1));
            }
        }
    }
}


enum InnerResult<'a, V: Clone> {
    OneMore,
    Iter(Option<(Vec<u8>, &'a V, &'a u64)>),
}

struct RangeInner<'a, K: Key + 'a, P: PrefixTrait, V: Clone> {
    iter: Iter<'a, P, V>,
    end: Bound<K>,
    _marker: std::marker::PhantomData<P>,
}

struct RangeInnerNone {}

trait RangeInnerTrait<'a, K: Key + 'a, P: PrefixTrait, V: Clone> {
    fn next(&mut self) -> InnerResult<'a, V>;
}

pub struct Range<'a, K: Key + 'a, P: PrefixTrait, V: Clone> {
    inner: Box<dyn RangeInnerTrait<'a, K, P, V> + 'a>,
}

impl<'a, K: Key + 'a, P: PrefixTrait, V: Clone> RangeInnerTrait<'a, K, P, V> for RangeInnerNone {
    fn next(&mut self) -> InnerResult<'a, V> {
        InnerResult::Iter(None)
    }
}

impl<'a, K: Key, P: PrefixTrait, V: Clone> RangeInner<'a, K, P, V> {
    pub fn new(iter: Iter<'a, P, V>, end: Bound<K>) -> Self {
        Self {
            iter,
            end,
            _marker: Default::default(),
        }
    }
}

impl<'a, K: Key + 'a, P: PrefixTrait, V: Clone> RangeInnerTrait<'a, K, P, V> for RangeInner<'a, K, P, V> {
    fn next(&mut self) -> InnerResult<'a, V> {
        let Some(next) = self.iter.next() else {
            return InnerResult::Iter(None)
        };
        let next_key = next.0.as_slice();
        match &self.end {
            Bound::Included(k) if next_key == k.as_slice() => InnerResult::OneMore,
            Bound::Excluded(k) if next_key == k.as_slice() => InnerResult::Iter(None),
            Bound::Unbounded => InnerResult::Iter(Some(next)),
            _ => InnerResult::Iter(Some(next)),
        }
    }
}

impl<'a, K: Key, P: PrefixTrait + 'a, V: Clone + 'a> Iterator for Range<'a, K, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64);

    fn next(&mut self) -> Option<(Vec<u8>, &'a V, &'a u64)> {
        match self.inner.next() {
            InnerResult::OneMore => {
                let r = self.next();
                self.inner = Box::new(RangeInnerNone {});
                r
            }
            InnerResult::Iter(i) => i,
        }
    }
}

impl<'a, K: Key + 'a, P: PrefixTrait + 'a, V: Clone> Range<'a, K, P, V> {
    pub fn empty() -> Self {
        Self {
            inner: Box::new(RangeInnerNone {}),
        }
    }

    pub fn for_iter(iter: Iter<'a, P, V>, end: Bound<K>) -> Self {
        Self {
            inner: Box::new(RangeInner::new(iter, end)),
        }
    }
}
