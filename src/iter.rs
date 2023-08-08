use std::collections::Bound;
use std::sync::Arc;

use crate::art::Node;
use crate::{Key, PrefixTrait};

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

// impl<'a, P: PrefixTrait, V: Clone> Iterator for NodeIter<'a, P, V> {
//     fn next_back(&mut self) -> Option<Self::Item> {
//         self.node.next_back()
//     }
// }

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
    inner_node_iter: Vec<NodeIter<'a, P, V>>,
}

impl<'a, P: PrefixTrait + 'a, V: Clone> IterState<'a, P, V> {
    pub fn new(node: &'a Node<P, V>) -> Self {
        let mut inner_node_iter = Vec::new();
        inner_node_iter.push(NodeIter::new(node.iter()));

        Self { inner_node_iter }
    }
}

impl<'a, P: PrefixTrait + 'a, V: Clone> Iterator for IterState<'a, P, V> {
    type Item = (Vec<u8>, &'a V, &'a u64);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some(last_iter) = self.inner_node_iter.last_mut() else {
                return None;
            };

            let Some((_, node)) = last_iter.next() else{
                self.inner_node_iter.pop();
                continue;

            };

            if node.is_leaf() {
                if let Some(v) = node.get_value() {
                    return Some((v.0.as_byte_slice().to_vec(), v.1, v.2));
                }
            } else {
                self.inner_node_iter.push(NodeIter::new(node.iter()));
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

impl<'a, K: Key + 'a, P: PrefixTrait, V: Clone> RangeInnerTrait<'a, K, P, V>
    for RangeInner<'a, K, P, V>
{
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
