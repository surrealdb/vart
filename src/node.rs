#[allow(warnings)]

use std::cmp::min;
use std::mem::MaybeUninit;

use crate::{Prefix, VecArray};


/*
    Node trait implementations
*/

pub trait NodeTrait<N> {
    fn add_child(&mut self, key: u8, node: N);
    fn find_child(&self, key: u8) -> Option<&N>;
    fn find_child_mut(&mut self, key: u8) -> Option<&mut N>;
    fn delete_child(&mut self, key: u8) -> Option<N>;
    fn num_children(&self) -> usize;
    fn size(&self) -> usize;
}

pub struct LeafNode<K: Prefix + Clone, V> {
    pub key: K,
    pub value: V,
    pub ts: u64, // Timestamp for the leaf node
}

impl<K: Prefix + Clone, V> LeafNode<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Self { key, value, ts:0 }
    }
}


pub struct FlatNode<P: Prefix + Clone, N, const WIDTH: usize> {
    pub prefix: P, // Prefix associated with the node (and Key in the leaf node)
    pub ts: u64, // Timestamp for the flat node

    // Keys and children
    keys: [u8; WIDTH],
    children: Box<[MaybeUninit<N>; WIDTH]>,
    num_children: u8,
}

impl<P: Prefix + Clone, N, const WIDTH: usize> FlatNode<P, N, WIDTH> {
    #[inline]
    pub fn new(prefix: P) -> Self {
        Self {
            prefix: prefix,
            ts:0,
            keys: [0; WIDTH],
            children: Box::new(unsafe { MaybeUninit::uninit().assume_init() }),
            num_children: 0,
        }
    }

    pub fn resize<const NEW_WIDTH: usize>(&mut self) -> FlatNode<P, N, NEW_WIDTH> {
        let mut new: FlatNode<P, N, NEW_WIDTH> = FlatNode::new(self.prefix.clone());
        for i in 0..self.num_children as usize {
            new.keys[i] = self.keys[i];
            new.children[i] = std::mem::replace(&mut self.children[i], MaybeUninit::uninit())
        }
        new.num_children = self.num_children;
        self.num_children = 0;
        new
    }

    #[inline]
    fn find_pos(&self, key: u8) -> Option<usize> {
        let idx = (0..self.num_children as usize)
            .rev()
            .find(|&i| key < self.keys.as_ref()[i]);
        idx.or(Some(self.num_children as usize))
    }

    #[inline]
    fn index(&self, key: u8) -> Option<usize> {
        self.keys[0..min(WIDTH, self.num_children as usize)]
        .iter()
        .position(|&c| key == c)
    }

    pub fn grow<const NEW_WIDTH: usize>(&mut self) -> Node48<P, N, NEW_WIDTH> {
        let mut n48 = Node48::new(self.prefix.clone());
        for i in 0..self.num_children as usize {
            let stolen = std::mem::replace(&mut self.children[i], MaybeUninit::uninit());
            n48.add_child(self.keys[i], unsafe { stolen.assume_init() });
        }
        self.num_children = 0;
        n48
    }
}

impl<P: Prefix + Clone, N, const WIDTH: usize> NodeTrait<N> for FlatNode<P, N, WIDTH> {
    #[inline]
    fn add_child(&mut self, key: u8, node: N) {
        let idx = self.find_pos(key).expect("node is full");

        for i in (idx..self.num_children as usize).rev() {
            self.keys[i + 1] = self.keys[i];
            self.children[i + 1] = std::mem::replace(&mut self.children[i], MaybeUninit::uninit());
        }
        self.keys[idx] = key;
        self.children[idx].write(node);
        self.num_children += 1;
    }

    fn find_child(&self, key: u8) -> Option<&N> {
        let idx = self.index(key)?;
        Some(unsafe { self.children[idx].assume_init_ref() })
    }

    fn find_child_mut(&mut self, key: u8) -> Option<&mut N> {
        let idx = self.index(key)?;
        return Some(unsafe { self.children[idx].assume_init_mut() });
    }

    fn delete_child(&mut self, key: u8) -> Option<N> {
        let idx = self
            .keys
            .iter()
            .take(self.num_children as usize)
            .position(|&k| k == key)?;

        let deleted_node = std::mem::replace(&mut self.children[idx], MaybeUninit::uninit());

        for i in idx..(WIDTH - 1) {
            self.keys[i] = self.keys[i + 1];
            self.children[i] = std::mem::replace(&mut self.children[i + 1], MaybeUninit::uninit());
        }

        self.keys[WIDTH - 1] = 0;
        self.children[WIDTH - 1] = MaybeUninit::uninit();
        self.num_children -= 1;

        Some(unsafe { deleted_node.assume_init() })
    }

    #[inline(always)]
    fn num_children(&self) -> usize {
        self.num_children as usize
    }

    #[inline(always)]
    fn size(&self) -> usize {
        WIDTH
    }
}

impl<P: Prefix + Clone, N, const WIDTH: usize> Drop for FlatNode<P, N, WIDTH> {
    fn drop(&mut self) {
        for value in &mut self.children[..self.num_children as usize] {
            unsafe { value.assume_init_drop() }
        }
        self.num_children = 0;
    }
}

pub struct Node48<P: Prefix + Clone, N, const WIDTH: usize> {
    pub prefix: P, // Prefix associated with the node
    pub ts: u64, // Timestamp for node48

    // Keys and children
    keys: Box<VecArray<u8, 256>>,
    children: Box<VecArray<N, WIDTH>>,
    num_children: u8,
}

impl<P: Prefix + Clone, N, const WIDTH: usize> Node48<P, N, WIDTH> {
    pub fn new(prefix: P) -> Self {
        Self {
            prefix: prefix,
            ts:0,
            keys: Box::new(VecArray::new()),
            children: Box::new(VecArray::new()),
            num_children: 0,
        }
    }

    pub fn shrink<const NEW_WIDTH: usize>(&mut self) -> FlatNode<P, N, NEW_WIDTH> {
        let mut node = FlatNode::<P, N, NEW_WIDTH>::new(self.prefix.clone());
        self.num_children = 0;
        self.resize(&mut node);
        node
    }

    pub fn grow(&mut self) -> Node256<P, N> {
        let mut n256: Node256<P, N> = Node256::new(self.prefix.clone());
        self.num_children = 0;
        self.resize(&mut n256);
        n256
    }

    fn resize<NM: NodeTrait<N>>(&mut self, nm: &mut NM) {
        for (key, pos) in self.keys.iter() {
            let node = self.children.erase(*pos as usize).unwrap();
            nm.add_child(key as u8, node);
        }
    }
}

impl<P: Prefix + Clone, N, const WIDTH: usize> NodeTrait<N> for Node48<P, N, WIDTH> {
    fn add_child(&mut self, key: u8, node: N) {
        let pos = self.children.first_free_pos();
        self.keys.set(key as usize, pos as u8);
        self.children.set(pos, node);
        self.num_children += 1;
    }

    fn find_child(&self, key: u8) -> Option<&N> {
        if let Some(pos) = self.keys.get(key as usize) {
            return self.children.get(*pos as usize);
        }
        None
    }

    fn find_child_mut(&mut self, key: u8) -> Option<&mut N> {
        if let Some(pos) = self.keys.get(key as usize) {
            return self.children.get_mut(*pos as usize);
        }
        None
    }

    fn delete_child(&mut self, key: u8) -> Option<N> {
        let pos = self.keys.erase(key as usize)?;

        let old = self.children.erase(pos as usize);
        self.num_children -= 1;

        old
    }

    fn num_children(&self) -> usize {
        self.num_children as usize
    }

    #[inline]
    fn size(&self) -> usize {
        WIDTH
    }
}

impl<P: Prefix + Clone, N, const WIDTH: usize> Drop for Node48<P, N, WIDTH> {
    fn drop(&mut self) {
        if self.num_children == 0 {
            return;
        }
        self.num_children = 0;
        self.keys.clear();
        self.children.clear();
    }
}

pub struct Node256<P: Prefix + Clone, N> {
    pub prefix: P, // Prefix associated with the node
    pub ts: u64, // Timestamp for node56

    children: Box<VecArray<N, 256>>,
    num_children: usize,
}

impl<P: Prefix + Clone, N> Node256<P, N> {
    pub fn new(prefix: P) -> Self {
        Self {
            prefix: prefix,
            ts:0,
            children: Box::new(VecArray::new()),
            num_children: 0,
        }
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (u8, &N)> {
        self.children.iter().map(|(key, node)| (key as u8, node))
    }

    pub fn shrink<const NEW_WIDTH: usize>(&mut self) -> Node48<P, N, NEW_WIDTH> {
        let mut indexed = Node48::new(self.prefix.clone());

        let keys: Vec<usize> = self.children.iter_keys().collect();
        for key in keys {
            let child = self.children.erase(key).unwrap();
            indexed.add_child(key as u8, child);
        }
        indexed
    }

}

impl<P: Prefix + Clone, N> NodeTrait<N> for Node256<P, N> {
    #[inline]
    fn add_child(&mut self, key: u8, node: N) {
        self.children.set(key as usize, node);
        self.num_children += 1;
    }

    #[inline]
    fn find_child(&self, key: u8) -> Option<&N> {
        self.children.get(key as usize)
    }

    #[inline]
    fn find_child_mut(&mut self, key: u8) -> Option<&mut N> {
        self.children.get_mut(key as usize)
    }

    #[inline]
    fn delete_child(&mut self, key: u8) -> Option<N> {
        let n = self.children.erase(key as usize);
        if n.is_some() {
            self.num_children -= 1;
        }
        n
    }

    #[inline]
    fn num_children(&self) -> usize {
        self.num_children
    }

    fn size(&self) -> usize {
        256
    }
}

#[cfg(test)]
mod tests {
    use super::{VecArray, NodeTrait};
    use crate::ArrayPrefix;

    #[test]
    fn new() {
        let v: VecArray<i32, 10> = VecArray::new();
        assert_eq!(v.storage.len(), 10);
    }

    #[test]
    fn push_and_pop() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        let index = v.push(5);
        assert_eq!(v.get(index), Some(&5));
        assert_eq!(v.pop(), Some(5));
    }

    #[test]
    fn last() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        v.push(6);
        assert_eq!(v.last(), Some(&6));
    }

    #[test]
    fn last_used_pos() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        v.push(6);
        assert_eq!(v.last_used_pos(), Some(1));
    }

    #[test]
    fn first_free_pos() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        assert_eq!(v.first_free_pos(), 1);
    }

    #[test]
    fn get_and_set() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.set(5, 6);
        assert_eq!(v.get(5), Some(&6));
    }

    #[test]
    fn get_mut() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.set(5, 6);
        if let Some(value) = v.get_mut(5) {
            *value = 7;
        }
        assert_eq!(v.get(5), Some(&7));
    }


    #[test]
    fn erase() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        assert_eq!(v.erase(0), Some(5));
        assert_eq!(v.get(0), None);
    }

    #[test]
    fn clear() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        v.clear();
        assert_eq!(v.is_empty(), true);
    }

    #[test]
    fn is_empty() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        assert_eq!(v.is_empty(), true);
        v.push(5);
        assert_eq!(v.is_empty(), false);
    }

    #[test]
    fn iter_keys() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        v.push(6);
        let keys: Vec<usize> = v.iter_keys().collect();
        assert_eq!(keys, vec![0, 1]);
    }

    #[test]
    fn iter() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        v.push(6);
        let values: Vec<(usize, &i32)> = v.iter().collect();
        assert_eq!(values, vec![(0, &5), (1, &6)]);
    }

    fn node_test(mut node: impl NodeTrait<usize>, size: usize) {
        for i in 0..size {
            node.add_child(i as u8, i);
        }

        for i in 0..size {
            assert!(matches!(node.find_child(i as u8), Some(v) if *v == i));
        }

        for i in 0..size {
            assert!(matches!(node.delete_child(i as u8), Some(v) if v == i));
        }

        assert!(matches!(node.delete_child((size + 1) as u8), None));
    }

    #[test]
    fn test_flatnode() {
        let dummy_prefix: ArrayPrefix<8> = ArrayPrefix::key("foo".as_bytes());


        node_test(super::FlatNode::<ArrayPrefix<8>, usize, 4>::new(dummy_prefix.clone()), 4);
        node_test(super::FlatNode::<ArrayPrefix<8>, usize, 16>::new(dummy_prefix.clone()), 16);
        node_test(super::FlatNode::<ArrayPrefix<8>, usize, 32>::new(dummy_prefix.clone()), 32);
        node_test(super::FlatNode::<ArrayPrefix<8>, usize, 48>::new(dummy_prefix.clone()), 48);
        node_test(super::FlatNode::<ArrayPrefix<8>, usize, 64>::new(dummy_prefix.clone()), 64);

        // resize from 16 to 4
        let mut node = super::FlatNode::<ArrayPrefix<8>, usize, 16>::new(dummy_prefix.clone());
        for i in 0..4 {
            node.add_child(i as u8, i);
        }

        let resized: super::FlatNode<ArrayPrefix<8>, usize, 4> = node.resize();
        assert_eq!(resized.num_children, 4);
        for i in 0..4 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        // resize from 4 to 16
        let mut node = super::FlatNode::<ArrayPrefix<8>, usize, 4>::new(dummy_prefix.clone());
        for i in 0..4 {
            node.add_child(i as u8, i);
        }
        let mut resized: super::FlatNode<ArrayPrefix<8>, usize, 16> = node.resize();
        assert_eq!(resized.num_children, 4);
        for i in 4..16 {
            resized.add_child(i as u8, i);
        }
        assert_eq!(resized.num_children, 16);
        for i in 0..16 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        // resize from 16 to 48
        let mut node = super::FlatNode::<ArrayPrefix<8>, usize, 16>::new(dummy_prefix.clone());
        for i in 0..16 {
            node.add_child(i as u8, i);
        }


        let resized = node.grow::<48>();
        assert_eq!(resized.num_children, 16);
        for i in 0..16 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        
        let mut node = super::FlatNode::<ArrayPrefix<8>, usize, 4>::new(dummy_prefix.clone());
        node.add_child(1, 1);
        node.add_child(2, 2);
        node.add_child(3, 3);
        node.add_child(4, 4);
        assert_eq!(node.num_children(), 4);
        assert_eq!(node.find_child(1), Some(&1));
        assert_eq!(node.find_child(2), Some(&2));
        assert_eq!(node.find_child(3), Some(&3));
        assert_eq!(node.find_child(4), Some(&4));
        assert_eq!(node.find_child(5), None);
        assert_eq!(node.find_child_mut(1), Some(&mut 1));
        assert_eq!(node.find_child_mut(2), Some(&mut 2));
        assert_eq!(node.find_child_mut(3), Some(&mut 3));
        assert_eq!(node.find_child_mut(4), Some(&mut 4));
        assert_eq!(node.find_child_mut(5), None);
        assert_eq!(node.delete_child(1), Some(1));
        assert_eq!(node.delete_child(2), Some(2));
        assert_eq!(node.delete_child(3), Some(3));
        assert_eq!(node.delete_child(4), Some(4));
        assert_eq!(node.delete_child(5), None);
        assert_eq!(node.num_children(), 0);
    }

    #[test]
    fn test_node48() {
        let dummy_prefix: ArrayPrefix<8> = ArrayPrefix::key("foo".as_bytes());

        // node_test(super::Node48::<usize, 48>::new(), 48);
        let mut n48 = super::Node48::<ArrayPrefix<8>, u8, 48>::new(dummy_prefix.clone());
        for i in 0..48 {
            n48.add_child(i, i);
            assert_eq!(*n48.find_child(i).unwrap(), i);
        }
        for i in 0..48 {
            assert_eq!(*n48.find_child(i).unwrap(), i);
        }
        for i in 0..48 {
            assert_eq!(n48.delete_child(i).unwrap(), i);
        }
        for i in 0..48 {
            assert!(n48.find_child(i as u8).is_none());
        }

        // resize from 48 to 16
        let mut node = super::Node48::<ArrayPrefix<8>, u8, 48>::new(dummy_prefix.clone());
        for i in 0..16 {
            node.add_child(i as u8, i);
        }

        let resized = node.shrink::<16>();
        assert_eq!(resized.num_children, 16);
        for i in 0..16 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        // resize from 48 to 4
        let mut node = super::Node48::<ArrayPrefix<8>, u8, 48>::new(dummy_prefix.clone());
        for i in 0..4 {
            node.add_child(i as u8, i);
        }
        let resized = node.shrink::<4>();
        assert_eq!(resized.num_children, 4);
        for i in 0..4 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        // resize from 48 to 256
        let mut node = super::Node48::<ArrayPrefix<8>, u8, 48>::new(dummy_prefix.clone());
        for i in 0..48 {
            node.add_child(i as u8, i);
        }

        let resized = node.grow();
        assert_eq!(resized.num_children, 48);
        for i in 0..48 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }
    }

    #[test]
    fn test_node256() {
        let dummy_prefix: ArrayPrefix<8> = ArrayPrefix::key("foo".as_bytes());

        node_test(super::Node256::<ArrayPrefix<8>, usize>::new(dummy_prefix.clone()), 255);

        let mut n256 = super::Node256::new(dummy_prefix.clone());
        for i in 0..255 {
            n256.add_child(i, i);
            assert_eq!(*n256.find_child(i).unwrap(), i);
            assert_eq!(n256.delete_child(i), Some(i));
            assert_eq!(n256.find_child(i), None);
        }

        // resize from 256 to 48
        let mut node = super::Node256::new(dummy_prefix.clone());
        for i in 0..48 {
            node.add_child(i, i);
        }

        let resized = node.shrink::<48>();
        assert_eq!(resized.num_children, 48);
        for i in 0..48 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }
    }
}
