#[allow(warnings)]

use std::cmp::min;
use std::mem::MaybeUninit;


/*
    Node trait implementations
*/

pub trait NodeTrait<N> {
    fn add_child(&mut self, key: u8, node: N);
    fn find_child(&self, key: u8) -> Option<&N>;
    fn find_child_mut(&mut self, key: u8) -> Option<&mut N>;
    fn delete_child(&mut self, key: u8) -> Option<N>;
    fn num_children(&self) -> usize;
    fn width(&self) -> usize;
}

pub struct FlatNode<N, const WIDTH: usize> {
    keys: [u8; WIDTH],
    children: Box<[MaybeUninit<N>; WIDTH]>,
    num_children: u8,
}

impl<N, const WIDTH: usize> Default for FlatNode<N, WIDTH> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N, const WIDTH: usize> FlatNode<N, WIDTH> {
    #[inline]
    pub fn new() -> Self {
        Self {
            keys: [0; WIDTH],
            children: Box::new(unsafe { MaybeUninit::uninit().assume_init() }),
            num_children: 0,
        }
    }

    pub fn resize<const NEW_WIDTH: usize>(&mut self) -> FlatNode<N, NEW_WIDTH> {
        let mut new: FlatNode<N, NEW_WIDTH> = FlatNode::new();
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

    pub fn grow<const NEW_WIDTH: usize>(&mut self) -> Node48<N, NEW_WIDTH> {
        let mut n48 = Node48::new();
        for i in 0..self.num_children as usize {
            let stolen = std::mem::replace(&mut self.children[i], MaybeUninit::uninit());
            n48.add_child(self.keys[i], unsafe { stolen.assume_init() });
        }
        self.num_children = 0;
        n48
    }
}

impl<N, const WIDTH: usize> NodeTrait<N> for FlatNode<N, WIDTH> {
    #[inline]
    fn add_child(&mut self, key: u8, node: N) {
        let idx = self.find_pos(key).expect("add_child: no space left");

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
        // Find position of the key
        let idx = self
            .keys
            .iter()
            .take(self.num_children as usize)
            .position(|&k| k == key)?;

        // Remove the value.
        let node = std::mem::replace(&mut self.children[idx], MaybeUninit::uninit());

        // Shift keys and children to the left.
        for i in idx..(WIDTH - 1) {
            self.keys[i] = self.keys[i + 1];
            self.children[i] = std::mem::replace(&mut self.children[i + 1], MaybeUninit::uninit());
        }

        // Fix the last key and child and adjust count.
        self.keys[WIDTH - 1] = 0;
        self.children[WIDTH - 1] = MaybeUninit::uninit();

        self.num_children -= 1;

        // Return what we deleted.
        Some(unsafe { node.assume_init() })
    }

    #[inline(always)]
    fn num_children(&self) -> usize {
        self.num_children as usize
    }

    #[inline(always)]
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<N, const WIDTH: usize> Drop for FlatNode<N, WIDTH> {
    fn drop(&mut self) {
        for value in &mut self.children[..self.num_children as usize] {
            unsafe { value.assume_init_drop() }
        }
        self.num_children = 0;
    }
}

pub struct Node48<N, const WIDTH: usize> {
    child_ptr_indexes: Box<VecArray<u8, 256>>,
    children: Box<VecArray<N, WIDTH>>,
    num_children: u8,
}

impl<N, const WIDTH: usize> Default for Node48<N, WIDTH> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N, const WIDTH: usize> Node48<N, WIDTH> {
    pub fn new() -> Self {
        Self {
            child_ptr_indexes: Box::new(VecArray::new()),
            children: Box::new(VecArray::new()),
            num_children: 0,
        }
    }

    pub fn shrink<const NEW_WIDTH: usize>(&mut self) -> FlatNode<N, NEW_WIDTH> {
        let mut node = FlatNode::<N, NEW_WIDTH>::new();
        self.num_children = 0;
        self.resize(&mut node);
        node
    }

    pub fn grow(&mut self) -> Node256<N> {
        let mut n256: Node256<N> = Node256::new();
        self.num_children = 0;
        self.resize(&mut n256);
        n256
    }

    fn resize<NM: NodeTrait<N>>(&mut self, nm: &mut NM) {
        for (key, pos) in self.child_ptr_indexes.iter() {
            let node = self.children.erase(*pos as usize).unwrap();
            nm.add_child(key as u8, node);
        }
    }
}

impl<N, const WIDTH: usize> NodeTrait<N> for Node48<N, WIDTH> {
    fn add_child(&mut self, key: u8, node: N) {
        let pos = self.children.first_free_pos();
        self.child_ptr_indexes.set(key as usize, pos as u8);
        self.children.set(pos, node);
        self.num_children += 1;
    }

    fn find_child(&self, key: u8) -> Option<&N> {
        if let Some(pos) = self.child_ptr_indexes.get(key as usize) {
            return self.children.get(*pos as usize);
        }
        None
    }

    fn find_child_mut(&mut self, key: u8) -> Option<&mut N> {
        if let Some(pos) = self.child_ptr_indexes.get(key as usize) {
            return self.children.get_mut(*pos as usize);
        }
        None
    }

    fn delete_child(&mut self, key: u8) -> Option<N> {
        let pos = self.child_ptr_indexes.erase(key as usize)?;

        let old = self.children.erase(pos as usize);
        self.num_children -= 1;

        old
    }

    fn num_children(&self) -> usize {
        self.num_children as usize
    }

    #[inline]
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<N, const WIDTH: usize> Drop for Node48<N, WIDTH> {
    fn drop(&mut self) {
        if self.num_children == 0 {
            return;
        }
        self.num_children = 0;
        self.child_ptr_indexes.clear();
        self.children.clear();
    }
}


pub struct VecArray<X, const WIDTH: usize> {
    storage: Vec<Option<X>>,
}

impl<X, const WIDTH: usize> VecArray<X, WIDTH> {
    pub fn new() -> Self {
        Self {
            storage: Vec::with_capacity(WIDTH),
        }
    }

    pub fn push(&mut self, x: X) -> usize {
        let pos = self.first_free_pos();
        self.storage[pos] = Some(x);
        pos
    }

    pub fn pop(&mut self) -> Option<X> {
        self.last_used_pos().and_then(|pos| self.storage[pos].take())
    }

    pub fn last(&self) -> Option<&X> {
        self.last_used_pos().and_then(|pos| self.storage[pos].as_ref())
    }

    #[inline]
    pub fn last_used_pos(&self) -> Option<usize> {
        self.storage.iter().rposition(Option::is_some)
    }

    // #[inline]
    // pub fn first_free_pos(&self) -> Option<usize> {
    //     // self.storage.iter().position(Option::is_none)
    //     self.storage.iter().position(|x| x.is_none())
    // }

    #[inline]
    pub fn first_free_pos(&mut self) -> usize {
        let pos = self.storage.iter().position(|x| x.is_none());
        match pos {
            Some(p) => p,
            None => {
                // No free position was found, so we add a new one.
                self.storage.push(None);
                self.storage.len() - 1
            }
        }
    }

    #[inline]
    pub fn get(&self, pos: usize) -> Option<&X> {
        self.storage.get(pos).and_then(Option::as_ref)
    }

    #[inline]
    pub fn get_mut(&mut self, pos: usize) -> Option<&mut X> {
        self.storage.get_mut(pos).and_then(Option::as_mut)
    }

    #[inline]
    pub fn set(&mut self, pos: usize, x: X) {
        if pos < self.storage.len() {
            self.storage[pos] = Some(x);
        } else {
            self.storage.resize_with(pos + 1, || None);
            self.storage[pos] = Some(x);
        }
    }


    #[inline]
    pub fn update(&mut self, pos: usize, x: X) -> Option<X> {
        std::mem::replace(&mut self.storage[pos], Some(x))
    }

    #[inline]
    pub fn erase(&mut self, pos: usize) -> Option<X> {
        self.storage[pos].take()
    }

    pub fn clear(&mut self) {
        self.storage.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }

    pub fn size(&mut self) -> usize {
        self.storage.len()
    }

    pub fn iter_keys(&self) -> impl DoubleEndedIterator<Item = usize> + '_ {
        self.storage.iter().enumerate().filter_map(|(i, x)| {
            if x.is_some() {
                Some(i)
            } else {
                None
            }
        })
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (usize, &X)> {
        self.storage.iter().enumerate().filter_map(|(i, x)| {
            x.as_ref().map(|v| (i, v))
        })
    }

    pub fn iter_mut(&mut self) -> impl DoubleEndedIterator<Item = (usize, &mut X)> {
        self.storage.iter_mut().enumerate().filter_map(|(i, x)| {
            x.as_mut().map(|v| (i, v))
        })
    }
}

impl<X, const WIDTH: usize> Default for VecArray<X, WIDTH> {
    fn default() -> Self {
        Self::new()
    }
}

impl<X, const WIDTH: usize> std::ops::Index<usize> for VecArray<X, WIDTH> {
    type Output = X;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}

pub struct Node256<N> {
    children: Box<VecArray<N, 256>>,
    num_children: usize,
}

impl<N> Node256<N> {
    pub fn new() -> Self {
        Self {
            children: Box::new(VecArray::new()),
            num_children: 0,
        }
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (u8, &N)> {
        self.children.iter().map(|(key, node)| (key as u8, node))
    }

    pub fn shrink<const NEW_WIDTH: usize>(&mut self) -> Node48<N, NEW_WIDTH> {
        let mut indexed = Node48::new();

        let keys: Vec<usize> = self.children.iter_keys().collect();
        for key in keys {
            let child = self.children.erase(key).unwrap();
            indexed.add_child(key as u8, child);
        }
        indexed
    }

}

impl<N> NodeTrait<N> for Node256<N> {
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

    fn width(&self) -> usize {
        256
    }
}

#[cfg(test)]
mod tests {
    use super::{VecArray, NodeTrait};

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
    fn update() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        assert_eq!(v.update(0, 6), Some(5));
        assert_eq!(v.get(0), Some(&6));
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

    #[test]
    fn iter_mut() {
        let mut v: VecArray<i32, 10> = VecArray::new();
        v.push(5);
        v.push(6);
        for (index, value) in v.iter_mut() {
            *value += 1;
        }
        assert_eq!(v.get(0), Some(&6));
        assert_eq!(v.get(1), Some(&7));
    }


    // #[test]
    // fn test_partial_before() {
    //     let a = ArrayPartial::from_slice(b"Hello, world!");
    //     assert_eq!(a.partial_before(5).to_slice(), b"Hello");
    // }

    // #[test]
    // fn test_partial_from() {
    //     let arr: ArrayPartial<16> = ArrayPartial::from_slice(b"Hello, world!");
    //     assert_eq!(arr.partial_from(7, 5).to_slice(), b"world");
    // }

    // #[test]
    // fn test_prefix_after() {
    //     let arr: ArrayPartial<16> = ArrayPartial::from_slice(b"Hello, world!");
    //     assert_eq!(arr.partial_after(7).to_slice(), b"world!");
    // }

    // #[test]
    // fn test_at() {
    //     let arr: ArrayPartial<16> = ArrayPartial::from_slice(b"Hello, world!");
    //     assert_eq!(arr.at(0), 72);
    // }

    // #[test]
    // fn test_length() {
    //     let arr: ArrayPartial<16> = ArrayPartial::from_slice(b"Hello, world!");
    //     assert_eq!(arr.length(), 13);
    // }

    // #[test]
    // fn test_prefix_length_common() {
    //     let arr1: ArrayPartial<16> = ArrayPartial::from_slice(b"Hello, world!");
    //     let arr2: ArrayPartial<16> = ArrayPartial::from_slice(b"Hello, there!");
    //     assert_eq!(arr1.prefix_length_common(&arr2), 7);
    // }

    // #[test]
    // fn test_from_slice() {
    //     let arr: ArrayPartial<16> = ArrayPartial::from_slice(b"Hello, world!");
    //     assert_eq!(arr.to_slice(), b"Hello, world!");
    // }

    // #[test]
    // fn test_partial_chain_with_key() {
    //     let arr1: ArrayPartial<16> = ArrayPartial::key(b"Hello, world!");
    //     let arr2: ArrayPartial<16> = ArrayPartial::key(b"Hello, there!");
    //     let partial1 = arr1.partial_before(6);
    //     assert_eq!(partial1.to_slice(), b"Hello,");
    //     let partial2 = arr2.partial_from(7, 5);
    //     assert_eq!(partial2.to_slice(), b"there");
    //     let partial3 = partial1.partial_after(1);
    //     assert_eq!(partial3.to_slice(), b"ello,");
    //     assert_eq!(0, partial3.prefix_length_common(&partial2));
    // }



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
        node_test(super::FlatNode::<usize, 4>::new(), 4);
        node_test(super::FlatNode::<usize, 16>::new(), 16);
        node_test(super::FlatNode::<usize, 32>::new(), 32);
        node_test(super::FlatNode::<usize, 48>::new(), 48);
        node_test(super::FlatNode::<usize, 64>::new(), 64);

        // resize from 16 to 4
        let mut node = super::FlatNode::<usize, 16>::new();
        for i in 0..4 {
            node.add_child(i as u8, i);
        }

        let resized: super::FlatNode<usize, 4> = node.resize();
        assert_eq!(resized.num_children, 4);
        for i in 0..4 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        // resize from 4 to 16
        let mut node = super::FlatNode::<usize, 4>::new();
        for i in 0..4 {
            node.add_child(i as u8, i);
        }
        let mut resized: super::FlatNode<usize, 16> = node.resize();
        assert_eq!(resized.num_children, 4);
        for i in 4..16 {
            resized.add_child(i as u8, i);
        }
        assert_eq!(resized.num_children, 16);
        for i in 0..16 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        // resize from 16 to 48
        let mut node = super::FlatNode::<usize, 16>::new();
        for i in 0..16 {
            node.add_child(i as u8, i);
        }


        let resized = node.grow::<48>();
        assert_eq!(resized.num_children, 16);
        for i in 0..16 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        
        let mut node = super::FlatNode::<usize, 4>::new();
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
        // node_test(super::Node48::<usize, 48>::new(), 48);

        let mut n48 = super::Node48::<u8, 48>::new();
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
        let mut node = super::Node48::<u8, 48>::new();
        for i in 0..16 {
            node.add_child(i as u8, i);
        }

        let resized = node.shrink::<16>();
        assert_eq!(resized.num_children, 16);
        for i in 0..16 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        // resize from 48 to 4
        let mut node = super::Node48::<u8, 48>::new();
        for i in 0..4 {
            node.add_child(i as u8, i);
        }
        let resized = node.shrink::<4>();
        assert_eq!(resized.num_children, 4);
        for i in 0..4 {
            assert!(matches!(resized.find_child(i as u8), Some(v) if *v == i));
        }

        // resize from 48 to 256
        let mut node = super::Node48::<u8, 48>::new();
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
        node_test(super::Node256::<usize>::new(), 255);

        let mut n256 = super::Node256::new();
        for i in 0..255 {
            n256.add_child(i, i);
            assert_eq!(*n256.find_child(i).unwrap(), i);
            assert_eq!(n256.delete_child(i), Some(i));
            assert_eq!(n256.find_child(i), None);
        }

        // resize from 256 to 48
        let mut node = super::Node256::new();
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
