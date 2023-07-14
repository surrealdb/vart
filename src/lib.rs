#[allow(warnings)]
mod art;

use std::cmp::min;
use std::mem::{self, MaybeUninit};

pub trait Partial {
    fn at(&self, pos: usize) -> u8;
    fn length(&self) -> usize;
    fn partial_before(&self, length: usize) -> Self;
    fn partial_after(&self, start: usize) -> Self;
    fn longest_common_prefix(&self, slice: &[u8]) -> usize;
}

pub trait Key: Clone {
    fn at(&self, pos: usize) -> u8;
    fn length(&self) -> usize;
    fn partial_after(&self, pos: usize) -> &[u8];
}

/*
    Partial trait implementations
*/

#[derive(Clone, Debug, Eq)]
pub struct ArrayPartial<const SIZE: usize> {
    data: [u8; SIZE],
    len: usize,
}

impl<const SIZE: usize> PartialEq for ArrayPartial<SIZE> {
    fn eq(&self, other: &Self) -> bool {
        self.data[..self.len] == other.data[..other.len]
    }
}

impl<const SIZE: usize> ArrayPartial<SIZE> {
    pub fn key(src: &[u8]) -> Self {
        assert!(src.len() < SIZE);
        let mut data = [0; SIZE];
        data[..src.len()].copy_from_slice(src);
        data[src.len()] = 0;
        Self {
            data,
            len: src.len() + 1,
        }
    }

    pub fn from_slice(src: &[u8]) -> Self {
        assert!(src.len() <= SIZE);
        let mut data = [0; SIZE];
        data[..src.len()].copy_from_slice(src);
        Self {
            data,
            len: src.len(),
        }
    }

    pub fn to_slice(&self) -> &[u8] {
        &self.data[..self.len]
    }
}

impl<const SIZE: usize> Partial for ArrayPartial<SIZE> {
    #[inline(always)]
    fn at(&self, pos: usize) -> u8 {
        assert!(pos < self.len);
        self.data[pos]
    }

    fn partial_before(&self, length: usize) -> Self {
        assert!(length <= self.len);
        ArrayPartial::from_slice(&self.data[..length])
    }

    fn partial_after(&self, start: usize) -> Self {
        assert!(start <= self.len);
        ArrayPartial::from_slice(&self.data[start..self.len])
    }

    #[inline(always)]
    fn length(&self) -> usize {
        self.len
    }

    fn longest_common_prefix(&self, key: &[u8]) -> usize {
        let len = min(self.len, key.len());
        let len = min(len, SIZE);
        let mut idx = 0;
        while idx < len {
            if self.data[idx] != key[idx] {
                break;
            }
            idx += 1;
        }
        idx
    }
}

impl<const SIZE: usize> From<&[u8]> for ArrayPartial<SIZE> {
    fn from(src: &[u8]) -> Self {
        Self::from_slice(src)
    }
}

/*
    Key trait implementations
*/

// Owned vec size key.
#[derive(Clone)]
pub struct VectorKey {
    data: Vec<u8>,
}

impl VectorKey {
    pub fn from_str(key: &str) -> Self {
        let mut data = Vec::with_capacity(key.len() + 1);
        data.extend_from_slice(key.as_bytes());
        data.push(0);
        Self { data }
    }

    pub fn from_slice(data: &[u8]) -> Self {
        let mut data = data.to_owned();
        if !data.contains(&0) {
            data.push(0);
        }
        Self { data }
    }
}

impl Key for VectorKey {
    fn at(&self, pos: usize) -> u8 {
        self.data[pos]
    }

    fn length(&self) -> usize {
        self.data.len()
    }

    fn partial_after(&self, pos: usize) -> &[u8] {
        &self.data[pos..self.length()]
    }
}

#[derive(Clone, Copy)]
pub struct ArrayKey<const N: usize> {
    data: [u8; N],
    len: usize,
}

impl<const N: usize> ArrayKey<N> {
    pub fn from_str(key: &str) -> Self {
        assert!(key.len() < N, "data length is greater than array length");
        let mut arr = [0; N];
        arr[..key.len()].copy_from_slice(key.as_bytes());
        Self {
            data: arr,
            len: key.len() + 1,
        }
    }
}

impl<const N: usize> Key for ArrayKey<N> {
    fn at(&self, pos: usize) -> u8 {
        self.data[pos]
    }

    fn length(&self) -> usize {
        self.len
    }

    fn partial_after(&self, pos: usize) -> &[u8] {
        &self.data[pos..self.length()]
    }
}

/*
    Node trait implementations
*/

pub trait NodeTrait<N> {
    fn add_child(&mut self, key: u8, node: N);
    fn seek_child(&self, key: u8) -> Option<&N>;
    fn seek_child_mut(&mut self, key: u8) -> Option<&mut N>;
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
            keys: [255; WIDTH],
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
        if WIDTH == 16 {
            let mut left = 0_usize;
            let mut right = self.num_children as usize;
            while left < right {
                let mid = (left + right) / 2;
                match self.keys[mid] {
                    v if v == key => return Some(mid),
                    v if v < key => {
                        left = mid + 1;
                    }
                    _ => {
                        right = mid;
                    }
                }
            }
            None
        } else {
            (0..self.num_children as usize).find(|&i| self.keys.as_ref()[i] == key)
        }
    }

    fn grow<const NEW_WIDTH: usize>(&mut self) -> Node48<N, NEW_WIDTH> {
        let mut n48 = Node48::new();
        for i in 0..self.num_children as usize {
            n48.keys[self.keys[i] as usize] = (i + 1) as u8;
            n48.children[i] = std::mem::replace(&mut self.children[i], MaybeUninit::uninit());
            n48.num_children += 1;
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

    fn seek_child(&self, key: u8) -> Option<&N> {
        let idx = self.index(key)?;
        Some(unsafe { self.children[idx].assume_init_ref() })
    }

    fn seek_child_mut(&mut self, key: u8) -> Option<&mut N> {
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
        self.keys[WIDTH - 1] = 255;
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
    keys: [u8; 256],
    children: Box<[MaybeUninit<N>; WIDTH]>,
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
            keys: [0; 256],
            children: Box::new(unsafe { MaybeUninit::uninit().assume_init() }),
            num_children: 0,
        }
    }

    fn shrink<const NEW_WIDTH: usize>(&mut self) -> FlatNode<N, NEW_WIDTH> {
        let mut node = FlatNode::<N, NEW_WIDTH>::new();
        for i in 0..self.keys.len() {
            let pos = self.keys[i] as usize;
            if pos != 0 {
                node.children[node.num_children as usize] =
                    mem::replace(&mut self.children[pos - 1], MaybeUninit::uninit());
                node.keys[node.num_children as usize] = i as u8;
                node.num_children += 1;
            }
        }
        self.num_children = 0;
        node
    }

    fn grow<const NEW_WIDTH: usize>(&mut self) -> Node256<N> {
        let mut n256: Node256<N> = Node256::new();

        for (k, v) in self.keys.iter().enumerate().filter(|(_, v)| **v > 0) {
            let val_idx = *v as usize;
            let old = unsafe {
                mem::replace(&mut self.children[val_idx - 1], MaybeUninit::uninit()).assume_init()
            };
            n256.add_child(k as u8, old);
        }
        self.num_children = 0;
        n256
    }
}

impl<N, const WIDTH: usize> NodeTrait<N> for Node48<N, WIDTH> {
    fn add_child(&mut self, key: u8, node: N) {
        let i = key as usize;
        if self.keys[i] != 0 || self.num_children >= WIDTH as u8 {
            return;
        }

        self.keys[i] = self.num_children + 1;
        self.children[self.num_children as usize].write(node);
        self.num_children += 1;
    }

    fn seek_child(&self, key: u8) -> Option<&N> {
        let idx = self.keys[key as usize] as usize;
        if idx > 0 {
            return Some(unsafe { self.children[idx - 1].assume_init_ref() });
        }
        None
    }

    fn seek_child_mut(&mut self, key: u8) -> Option<&mut N> {
        let idx = self.keys[key as usize] as usize;
        if idx > 0 {
            return Some(unsafe { self.children[idx].assume_init_mut() });
        }
        None
    }

    fn delete_child(&mut self, key: u8) -> Option<N> {
        let key_idx = key as usize;
        if self.keys[key_idx] == 0 {
            return None;
        }
        let val_idx = self.keys[key_idx] as usize - 1;
        let val = unsafe {
            mem::replace(&mut self.children[val_idx], MaybeUninit::uninit()).assume_init()
        };
        self.keys[key_idx] = 0;

        if self.num_children == 1 {
            self.num_children = 0;
            return Some(val);
        }

        for i in 0..self.keys.len() {
            // find key which uses last cell inside values array
            if self.keys[i] == self.num_children {
                // move value of key which points to last array cell
                self.keys[i] = val_idx as u8 + 1;
                self.children[val_idx] = mem::replace(
                    &mut self.children[(self.num_children - 1) as usize],
                    MaybeUninit::uninit(),
                );
                break;
            }
        }

        self.num_children -= 1;
        Some(val)
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
        for value in &mut self.children[..self.num_children as usize] {
            unsafe { value.assume_init_drop() }
        }
        self.num_children = 0;
    }
}

pub struct Node256<N> {
    key_mask: [u8; 32],
    children: Box<[MaybeUninit<N>; 256]>,
    num_children: usize,
}

impl<N> Default for Node256<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N> Drop for Node256<N> {
    fn drop(&mut self) {
        for value in &mut self.children[..self.num_children] {
            unsafe { value.assume_init_drop() }
        }
        self.num_children = 0;
    }
}

impl<N> Node256<N> {
    pub fn new() -> Self {
        Self {
            key_mask: [0; 32],
            children: Box::new(unsafe { MaybeUninit::uninit().assume_init() }),
            num_children: 0,
        }
    }

    #[inline]
    fn set_mask(&mut self, key: usize) {
        let byte_index = key / 8;
        let bit_index = key % 8;
        self.key_mask[byte_index] |= 1 << bit_index;
    }

    #[inline]
    fn unset_mask(&mut self, key: usize) {
        let byte_index = key / 8;
        let bit_index = key % 8;
        self.key_mask[byte_index] &= !(1 << bit_index);
    }

    #[inline]
    fn get_mask(&self, key: usize) -> bool {
        let byte_index = key / 8;
        let bit_index = key % 8;
        (self.key_mask[byte_index] & (1 << bit_index)) != 0
    }

    pub fn shrink<const NEW_WIDTH: usize>(&mut self) -> Node48<N, NEW_WIDTH> {
        let mut n48 = Node48::new();

        for i in 0..self.children.len() {
            if !self.get_mask(i) {
                continue;
            }
            n48.children[n48.num_children as usize] =
                mem::replace(&mut self.children[i], MaybeUninit::uninit());
            n48.keys[i] = n48.num_children + 1;
            n48.num_children += 1;
        }
        self.num_children = 0;
        n48
    }
}

impl<N> NodeTrait<N> for Node256<N> {
    #[inline]
    fn add_child(&mut self, key: u8, node: N) {
        self.children[key as usize] = MaybeUninit::new(node);
        self.set_mask(key as usize);
        self.num_children += 1;
    }

    #[inline]
    fn seek_child(&self, key: u8) -> Option<&N> {
        if self.get_mask(key as usize) {
            Some(unsafe { self.children[key as usize].assume_init_ref() })
        } else {
            None
        }
    }

    #[inline]
    fn seek_child_mut(&mut self, key: u8) -> Option<&mut N> {
        if self.get_mask(key as usize) {
            Some(unsafe { self.children[key as usize].assume_init_mut() })
        } else {
            None
        }
    }

    #[inline]
    fn delete_child(&mut self, key: u8) -> Option<N> {
        if self.get_mask(key as usize) {
            let i = key as usize;
            let old = std::mem::replace(&mut self.children[i], MaybeUninit::uninit());
            self.num_children -= 1;
            self.unset_mask(key as usize);
            Some(unsafe { old.assume_init() })
        } else {
            None
        }
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
    use crate::NodeTrait;

    fn node_test(mut node: impl NodeTrait<usize>, size: usize) {
        for i in 0..size {
            node.add_child(i as u8, i);
        }

        for i in 0..size {
            assert!(matches!(node.seek_child(i as u8), Some(v) if *v == i));
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
            assert!(matches!(resized.seek_child(i as u8), Some(v) if *v == i));
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
            assert!(matches!(resized.seek_child(i as u8), Some(v) if *v == i));
        }

        let mut node = super::FlatNode::<usize, 4>::new();
        node.add_child(1, 1);
        node.add_child(2, 2);
        node.add_child(3, 3);
        node.add_child(4, 4);
        assert_eq!(node.num_children(), 4);
        assert_eq!(node.seek_child(1), Some(&1));
        assert_eq!(node.seek_child(2), Some(&2));
        assert_eq!(node.seek_child(3), Some(&3));
        assert_eq!(node.seek_child(4), Some(&4));
        assert_eq!(node.seek_child(5), None);
        assert_eq!(node.seek_child_mut(1), Some(&mut 1));
        assert_eq!(node.seek_child_mut(2), Some(&mut 2));
        assert_eq!(node.seek_child_mut(3), Some(&mut 3));
        assert_eq!(node.seek_child_mut(4), Some(&mut 4));
        assert_eq!(node.seek_child_mut(5), None);
        assert_eq!(node.delete_child(1), Some(1));
        assert_eq!(node.delete_child(2), Some(2));
        assert_eq!(node.delete_child(3), Some(3));
        assert_eq!(node.delete_child(4), Some(4));
        assert_eq!(node.delete_child(5), None);
        assert_eq!(node.num_children(), 0);
    }

    #[test]
    fn test_node48() {
        node_test(super::Node48::<usize, 48>::new(), 48);

        let mut n48 = super::Node48::<u8, 48>::new();
        for i in 0..48 {
            n48.add_child(i, i);
            assert_eq!(*n48.seek_child(i).unwrap(), i);
        }
        for i in 0..48 {
            assert_eq!(*n48.seek_child(i).unwrap(), i);
        }
        for i in 0..48 {
            assert_eq!(n48.delete_child(i).unwrap(), i);
        }
        for i in 0..48 {
            assert!(n48.seek_child(i as u8).is_none());
        }

        // resize from 48 to 16
        let mut node = super::Node48::<u8, 48>::new();
        for i in 0..16 {
            node.add_child(i as u8, i);
        }

        let resized = node.shrink::<16>();
        assert_eq!(resized.num_children, 16);
        for i in 0..16 {
            assert!(matches!(resized.seek_child(i as u8), Some(v) if *v == i));
        }

        // resize from 48 to 4
        let mut node = super::Node48::<u8, 48>::new();
        for i in 0..4 {
            node.add_child(i as u8, i);
        }
        let resized = node.shrink::<4>();
        assert_eq!(resized.num_children, 4);
        for i in 0..4 {
            assert!(matches!(resized.seek_child(i as u8), Some(v) if *v == i));
        }

        // resize from 48 to 256
        let mut node = super::Node48::<u8, 48>::new();
        for i in 0..48 {
            node.add_child(i as u8, i);
        }

        let resized = node.grow::<256>();
        assert_eq!(resized.num_children, 48);
        for i in 0..48 {
            assert!(matches!(resized.seek_child(i as u8), Some(v) if *v == i));
        }
    }

    #[test]
    fn test_node256() {
        node_test(super::Node256::<usize>::new(), 255);

        let mut n256 = super::Node256::new();
        for i in 0..255 {
            n256.add_child(i, i);
            assert_eq!(*n256.seek_child(i).unwrap(), i);
            assert_eq!(n256.delete_child(i), Some(i));
            assert_eq!(n256.seek_child(i), None);
        }

        // resize from 256 to 48
        let mut node = super::Node256::new();
        for i in 0..48 {
            node.add_child(i, i);
        }

        let resized = node.shrink::<48>();
        assert_eq!(resized.num_children, 48);
        for i in 0..48 {
            assert!(matches!(resized.seek_child(i as u8), Some(v) if *v == i));
        }
    }
}
