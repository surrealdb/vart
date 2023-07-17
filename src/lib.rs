#[allow(warnings)]
mod art;
pub mod node;

use std::{cmp::min, fmt::Debug};



pub trait Prefix {
    fn at(&self, pos: usize) -> u8;
    fn length(&self) -> usize;
    fn prefix_before(&self, length: usize) -> Self;
    fn prefix_after(&self, start: usize) -> Self;
    fn longest_common_prefix(&self, slice: &[u8]) -> usize;
}

pub trait Key: Clone {
    fn at(&self, pos: usize) -> u8;
    fn length(&self) -> usize;
    fn prefix_after(&self, pos: usize) -> &[u8];
    fn as_slice(&self) -> &[u8] {
        self.prefix_after(0)
    }
}

pub trait PrefixTrait: Prefix + Clone + PartialEq + Debug + for<'a> From<&'a [u8]> {}
impl<T: Prefix + Clone + PartialEq + Debug + for<'a> From<&'a [u8]>> PrefixTrait for T {}


/*
    Partial trait implementations
*/

#[derive(Clone, Debug, Eq)]
pub struct ArrayPrefix<const SIZE: usize> {
    data: [u8; SIZE],
    len: usize,
}

impl<const SIZE: usize> PartialEq for ArrayPrefix<SIZE> {
    fn eq(&self, other: &Self) -> bool {
        self.data[..self.len] == other.data[..other.len]
    }
}
impl<const SIZE: usize> ArrayPrefix<SIZE> {
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

impl<const SIZE: usize> Prefix for ArrayPrefix<SIZE> {
    fn prefix_before(&self, length: usize) -> Self {
        assert!(length <= self.len);
        ArrayPrefix::from_slice(&self.data[..length])
    }

    fn prefix_after(&self, start: usize) -> Self {
        assert!(start <= self.len);
        ArrayPrefix::from_slice(&self.data[start..self.len])
    }

    #[inline(always)]
    fn at(&self, pos: usize) -> u8 {
        assert!(pos < self.len);
        self.data[pos]
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

impl<const SIZE: usize> From<&[u8]> for ArrayPrefix<SIZE> {
    fn from(src: &[u8]) -> Self {
        Self::from_slice(src)
    }
}

impl<const SIZE: usize, K: Key> From<K> for ArrayPrefix<SIZE> {
    fn from(src: K) -> Self {
        Self::from_slice(src.as_slice())
    }
}

/*
    Key trait implementations
*/

#[derive(Clone)]
pub struct VectorKey {
    data: Vec<u8>,
}

impl VectorKey {
    pub fn from_string(s: &String) -> Self {
        let mut data = Vec::with_capacity(s.len() + 1);
        data.extend_from_slice(s.as_bytes());
        data.push(0);
        Self { data }
    }

    pub fn from_str(s: &str) -> Self {
        let mut data = Vec::with_capacity(s.len() + 1);
        data.extend_from_slice(s.as_bytes());
        data.push(0);
        Self { data }
    }

    pub fn from_slice(data: &[u8]) -> Self {
        let data = Vec::from(data);
        Self { data }
    }

    pub fn from(data: Vec<u8>) -> Self {
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

    fn prefix_after(&self, pos: usize) -> &[u8] {
        &self.data[pos..]
    }
}

/*
    Vec Array implementation
*/


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
    pub fn erase(&mut self, pos: usize) -> Option<X> {
        self.storage[pos].take()
    }

    pub fn clear(&mut self) {
        self.storage.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
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
}
