#[allow(warnings)]
mod art;
pub mod node;

use std::cmp::min;


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

// Owned vec size key.
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

    fn prefix_after(&self, pos: usize) -> &[u8] {
        &self.data[pos..self.length()]
    }
}
