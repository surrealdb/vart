// #[allow(warnings)]
pub mod art;
pub mod iter;
pub mod node;
pub mod snapshot;

use std::cmp::{Ord, Ordering, PartialOrd};
use std::error::Error;
use std::fmt;
use std::fmt::Debug;
use std::str::FromStr;

// "Partial" in the Adaptive Radix Tree paper refers to "partial keys", a technique employed
// for prefix compression in this data structure. Instead of storing entire keys in the nodes,
// ART nodes often only store partial keys, which are the differing prefixes of the keys.
// This approach significantly reduces the memory requirements of the data structure.
// Key is a trait that provides an abstraction for partial keys.
pub trait Key {
    fn at(&self, pos: usize) -> u8;
    fn len(&self) -> usize;
    fn prefix_before(&self, length: usize) -> Self;
    fn prefix_after(&self, start: usize) -> Self;
    fn longest_common_prefix(&self, slice: &[u8]) -> usize;
    fn as_slice(&self) -> &[u8];
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub trait KeyTrait:
    Key + Clone + PartialEq + PartialOrd + Ord + Debug + for<'a> From<&'a [u8]>
{
}
impl<T: Key + Clone + PartialOrd + PartialEq + Ord + Debug + for<'a> From<&'a [u8]>> KeyTrait
    for T
{
}

/*
    Key trait implementations
*/

// Source: https://www.the-paper-trail.org/post/art-paper-notes/
//
// Keys can be of two types:
// 1. Fixed-length datatypes such as 128-bit integers, or strings of exactly 64-bytes,
// don’t have any problem because there can, by construction, never be any key that’s
// a prefix of any other.
//
// 2. Variable-length datatypes such as general strings, can be transformed into types
// where no key is the prefix of any other by a simple trick: append the NULL byte to every key.
// The NULL byte, as it does in C-style strings, indicates that this is the end of the key, and
// no characters can come after it. Therefore no string with a null-byte can be a prefix of any other,
// because no string can have any characters after the NULL byte!
//
#[derive(Clone, Debug, Eq)]
pub struct FixedSizeKey<const SIZE: usize> {
    content: [u8; SIZE],
    len: usize,
}

impl<const SIZE: usize> PartialEq for FixedSizeKey<SIZE> {
    fn eq(&self, other: &Self) -> bool {
        self.content[..self.len] == other.content[..other.len]
    }
}

impl<const SIZE: usize> PartialOrd for FixedSizeKey<SIZE> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<const SIZE: usize> Ord for FixedSizeKey<SIZE> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.content[..self.len].cmp(&other.content[..other.len])
    }
}

impl<const SIZE: usize> FixedSizeKey<SIZE> {
    // Create new instance with data ending in zero byte
    pub fn create_key(src: &[u8]) -> Self {
        debug_assert!(src.len() < SIZE);
        let mut content = [0; SIZE];
        content[..src.len()].copy_from_slice(src);
        content[src.len()] = 0;
        Self {
            content,
            len: src.len() + 1,
        }
    }

    // Create new instance from slice
    pub fn from_slice(src: &[u8]) -> Self {
        debug_assert!(src.len() <= SIZE);
        let mut content = [0; SIZE];
        content[..src.len()].copy_from_slice(src);
        Self {
            content,
            len: src.len(),
        }
    }

    pub fn from_string(s: &String) -> Self {
        assert!(s.len() < SIZE, "data length is greater than array length");
        let mut arr = [0; SIZE];
        arr[..s.len()].copy_from_slice(s.as_bytes());
        Self {
            content: arr,
            len: s.len() + 1,
        }
    }
}

impl<const SIZE: usize> Key for FixedSizeKey<SIZE> {
    // Returns slice of the internal data up to the actual length
    fn as_slice(&self) -> &[u8] {
        &self.content[..self.len]
    }

    // Creates a new instance of FixedSizeKey consisting only of the initial part of the content
    fn prefix_before(&self, length: usize) -> Self {
        assert!(length <= self.len);
        Self::from_slice(&self.content[..length])
    }

    // Creates a new instance of FixedSizeKey excluding the initial part of the content
    fn prefix_after(&self, start: usize) -> Self {
        assert!(start <= self.len);
        Self::from_slice(&self.content[start..self.len])
    }

    #[inline(always)]
    fn at(&self, pos: usize) -> u8 {
        assert!(pos < self.len);
        self.content[pos]
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }

    // Returns the length of the longest common prefix between this object's content and the given byte slice
    fn longest_common_prefix(&self, key: &[u8]) -> usize {
        let len = self.len.min(key.len()).min(SIZE);
        self.content[..len]
            .iter()
            .zip(key)
            .take_while(|&(a, &b)| *a == b)
            .count()
    }
}

impl<const SIZE: usize> FromStr for FixedSizeKey<SIZE> {
    type Err = TrieError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() >= SIZE {
            return Err(TrieError::FixedSizeKeyLengthExceeded);
        }
        let mut arr = [0; SIZE];
        arr[..s.len()].copy_from_slice(s.as_bytes());
        Ok(Self {
            content: arr,
            len: s.len() + 1,
        })
    }
}

impl<const SIZE: usize> From<&[u8]> for FixedSizeKey<SIZE> {
    fn from(src: &[u8]) -> Self {
        Self::from_slice(src)
    }
}

impl<const N: usize> From<u8> for FixedSizeKey<N> {
    fn from(data: u8) -> Self {
        Self::from_slice(data.to_be_bytes().as_ref())
    }
}

impl<const N: usize> From<u16> for FixedSizeKey<N> {
    fn from(data: u16) -> Self {
        Self::from_slice(data.to_be_bytes().as_ref())
    }
}

impl<const N: usize> From<u64> for FixedSizeKey<N> {
    fn from(data: u64) -> Self {
        Self::from_slice(data.to_be_bytes().as_ref())
    }
}

impl<const N: usize> From<&str> for FixedSizeKey<N> {
    fn from(data: &str) -> Self {
        Self::from_str(data).unwrap()
    }
}

impl<const N: usize> From<String> for FixedSizeKey<N> {
    fn from(data: String) -> Self {
        Self::from_string(&data)
    }
}
impl<const N: usize> From<&String> for FixedSizeKey<N> {
    fn from(data: &String) -> Self {
        Self::from_string(data)
    }
}

// A VariableSizeKey is a variable-length datatype with NULL byte appended to it.
#[derive(Clone, PartialEq, PartialOrd, Ord, Eq, Debug)]
pub struct VariableSizeKey {
    data: Vec<u8>,
}

impl VariableSizeKey {
    pub fn key(src: &[u8]) -> Self {
        let mut data = Vec::with_capacity(src.len() + 1);
        data.extend_from_slice(src);
        data.push(0);
        Self { data }
    }

    pub fn from_slice(src: &[u8]) -> Self {
        Self {
            data: Vec::from(src),
        }
    }

    pub fn to_slice(&self) -> &[u8] {
        &self.data
    }

    pub fn terminate(&self) -> Self {
        let mut data = Vec::with_capacity(self.data.len() + 1);
        data.extend_from_slice(&self.data);
        data.push(0);
        Self { data }
    }

    pub fn from_string(s: &String) -> Self {
        let mut data = Vec::with_capacity(s.len() + 1);
        data.extend_from_slice(s.as_bytes());
        data.push(0);
        Self { data }
    }

    pub fn from(data: Vec<u8>) -> Self {
        Self { data }
    }

    pub fn from_slice_with_termination(src: &[u8]) -> Self {
        let mut data = Vec::with_capacity(src.len() + 1);
        data.extend_from_slice(src);
        data.push(0);
        Self { data }
    }
}

impl FromStr for VariableSizeKey {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut data = Vec::with_capacity(s.len() + 1);
        data.extend_from_slice(s.as_bytes());
        data.push(0);
        Ok(Self { data })
    }
}

impl From<&[u8]> for VariableSizeKey {
    fn from(src: &[u8]) -> Self {
        Self::from_slice(src)
    }
}

impl Key for VariableSizeKey {
    fn prefix_before(&self, length: usize) -> Self {
        assert!(length <= self.data.len());
        VariableSizeKey::from_slice(&self.data[..length])
    }

    fn prefix_after(&self, start: usize) -> Self {
        assert!(start <= self.data.len());
        VariableSizeKey::from_slice(&self.data[start..self.data.len()])
    }

    #[inline(always)]
    fn at(&self, pos: usize) -> u8 {
        assert!(pos < self.data.len());
        self.data[pos]
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.data.len()
    }

    // Returns the length of the longest common prefix between this object's content and the given byte slice
    fn longest_common_prefix(&self, key: &[u8]) -> usize {
        let len = self.data.len().min(key.len());
        self.data[..len]
            .iter()
            .zip(key)
            .take_while(|&(a, &b)| *a == b)
            .count()
    }

    fn as_slice(&self) -> &[u8] {
        &self.data[..self.data.len()]
    }
}

/*
    BitSet implementation
*/

#[derive(Clone)]
pub struct BitSet<const SIZE: usize> {
    bits: [bool; SIZE],
}

impl<const SIZE: usize> Default for BitSet<SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const SIZE: usize> BitSet<SIZE> {
    pub fn new() -> Self {
        Self {
            bits: [false; SIZE],
        }
    }

    pub fn first_empty(&self) -> Option<usize> {
        self.bits.iter().position(|&bit| !bit)
    }

    pub fn first_set(&self) -> Option<usize> {
        self.bits.iter().position(|&bit| bit)
    }

    pub fn set(&mut self, pos: usize) {
        if pos < self.bits.len() {
            self.bits[pos] = true;
        }
    }

    pub fn unset(&mut self, pos: usize) {
        if pos < self.bits.len() {
            self.bits[pos] = false;
        }
    }

    pub fn check(&self, pos: usize) -> bool {
        pos < self.bits.len() && self.bits[pos]
    }

    pub fn clear(&mut self) {
        for bit in &mut self.bits {
            *bit = false;
        }
    }

    pub fn last(&self) -> Option<usize> {
        self.bits.iter().rposition(|&bit| bit)
    }

    pub fn is_empty(&self) -> bool {
        self.bits.iter().all(|&bit| !bit)
    }

    pub fn size(&self) -> usize {
        self.bits.len()
    }

    pub fn capacity(&self) -> usize {
        self.bits.len()
    }
}

// Define a custom error enum representing different error cases for the Trie
#[derive(Clone, Debug)]
pub enum TrieError {
    IllegalArguments,
    NotFound,
    KeyNotFound,
    SnapshotNotFound,
    SnapshotEmpty,
    SnapshotNotClosed,
    SnapshotAlreadyClosed,
    SnapshotReadersNotClosed,
    TreeAlreadyClosed,
    FixedSizeKeyLengthExceeded,
    Other(String),
}

impl Error for TrieError {}

// Implement the Display trait to define how the error should be formatted as a string
impl fmt::Display for TrieError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TrieError::IllegalArguments => write!(f, "Illegal arguments"),
            TrieError::NotFound => write!(f, "Not found"),
            TrieError::KeyNotFound => write!(f, "Key not found"),
            TrieError::SnapshotNotFound => write!(f, "Snapshot not found"),
            TrieError::SnapshotNotClosed => write!(f, "Snapshot not closed"),
            TrieError::SnapshotAlreadyClosed => write!(f, "Snapshot already closed"),
            TrieError::SnapshotReadersNotClosed => {
                write!(f, "Readers in the snapshot are not closed")
            }
            TrieError::TreeAlreadyClosed => write!(f, "Tree already closed"),
            TrieError::Other(ref message) => write!(f, "Other error: {}", message),
            TrieError::SnapshotEmpty => write!(f, "Snapshot is empty"),
            TrieError::FixedSizeKeyLengthExceeded => write!(f, "Fixed key length exceeded"),
        }
    }
}
