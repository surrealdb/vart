#![forbid(unsafe_code)]
pub mod art;
pub mod iter;
pub mod node;

use std::cmp::{Ord, Ordering, PartialOrd};
use std::error::Error;
use std::fmt;
use std::fmt::Debug;
use std::str::FromStr;

/// Key abstraction for Adaptive Radix Tree operations, providing prefix extraction,
/// longest common prefix calculation, and byte-wise indexing.
pub trait Key {
    fn at(&self, pos: usize) -> u8;
    fn len(&self) -> usize;
    fn prefix_before(&self, length: usize) -> &[u8];
    fn prefix_after(&self, start: usize) -> &[u8];
    fn longest_common_prefix(&self, slice: &[u8]) -> usize;
    fn as_slice(&self) -> &[u8];
    fn extend(&self, other: &Self) -> Self;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub trait KeyTrait: Key + Clone + Ord + Debug + for<'a> From<&'a [u8]> {}
impl<T: Key + Clone + Ord + Debug + for<'a> From<&'a [u8]>> KeyTrait for T {}

/*
    Key trait implementations
*/

/// Fixed-capacity byte array key, suitable for integers, UUIDs, and fixed-length hashes.
/// Eliminates heap allocations by inlining key bytes up to `SIZE`.
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
    /// Create a new instance from a byte slice with an explicit trailing null byte appended.
    pub fn create_null_terminated(src: &[u8]) -> Self {
        Self::create_key(src)
    }

    /// Create new instance with data ending in zero byte
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

    pub fn from_string(s: &str) -> Self {
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
    fn as_slice(&self) -> &[u8] {
        &self.content[..self.len]
    }

    fn prefix_before(&self, length: usize) -> &[u8] {
        assert!(length <= self.len);
        &self.content[..length]
    }

    fn prefix_after(&self, start: usize) -> &[u8] {
        assert!(start <= self.len);
        &self.content[start..self.len]
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

    fn longest_common_prefix(&self, key: &[u8]) -> usize {
        let len = self.len.min(key.len()).min(SIZE);
        self.content[..len]
            .iter()
            .zip(key)
            .take_while(|&(a, &b)| *a == b)
            .count()
    }

    fn extend(&self, other: &Self) -> Self {
        assert!(self.len + other.len <= SIZE);
        let mut content = [0; SIZE];
        content[..self.len].copy_from_slice(&self.content[..self.len]);
        content[self.len..self.len + other.len].copy_from_slice(&other.content[..other.len]);
        Self {
            content,
            len: self.len + other.len,
        }
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

#[allow(clippy::fallible_impl_from)]
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
        Self::from_string(data.as_str())
    }
}
impl<const SIZE: usize> Default for FixedSizeKey<SIZE> {
    fn default() -> Self {
        Self {
            content: [0; SIZE],
            len: 0,
        }
    }
}

impl<const SIZE: usize> AsRef<[u8]> for FixedSizeKey<SIZE> {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<const SIZE: usize> std::borrow::Borrow<[u8]> for FixedSizeKey<SIZE> {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<const SIZE: usize> std::ops::Deref for FixedSizeKey<SIZE> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<const SIZE: usize> std::hash::Hash for FixedSizeKey<SIZE> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl Key for byteslice::ByteSlice {
    #[inline(always)]
    fn at(&self, pos: usize) -> u8 {
        assert!(pos < self.len());
        self[pos]
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.len()
    }

    #[inline(always)]
    fn prefix_before(&self, length: usize) -> &[u8] {
        assert!(length <= self.len());
        &self[..length]
    }

    #[inline(always)]
    fn prefix_after(&self, start: usize) -> &[u8] {
        assert!(start <= self.len());
        &self[start..]
    }

    #[inline(always)]
    fn longest_common_prefix(&self, key: &[u8]) -> usize {
        let len = self.len().min(key.len());
        self[..len]
            .iter()
            .zip(key)
            .take_while(|&(a, &b)| *a == b)
            .count()
    }

    #[inline(always)]
    fn as_slice(&self) -> &[u8] {
        self
    }

    #[inline]
    fn extend(&self, other: &Self) -> Self {
        let mut v = Vec::with_capacity(self.len() + other.len());
        v.extend_from_slice(self);
        v.extend_from_slice(other);
        byteslice::ByteSlice::from(v)
    }
}

// VariableSizeKey is a variable-length key type stored as a byte vector.
#[derive(Clone, PartialEq, PartialOrd, Ord, Eq, Debug, Default, Hash)]
pub struct VariableSizeKey {
    data: byteslice::ByteSlice,
}

impl VariableSizeKey {
    #[inline]
    pub fn key(src: &[u8]) -> Self {
        Self::from_slice(src)
    }

    #[inline]
    pub fn from_slice(src: &[u8]) -> Self {
        Self {
            data: byteslice::ByteSlice::from(src),
        }
    }

    #[inline]
    pub fn to_slice(&self) -> &[u8] {
        &self.data
    }

    #[inline]
    pub fn from_string(s: &str) -> Self {
        Self::from_slice(s.as_bytes())
    }

    #[inline]
    pub fn is_inline(&self) -> bool {
        self.data.is_inline()
    }
}

impl From<Vec<u8>> for VariableSizeKey {
    #[inline]
    fn from(data: Vec<u8>) -> Self {
        Self {
            data: byteslice::ByteSlice::from(data),
        }
    }
}

impl From<Box<[u8]>> for VariableSizeKey {
    #[inline]
    fn from(data: Box<[u8]>) -> Self {
        Self {
            data: byteslice::ByteSlice::from(data.into_vec()),
        }
    }
}

impl From<&str> for VariableSizeKey {
    #[inline]
    fn from(s: &str) -> Self {
        Self::from_slice(s.as_bytes())
    }
}

impl From<String> for VariableSizeKey {
    #[inline]
    fn from(s: String) -> Self {
        Self {
            data: byteslice::ByteSlice::from(s.into_bytes()),
        }
    }
}

impl From<byteslice::ByteSlice> for VariableSizeKey {
    #[inline]
    fn from(data: byteslice::ByteSlice) -> Self {
        Self { data }
    }
}

impl From<VariableSizeKey> for byteslice::ByteSlice {
    #[inline]
    fn from(k: VariableSizeKey) -> Self {
        k.data
    }
}

impl AsRef<[u8]> for VariableSizeKey {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.data
    }
}

impl std::borrow::Borrow<[u8]> for VariableSizeKey {
    #[inline]
    fn borrow(&self) -> &[u8] {
        &self.data
    }
}

impl std::ops::Deref for VariableSizeKey {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl FromStr for VariableSizeKey {
    type Err = std::convert::Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from_slice(s.as_bytes()))
    }
}

impl From<&[u8]> for VariableSizeKey {
    #[inline]
    fn from(src: &[u8]) -> Self {
        Self::from_slice(src)
    }
}

impl Key for VariableSizeKey {
    #[inline(always)]
    fn prefix_before(&self, length: usize) -> &[u8] {
        self.data.prefix_before(length)
    }

    #[inline(always)]
    fn prefix_after(&self, start: usize) -> &[u8] {
        self.data.prefix_after(start)
    }

    #[inline(always)]
    fn at(&self, pos: usize) -> u8 {
        self.data.at(pos)
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.data.len()
    }

    #[inline(always)]
    fn longest_common_prefix(&self, key: &[u8]) -> usize {
        self.data.longest_common_prefix(key)
    }

    #[inline(always)]
    fn as_slice(&self) -> &[u8] {
        self.data.as_slice()
    }

    #[inline]
    fn extend(&self, other: &Self) -> Self {
        Self {
            data: self.data.extend(&other.data),
        }
    }
}

// Define a custom error enum representing different error cases for the Trie
#[derive(Clone, Debug)]
pub enum TrieError {
    FixedSizeKeyLengthExceeded,
    VersionIsOld,
    RootIsNotUniquelyOwned,
    SnapshotOlderThanRoot,
}

impl Error for TrieError {}

// Implement the Display trait to define how the error should be formatted as a string
impl fmt::Display for TrieError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TrieError::FixedSizeKeyLengthExceeded => write!(f, "Fixed key length exceeded"),
            TrieError::VersionIsOld => {
                write!(f, "Given version is older than root's current version")
            }
            TrieError::RootIsNotUniquelyOwned => write!(f, "Root arc is not uniquely owned"),
            TrieError::SnapshotOlderThanRoot => write!(f, "Snapshot is older than root"),
        }
    }
}

const _: () = {
    fn assert_send_sync<T: Send + Sync>() {}
    fn check<P: KeyTrait + Send + Sync, V: Clone + Send + Sync>() {
        assert_send_sync::<art::Tree<P, V>>();
        assert_send_sync::<art::Node<P, V>>();
        assert_send_sync::<iter::Iter<'_, P, V>>();
        assert_send_sync::<FixedSizeKey<16>>();
        assert_send_sync::<VariableSizeKey>();
        assert_send_sync::<byteslice::ByteSlice>();
    }
    let _ = check::<FixedSizeKey<16>, usize>;
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_byteslice_sso_and_key() {
        use byteslice::ByteSlice;

        // 1. SSO short key (<= 20 bytes) -> inline
        let short = VariableSizeKey::from("user:0001:profile");
        assert_eq!(short.len(), 17);
        assert!(short.is_inline());
        assert_eq!(&*short, b"user:0001:profile");

        // 2. Long key (> 20 bytes) -> heap
        let long = VariableSizeKey::from("user:00000000000001:settings:advanced:profile");
        assert_eq!(long.len(), 45);
        assert!(!long.is_inline());

        // 3. Tree works directly with ByteSlice as Key
        let mut bs_tree: crate::art::Tree<ByteSlice, i32> = crate::art::Tree::new();
        let bs_key = ByteSlice::from("tenant_42");
        bs_tree.insert(&bs_key, 999, 1, 10).unwrap();
        assert_eq!(bs_tree.get(&bs_key, 0).unwrap().0, 999);
        assert_eq!(bs_tree.get_by_slice(b"tenant_42", 0).unwrap().0, 999);
    }

    #[test]
    fn test_key_traits() {
        use std::collections::HashSet;

        let vsk1 = VariableSizeKey::from("hello");
        let vsk2: VariableSizeKey = "hello".to_string().into();
        let vsk3: VariableSizeKey = b"hello"[..].into();
        assert_eq!(vsk1, vsk2);
        assert_eq!(vsk2, vsk3);
        assert_eq!(&*vsk1, b"hello");

        let mut set = HashSet::new();
        set.insert(vsk1);
        assert!(set.contains(&vsk2));

        let fsk: FixedSizeKey<8> = FixedSizeKey::from_slice(b"test");
        assert_eq!(&*fsk, b"test");
        let mut fset = HashSet::new();
        fset.insert(fsk.clone());
        assert!(fset.contains(&fsk));
    }

    #[test]
    fn test_fixed_size_key_extend_to_capacity() {
        let k1: FixedSizeKey<8> = FixedSizeKey::from_slice(b"1234");
        let k2: FixedSizeKey<8> = FixedSizeKey::from_slice(b"5678");
        let k3 = k1.extend(&k2);
        assert_eq!(k3.len(), 8);
        assert_eq!(k3.as_slice(), b"12345678");
    }
}
