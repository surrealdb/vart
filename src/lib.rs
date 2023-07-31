// #[allow(warnings)]
mod art;
pub mod node;

use std::fmt::Debug;

// "Partial" in the Adaptive Radix Tree paper refers to "partial keys", a technique employed
// for prefix compression in this data structure. Instead of storing entire keys in the nodes,
// ART nodes often only store partial keys, which are the differing prefixes of the keys.
// This approach significantly reduces the memory requirements of the data structure.
// Prefix is a trait that provides an abstraction for partial keys.
pub trait Prefix {
    fn at(&self, pos: usize) -> u8;
    fn length(&self) -> usize;
    fn prefix_before(&self, length: usize) -> Self;
    fn prefix_after(&self, start: usize) -> Self;
    fn longest_common_prefix(&self, slice: &[u8]) -> usize;
}

/// The `Key` trait provides a specific abstraction for keys, which are sequences of bytes.
pub trait Key: Clone {
    /// Returns the byte at the specified position.
    fn at(&self, pos: usize) -> u8;

    /// Returns the length of the key.
    fn length(&self) -> usize;

    /// Returns a byte slice that starts from the specified position in the key.
    fn prefix_after(&self, pos: usize) -> &[u8];

    /// Returns a byte slice that represents the key.
    fn as_slice(&self) -> &[u8] {
        self.prefix_after(0)
    }
}
pub trait PrefixTrait: Prefix + Clone + PartialEq + Debug + for<'a> From<&'a [u8]> {}
impl<T: Prefix + Clone + PartialEq + Debug + for<'a> From<&'a [u8]>> PrefixTrait for T {}

/*
    Prefix trait implementations
*/

#[derive(Clone, Debug, Eq)]
pub struct ArrayPrefix<const SIZE: usize> {
    content: [u8; SIZE],
    len: usize,
}

impl<const SIZE: usize> PartialEq for ArrayPrefix<SIZE> {
    fn eq(&self, other: &Self) -> bool {
        self.content[..self.len] == other.content[..other.len]
    }
}

impl<const SIZE: usize> ArrayPrefix<SIZE> {
    // Create new instance with data ending in zero byte
    pub fn create_key(src: &[u8]) -> Self {
        assert!(src.len() < SIZE);
        let mut content = [0; SIZE];
        content[..src.len()].copy_from_slice(src);
        content[src.len()] = 0;
        Self {
            content,
            len: src.len() + 1,
        }
    }

    // Create new instance from slice
    pub fn from_byte_slice(src: &[u8]) -> Self {
        assert!(src.len() <= SIZE);
        let mut content = [0; SIZE];
        content[..src.len()].copy_from_slice(src);
        Self {
            content,
            len: src.len(),
        }
    }

    // Returns slice of the internal data up to the actual length
    pub fn as_byte_slice(&self) -> &[u8] {
        &self.content[..self.len]
    }
}

impl<const SIZE: usize> Prefix for ArrayPrefix<SIZE> {
    // Creates a new instance of ArrayPrefix consisting only of the initial part of the content
    fn prefix_before(&self, length: usize) -> Self {
        assert!(length <= self.len);
        Self::from_byte_slice(&self.content[..length])
    }

    // Creates a new instance of ArrayPrefix excluding the initial part of the content
    fn prefix_after(&self, start: usize) -> Self {
        assert!(start <= self.len);
        Self::from_byte_slice(&self.content[start..self.len])
    }

    #[inline(always)]
    fn at(&self, pos: usize) -> u8 {
        assert!(pos < self.len);
        self.content[pos]
    }

    #[inline(always)]
    fn length(&self) -> usize {
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

impl<const SIZE: usize> From<&[u8]> for ArrayPrefix<SIZE> {
    fn from(src: &[u8]) -> Self {
        Self::from_byte_slice(src)
    }
}

impl<const SIZE: usize, K: Key> From<K> for ArrayPrefix<SIZE> {
    fn from(src: K) -> Self {
        Self::from_byte_slice(src.as_slice())
    }
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
// A VectorKey is a variable-length datatype with NULL byte appended to it.
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

/// A struct `VecArray` is a generic wrapper over a Vector that can store elements of type `X`.
/// It has a pre-defined constant capacity `WIDTH`. The elements are stored in a `Vec<Option<X>>`,
/// allowing for storage to be dynamically allocated and deallocated.
#[derive(Clone)]
pub struct VecArray<X, const WIDTH: usize> {
    storage: Vec<Option<X>>,
}

/// This is an implementation of the Default trait for VecArray. It simply calls the `new` function.
impl<X, const WIDTH: usize> Default for VecArray<X, WIDTH> {
    fn default() -> Self {
        Self::new()
    }
}

impl<X, const WIDTH: usize> VecArray<X, WIDTH> {
    /// This function constructs a new VecArray with a `WIDTH` number of `Option<X>` elements.
    pub fn new() -> Self {
        Self {
            storage: Vec::with_capacity(WIDTH),
        }
    }

    /// This function adds a new element `x` to the VecArray at the first available position. If the
    /// VecArray is full, it automatically resizes to make room for more elements. It returns the
    /// position where the element was inserted.
    pub fn push(&mut self, x: X) -> usize {
        let pos = self.first_free_pos();
        self.storage[pos] = Some(x);
        pos
    }

    /// This function removes and returns the last element in the VecArray if it exists.
    pub fn pop(&mut self) -> Option<X> {
        self.last_used_pos()
            .and_then(|pos| self.storage[pos].take())
    }

    /// This function returns a reference to the last element in the VecArray, if it exists.
    pub fn last(&self) -> Option<&X> {
        self.last_used_pos()
            .and_then(|pos| self.storage[pos].as_ref())
    }

    /// This function returns the position of the last used (non-None) element in the VecArray, if it exists.
    #[inline]
    pub fn last_used_pos(&self) -> Option<usize> {
        self.storage.iter().rposition(Option::is_some)
    }

    /// This function finds the position of the first free (None) slot in the VecArray. If all slots are filled,
    /// it expands the VecArray and returns the position of the new slot.
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

    /// This function returns an `Option` containing a reference to the element at the given position, if it exists.
    #[inline]
    pub fn get(&self, pos: usize) -> Option<&X> {
        self.storage.get(pos).and_then(Option::as_ref)
    }

    /// This function returns an `Option` containing a mutable reference to the element at the given position, if it exists.
    #[inline]
    pub fn get_mut(&mut self, pos: usize) -> Option<&mut X> {
        self.storage.get_mut(pos).and_then(Option::as_mut)
    }

    /// This function sets the element at the given position to the provided value. If the position is out of bounds,
    /// it automatically resizes the VecArray to make room for more elements.
    #[inline]
    pub fn set(&mut self, pos: usize, x: X) {
        if pos < self.storage.len() {
            self.storage[pos] = Some(x);
        } else {
            self.storage.resize_with(pos + 1, || None);
            self.storage[pos] = Some(x);
        }
    }

    /// This function removes the element at the given position from the VecArray, returning it if it exists.
    #[inline]
    pub fn erase(&mut self, pos: usize) -> Option<X> {
        self.storage[pos].take()
    }

    /// This function clears the VecArray, removing all elements.
    pub fn clear(&mut self) {
        self.storage.clear();
    }

    /// This function checks if the VecArray is empty, returning `true` if it is and `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }

    /// This function returns an iterator over the positions of all the used (non-None) elements in the VecArray.
    pub fn iter_keys(&self) -> impl DoubleEndedIterator<Item = usize> + '_ {
        self.storage.iter().enumerate().filter_map(
            |(i, x)| {
                if x.is_some() {
                    Some(i)
                } else {
                    None
                }
            },
        )
    }

    /// This function returns an iterator over pairs of positions and references to all the used (non-None) elements in the VecArray.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (usize, &X)> {
        self.storage
            .iter()
            .enumerate()
            .filter_map(|(i, x)| x.as_ref().map(|v| (i, v)))
    }
}
