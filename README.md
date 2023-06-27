# tart

This repository contains an implementation of the Timed Adaptive Radix Trie data structure in Rust. The Adaptive Radix Trie is a highly efficient indexing data structure that provides fast key-value lookups and efficient memory usage.

## Goals

- Adaptive Radix Trie: Efficient storage and retrieval of key-value pairs using an adaptive radix tree data structure.
- Copy-on-Write (COW): Make efficient and space-saving copies of the trie, enabling efficient updates and minimizing memory usage.
- Snapshots: Capture the current state of the trie and create immutable snapshots, allowing for point-in-time views of the data.
- Iterators: Traverse the key-value pairs in the trie using forward and backward iterators, enabling efficient data exploration.

## Roadmap

- 1) Basic Trie Functionality
  - Implement the core functionality of the adaptive radix trie, including insertion, deletion, and lookup operations based on the ART paper.
  - Add basic tests and benchmarks to ensure correctness and performance.

- 2) Copy-on-Write (COW) Support
  -  Introduce time-based copy-on-write functionality to create snapshots at specific points in time.
  - Implement mechanisms to efficiently manage time-based snapshots and retrieval.
  - Enhance testing and benchmarks to validate time-based COW.

- 3) Snapshot Support
  - Add support for capturing and creating immutable snapshots of the trie.
  - Design an efficient mechanism to manage multiple snapshots.
  - Enhance tests and benchmarks to cover snapshot-related functionality.

## Todo Features

- Implement Delete/Lookup operatrion on Trie
- Add tests on ART
- Implement CoW support by adding timestamp to each node
- Implement Snapshot support
- Implement support for range queries, allowing efficient retrieval of key-value pairs within a given key range.
- Investigate and optimize the trie's memory usage and space efficiency.
- Improve performance by optimizing the fixed sized keys and partials used in the trie.
- Add benches against BTreeMap and HashMap.
- Provide comprehensive documentation and usage examples for easy integration and understanding.


Please note that the roadmap is subject to change and will be updated as new features and improvements are planned or implemented.