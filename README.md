# vart: Versioned Adaptive Radix Trie for Rust

vart is a Rust library that implements an immutable Versioned Adaptive Radix Trie data structure. It allows you to efficiently manage key-value pairs with multiple versions and timestamps, making it a useful datastructure for applications that require tracking changes over time and enabling snapshot reads. With vart, you can handle versioned data, insert, delete, and query key-value items based on specific versions.

![License](https://img.shields.io/badge/license-Apache_License_2.0-00bfff.svg?style=flat-square)

## Features

- **Immutable:** Built on an immutable radix trie data structure employing copy-on-write semantics. This design allows for the storage and retrieval of multiple versions of the same key.

- **Version Tracking:** Track modifications to the key and manage multiple versions of the same key within the data structure.

- **Snapshot Reads:** Capture the current state of the trie and create immutable snapshots, allowing for point-in-time views of the data.
