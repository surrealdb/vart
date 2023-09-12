# tart: Timed-Adaptive Radix Trie for Rust

tart is a Rust library that implements an immutable Timed-Adaptive Radix Trie data structure. It allows you to efficiently manage key-value pairs with timestamps, making it ideal for applications that require tracking changes over time and enabling snapshot reads. With tart, you can handle versioned data, insert, delete, and query key-value items based on specific versions (or timestamps), and more.

![](https://img.shields.io/badge/license-Apache_License_2.0-00bfff.svg?style=flat-square)

## Features

- **Immutable:** Built on an immutable radix trie data structure. This means that once a key-value pair is added to tart, it cannot be modified or deleted, ensuring data integrity and enabling safe and predictable operations. Multiple versions of the same key can be stored and retrieved by using the version (or timestamp).

- **Timestamp Tracking:** Associate timestamps with key-value items, allowing for applications that need to track changes over time.

- **Snapshot Reads:** Capture the current state of the trie and create immutable snapshots, allowing for point-in-time views of the data.

- **Immutable and Copy-on-Write:** tart supports both immutable and copy-on-write operations, giving you flexibility in managing your data.

