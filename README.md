<br>

<h1 align="center">vart</h1>

<p align="center">An immutable, versioned, adaptive radix trie data structure for Rust.</p>

<br>

<p align="center">
    <a href="https://github.com/surrealdb/vart"><img src="https://img.shields.io/badge/status-stable-ff00bb.svg?style=flat-square"></a>
    &nbsp;
    <a href="https://docs.rs/vart/"><img src="https://img.shields.io/docsrs/vart?style=flat-square"></a>
    &nbsp;
    <a href="https://crates.io/crates/vart"><img src="https://img.shields.io/crates/v/vart?style=flat-square"></a>
    &nbsp;
    <a href="https://github.com/surrealdb/vart"><img src="https://img.shields.io/badge/license-Apache_License_2.0-00bfff.svg?style=flat-square"></a>
</p>

`vart` is a pure safe-Rust implementation of an immutable **Versioned Adaptive Radix Tree (ART)** data structure. It combines the space efficiency and cache locality of adaptive radix trees with copy-on-write structural sharing and multi-version timestamp history.

It is designed as an in-memory index engine for databases, storage engines, and analytical applications that require microsecond-latency point lookups, zero-allocation range scans, snapshot reads, and point-in-time historical queries.

---

## Performance

Benchmarked on bare metal (**AMD Ryzen Threadripper 9970X 32-Core / 64-Thread Processor @ 5.48 GHz, 128 GB DDR5 RAM**, Linux 6.8):

| Data Structure | Point Read (Random Hit) | Point Insert (In-Place) | Snapshot Clone | Allocations / Insert |
| :--- | ---: | ---: | ---: | ---: |
| **`vart::Tree` (Slice Lookup)** | <img width="16" align="absmiddle" src="/img/rocket.png" alt="🚀">&nbsp;**27.6 ns** (36.1M/s) | — | — | **0 allocs** |
| **`vart::Tree` (Standard Key)** | **29.2 ns** (34.1M/s) | **93.7 ns** (10.6M/s) | <img width="16" align="absmiddle" src="/img/rocket.png" alt="🚀">&nbsp;**8.12 ns** | **1.0 allocs** |
| `im::OrdMap` (Persistent B-Tree) | 38.2 ns (26.1M/s) | 52.2 ns (19.0M/s) | **7.93 ns** | ~0.06 allocs |
| `std::collections::BTreeMap` | 70.0 ns (14.2M/s) | 36.8 ns (27.0M/s) | 577.1 µs (~70,000× slower) | ~0.16 allocs |
| `std::collections::HashMap` | 14.2 ns (70.0M/s) | 28.4 ns (34.3M/s) | N/A | ~0 allocs |

- **Zero-Allocation Range Scanning**: Traverses 1,000 contiguous items in **8.19 microseconds** (~122,000,000 items/sec) with zero heap allocations during iteration via the unboxed `ChildrenIter` enum.
- **Zero-Allocation Point Lookups**: Queries directly by raw byte slice (`tree.get_by_slice` / `tree.contains_key_slice`) in **18.7 ns**, avoiding key wrapping allocations.
- **Snapshot Creation**: Instantaneous $O(1)$ snapshot creation via atomic reference counting (`tree.clone()`), enabling point-in-time isolation without cloning tree data.
- **In-Place Mutation Bypass**: High-throughput ingestion via `tree.insert_unchecked`, avoiding copy-on-write overhead when writing to uniquely owned trees while safely falling back to copy-on-write for shared snapshot paths.

---

## Features

- **100% Safe Rust**: Enforced with `#![forbid(unsafe_code)]` at the crate root.
- **Adaptive Radix Tree Architecture**: Dynamically resizes inner nodes across 4 compact layouts (`Node4` $\leftrightarrow$ `Node16` $\leftrightarrow$ `Node48` $\leftrightarrow$ `Node256`) to maximize L1/L2 cache locality and prefix compression.
- **Multi-Version Timestamp Ordering**: Supports multiple version and timestamp entries per key for point-in-time reads and transactional MVCC indexes.
- **Copy-on-Write Snapshots**: $O(1)$ tree branching; mutating a snapshot or active tree preserves complete isolation with shared subtrees safely cloned on write.
- **Zero-Allocation Slice Queries**: Look up records using raw byte slices (`&[u8]`) or string references (`&str`) without creating temporary key objects.
- **Unboxed Traversal**: Stack-allocated `ChildrenIter` eliminates double-boxing and dynamic vtable dispatch during forward and backward iteration.
- **Bidirectional Range Scans**: Full `DoubleEndedIterator` support across arbitrary ranges (`tree.range(A..B)` and `tree.range(A..B).rev()`), with lazy backward state initialization.
- **Standard Rust Collection Traits**: Implements `len()`, `is_empty()`, `fmt::Debug`, `IntoIterator`, `FromIterator`, `Deref`, `Borrow`, `AsRef`, `From`, `Default`, and `Hash`.
- **Thread Safety Guaranteed**: Compile-time static assertions ensure `Tree<P, V>`, `Node<P, V>`, and iterators implement `Send + Sync`.
- **Deterministic Simulation Tested (DST)**: Continuously validated by a seeded PRNG fuzzer against an in-memory `BTreeMap` reference oracle across millions of operations with continuous structural invariant verification.

---

## Quick Start

Add `vart` to your `Cargo.toml`:

```toml
[dependencies]
vart = "0.9"
```

```rust
use vart::art::Tree;
use vart::VariableSizeKey;

fn main() {
    let mut tree = Tree::<VariableSizeKey, String>::new();

    let user_1 = VariableSizeKey::from("users:0001");
    let user_2 = VariableSizeKey::from("users:0002");

    // Insert versioned key-value pairs (key, value, version, timestamp)
    tree.insert(&user_1, "Alice (v1)".into(), 1, 100).unwrap();
    tree.insert(&user_1, "Alice (v2)".into(), 2, 200).unwrap();
    tree.insert(&user_2, "Bob".into(), 1, 150).unwrap();

    assert_eq!(tree.len(), 2);

    // Point lookup (latest version)
    let (val, version, ts) = tree.get(&user_1, 0).unwrap();
    assert_eq!(val, "Alice (v2)");
    assert_eq!(version, 2);

    // Zero-allocation point lookup via raw byte slice
    assert!(tree.contains_key_slice(b"users:0001"));
    let (val, _, _) = tree.get_by_slice(b"users:0001", 0).unwrap();
    assert_eq!(val, "Alice (v2)");

    // Point-in-time read at historical timestamp
    let (historical_val, _, _) = tree.get_at_ts(&user_1, 150).unwrap();
    assert_eq!(historical_val, "Alice (v1)");

    // Create a copy-on-write snapshot (O(1))
    let snapshot = tree.clone();

    // Mutate the active tree
    let user_3 = VariableSizeKey::from("users:0003");
    tree.insert(&user_3, "Charlie".into(), 1, 300).unwrap();

    // Verify snapshot isolation
    assert!(tree.contains_key_slice(b"users:0003"));
    assert!(!snapshot.contains_key_slice(b"users:0003"));

    // Range scanning
    let start = VariableSizeKey::from("users:0001");
    let end = VariableSizeKey::from("users:0004");
    for (key_bytes, val, ver, ts) in tree.range(&start..&end) {
        println!("{:?} = {} (v{}, ts{})", std::str::from_utf8(key_bytes).unwrap(), val, ver, ts);
    }
}
```

---

## Core Operations

### Zero-Allocation Slice Lookups

Avoid allocating key wrapper structs when querying the tree:

```rust
use vart::art::Tree;
use vart::VariableSizeKey;

let mut tree = Tree::<VariableSizeKey, i32>::new();
let key = VariableSizeKey::from("tenant:100:profile");
tree.insert(&key, 42, 1, 100).unwrap();

// Zero-allocation check and retrieval using raw bytes
if tree.contains_key_slice(b"tenant:100:profile") {
    let (val, version, ts) = tree.get_by_slice(b"tenant:100:profile", 0).unwrap();
    assert_eq!(val, 42);
}
```

### Snapshot Isolation & Concurrent Branches

Creating a snapshot is an $O(1)$ reference copy. Shared subtrees are lazily cloned on write:

```rust
let mut tree = Tree::<VariableSizeKey, String>::new();
let k1 = VariableSizeKey::from("k1");
tree.insert(&k1, "initial".into(), 1, 10).unwrap();

// Create snapshot
let mut snapshot = tree.clone();

// Mutating one branch does not affect the other
tree.insert(&k1, "updated in main".into(), 2, 20).unwrap();
snapshot.insert(&k1, "updated in snap".into(), 2, 30).unwrap();

assert_eq!(tree.get(&k1, 0).unwrap().0, "updated in main");
assert_eq!(snapshot.get(&k1, 0).unwrap().0, "updated in snap");
```

### Bidirectional Range Scanning

Iterators implement `DoubleEndedIterator` with zero heap allocation during traversal:

```rust
let start = VariableSizeKey::from("prefix:001");
let end = VariableSizeKey::from("prefix:100");

// Forward iteration
for (k, v, _, _) in tree.range(&start..&end) {
    // ...
}

// Reverse iteration
for (k, v, _, _) in tree.range(&start..&end).rev() {
    // ...
}
```

### Key Types

`vart` provides two built-in key abstractions:

1. **`VariableSizeKey`**: General-purpose variable-length byte key backed by `Vec<u8>`. Implements `From<Vec<u8>>`, `From<String>`, `From<&str>`, `Deref<Target = [u8]>`, `Borrow<[u8]>`, and `Hash`.
2. **`FixedSizeKey<const SIZE: usize>`**: Inline array-backed key (`[u8; SIZE]`) for fixed-size keys (e.g. 64-bit/128-bit integers, UUIDs, or hashes) eliminating heap allocations for key storage.

---

## Deterministic Simulation Testing (DST)

`vart` includes a deterministic simulation testing harness in `tests/sim.rs` inspired by FoundationDB and TigerBeetle:

- **Seeded PRNG**: Every simulation run is parameterized by a 64-bit seed (`VART_SIM_SEED=<seed>`) to reproduce failures down to the byte.
- **Reference Oracle**: Runs state transitions in lockstep against a canonical `BTreeMap` reference oracle.
- **Continuous Invariant Checking**: Validates prefix compression, node capacity boundaries, child bitmaps, and version monotonicity after every simulated step via `tree.validate_invariants()`.

To run the simulation suite:

```bash
# Run with a random seed
cargo test --test sim -- --nocapture

# Run with an exact reproducible seed
VART_SIM_SEED=20202 cargo test --test sim -- --nocapture
```

---

## Benchmarks

Benchmarks can be run locally or executed on a dedicated bare-metal server using the included remote runner:

```bash
# Run comparison benchmarks locally
cargo bench --bench comparison_bench

# Run allocation and memory benchmarks locally
cargo bench --bench alloc_comparison

# Run on remote dedicated hardware (AMD Threadripper)
./scripts/bench-remote.sh --all
```

---

## License

This project is licensed under the [Apache License, Version 2.0](LICENSE).
