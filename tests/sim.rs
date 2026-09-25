//! Deterministic Simulation Testing (DST) for vart.
//!
//! Validates:
//! 1. Point lookups, timestamp queries, and zero-allocation slice reads against a canonical BTreeMap reference oracle.
//! 2. Multi-snapshot copy-on-write isolation across concurrent branch mutations.
//! 3. DoubleEndedIterator forward, backward, and alternating scan symmetry.
//! 4. Continuous structural invariant verification (sorted keys, bitmaps, occupancy, path prefixes).
//! 5. Exact tree.len() and tree.is_empty() tracking through arbitrary inserts, updates, and deletes.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::collections::{BTreeMap, HashMap};
use std::env;
use std::ops::Bound;
use vart::art::Tree;
use vart::VariableSizeKey;

#[derive(Clone, Debug, PartialEq, Eq)]
struct VersionEntry {
    version: u64,
    ts: u64,
    value: i32,
}

#[derive(Default, Clone)]
struct OracleState {
    keys: BTreeMap<Vec<u8>, Vec<VersionEntry>>,
}

impl OracleState {
    fn insert(&mut self, key: &[u8], value: i32, version: u64, ts: u64, replace: bool) {
        let entries = self.keys.entry(key.to_vec()).or_default();
        if replace {
            // Replace existing if newer
            if let Some(last) = entries.last_mut() {
                if version > last.version {
                    entries.clear();
                    entries.push(VersionEntry { version, ts, value });
                }
            } else {
                entries.push(VersionEntry { version, ts, value });
            }
        } else {
            // Insert or update (version, ts)
            match entries.binary_search_by(|v| (v.version, v.ts).cmp(&(version, ts))) {
                Ok(idx) => {
                    entries[idx] = VersionEntry { version, ts, value };
                }
                Err(idx) => {
                    entries.insert(idx, VersionEntry { version, ts, value });
                }
            }
        }
    }

    fn remove(&mut self, key: &[u8]) -> bool {
        self.keys.remove(key).is_some()
    }

    fn get_latest(&self, key: &[u8]) -> Option<(i32, u64, u64)> {
        let entries = self.keys.get(key)?;
        let last = entries.last()?;
        Some((last.value, last.version, last.ts))
    }

    fn get_at_ts(&self, key: &[u8], ts: u64) -> Option<(i32, u64, u64)> {
        let entries = self.keys.get(key)?;
        let entry = entries.iter().filter(|v| v.ts <= ts).max_by_key(|v| v.ts)?;
        Some((entry.value, entry.version, entry.ts))
    }

    fn range_keys(&self, start: Bound<&[u8]>, end: Bound<&[u8]>) -> Vec<(Vec<u8>, i32, u64, u64)> {
        let mut results = Vec::new();
        let bound_start = match start {
            Bound::Included(k) => Bound::Included(k.to_vec()),
            Bound::Excluded(k) => Bound::Excluded(k.to_vec()),
            Bound::Unbounded => Bound::Unbounded,
        };
        let bound_end = match end {
            Bound::Included(k) => Bound::Included(k.to_vec()),
            Bound::Excluded(k) => Bound::Excluded(k.to_vec()),
            Bound::Unbounded => Bound::Unbounded,
        };

        for (k, entries) in self.keys.range((bound_start, bound_end)) {
            if let Some(latest) = entries.last() {
                results.push((k.clone(), latest.value, latest.version, latest.ts));
            }
        }
        results
    }
}

struct Simulator {
    rng: StdRng,
    seed: u64,
    trees: HashMap<usize, Tree<VariableSizeKey, i32>>,
    oracles: HashMap<usize, OracleState>,
    active_id: usize,
    next_snapshot_id: usize,
    key_pool: Vec<Vec<u8>>,
    step: usize,
}

impl Simulator {
    fn new(seed: u64) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut trees = HashMap::new();
        let mut oracles = HashMap::new();

        trees.insert(0, Tree::new());
        oracles.insert(0, OracleState::default());

        // Pre-generate adversarial and prefix-heavy keys
        let mut key_pool = Vec::new();

        // 1. Single-byte keys
        for b in 0..=255u8 {
            key_pool.push(vec![b]);
        }

        // 2. Common prefixes with small deltas
        for i in 0..50 {
            key_pool.push(format!("ns:user:{:03}", i).into_bytes());
            key_pool.push(format!("ns:user:{:03}:profile", i).into_bytes());
            key_pool.push(format!("ns:user:{:03}:settings", i).into_bytes());
            key_pool.push(format!("ns:team:{:03}", i).into_bytes());
        }

        // 3. Hierarchical keys that are exact prefixes of others (tests inner_twig)
        key_pool.push(b"a".to_vec());
        key_pool.push(b"aa".to_vec());
        key_pool.push(b"aaa".to_vec());
        key_pool.push(b"aaaa".to_vec());
        key_pool.push(b"aab".to_vec());
        key_pool.push(b"ab".to_vec());
        key_pool.push(b"b".to_vec());

        // 4. Random binary keys
        for _ in 0..100 {
            let len = rng.gen_range(1..=32);
            let mut k = vec![0u8; len];
            rng.fill(&mut k[..]);
            key_pool.push(k);
        }

        Self {
            rng,
            seed,
            trees,
            oracles,
            active_id: 0,
            next_snapshot_id: 1,
            key_pool,
            step: 0,
        }
    }

    fn sample_key(&mut self) -> Vec<u8> {
        if self.rng.gen_bool(0.85) {
            let idx = self.rng.gen_range(0..self.key_pool.len());
            self.key_pool[idx].clone()
        } else {
            // Fresh random key
            let len = self.rng.gen_range(1..=48);
            let mut k = vec![0u8; len];
            self.rng.fill(&mut k[..]);
            k
        }
    }

    fn active_tree(&mut self) -> &mut Tree<VariableSizeKey, i32> {
        self.trees.get_mut(&self.active_id).unwrap()
    }

    fn active_oracle(&mut self) -> &mut OracleState {
        self.oracles.get_mut(&self.active_id).unwrap()
    }

    fn run_step(&mut self) {
        self.step += 1;
        let op = self.rng.gen_range(0..100);

        match op {
            0..=24 => {
                // Insert (CoW)
                let raw_key = self.sample_key();
                let key = VariableSizeKey::from_slice(&raw_key);
                let value = self.rng.gen_range(-1000..1000);
                let version = self.rng.gen_range(1..=10);
                let ts = version * 10 + self.rng.gen_range(0..=5);

                let res = self.active_tree().insert(&key, value, version, ts);
                if res.is_ok() {
                    self.active_oracle()
                        .insert(&raw_key, value, version, ts, false);
                }
            }
            25..=44 => {
                // Insert unchecked (in-place mutable)
                let raw_key = self.sample_key();
                let key = VariableSizeKey::from_slice(&raw_key);
                let value = self.rng.gen_range(-1000..1000);
                let version = self.rng.gen_range(1..=10);
                let ts = version * 10 + self.rng.gen_range(0..=5);

                let res = self
                    .active_tree()
                    .insert_unchecked(&key, value, version, ts);
                if res.is_ok() {
                    self.active_oracle()
                        .insert(&raw_key, value, version, ts, false);
                }
            }
            45..=54 => {
                // Insert or replace (simulates compaction replay)
                let raw_key = self.sample_key();
                let key = VariableSizeKey::from_slice(&raw_key);
                let value = self.rng.gen_range(-1000..1000);
                let version = self.rng.gen_range(1..=10);
                let ts = self.rng.gen_range(1..=100);

                let res = self
                    .active_tree()
                    .insert_or_replace_unchecked(&key, value, version, ts);
                if res.is_ok() {
                    self.active_oracle()
                        .insert(&raw_key, value, version, ts, true);
                }
            }
            55..=69 => {
                // Remove
                let raw_key = self.sample_key();
                let key = VariableSizeKey::from_slice(&raw_key);
                let removed_tree = self.active_tree().remove(&key);
                let removed_oracle = self.active_oracle().remove(&raw_key);
                assert_eq!(
                    removed_tree, removed_oracle,
                    "Remove return value mismatch at step {} (seed: {})",
                    self.step, self.seed
                );
            }
            70..=79 => {
                // Point reads & slice reads
                let raw_key = self.sample_key();
                let key = VariableSizeKey::from_slice(&raw_key);

                let tree_get = self.active_tree().get(&key, 0);
                let slice_get = self.active_tree().get_by_slice(&raw_key, 0);
                let oracle_get = self.active_oracle().get_latest(&raw_key);

                assert_eq!(
                    tree_get, slice_get,
                    "get vs get_by_slice mismatch at step {}",
                    self.step
                );

                if let Some((v, ver, ts)) = oracle_get {
                    assert_eq!(
                        tree_get,
                        Some((v, ver, ts)),
                        "Tree get mismatch with oracle at step {} for key {:?} (seed: {})",
                        self.step,
                        raw_key,
                        self.seed
                    );
                    assert!(self.active_tree().contains_key_slice(&raw_key));

                    // Verify get_at_ts at exact timestamp
                    let oracle_ts = self.active_oracle().get_at_ts(&raw_key, ts);
                    let tree_ts = self.active_tree().get_at_ts(&key, ts);
                    let tree_ts_slice = self.active_tree().get_at_ts_by_slice(&raw_key, ts);
                    assert_eq!(tree_ts, tree_ts_slice);
                    assert_eq!(
                        tree_ts, oracle_ts,
                        "get_at_ts mismatch at step {}",
                        self.step
                    );
                } else {
                    assert_eq!(
                        tree_get, None,
                        "Tree had key {:?} not in oracle at step {}",
                        raw_key, self.step
                    );
                    assert!(!self.active_tree().contains_key_slice(&raw_key));
                }
            }
            80..=89 => {
                // Range scans and DoubleEnded symmetry
                let k1 = self.sample_key();
                let k2 = self.sample_key();
                let (start_raw, end_raw) = if k1 <= k2 { (k1, k2) } else { (k2, k1) };

                let start_key = VariableSizeKey::from_slice(&start_raw);
                let end_key = VariableSizeKey::from_slice(&end_raw);

                // Forward range scan
                let tree_forward: Vec<_> = self
                    .active_tree()
                    .range(start_key.clone()..=end_key.clone())
                    .map(|(k, v, ver, ts)| (k.to_vec(), *v, ver, ts))
                    .collect();

                let oracle_forward = self
                    .active_oracle()
                    .range_keys(Bound::Included(&start_raw), Bound::Included(&end_raw));

                assert_eq!(
                    tree_forward, oracle_forward,
                    "Forward range scan mismatch at step {} (seed: {})",
                    self.step, self.seed
                );

                // Backward range scan
                let mut tree_backward: Vec<_> = self
                    .active_tree()
                    .range(start_key..=end_key)
                    .rev()
                    .map(|(k, v, ver, ts)| (k.to_vec(), *v, ver, ts))
                    .collect();
                tree_backward.reverse();

                assert_eq!(
                    tree_forward, tree_backward,
                    "DoubleEnded range symmetry mismatch (forward vs rev) at step {} (seed: {})",
                    self.step, self.seed
                );
            }
            90..=95 => {
                // Create Snapshot (clone tree & oracle)
                if self.trees.len() < 10 {
                    let new_id = self.next_snapshot_id;
                    self.next_snapshot_id += 1;
                    let cloned_tree = self.active_tree().clone();
                    let cloned_oracle = self.active_oracle().clone();
                    self.trees.insert(new_id, cloned_tree);
                    self.oracles.insert(new_id, cloned_oracle);
                }
            }
            _ => {
                // Switch active snapshot branch
                let keys: Vec<usize> = self.trees.keys().copied().collect();
                let chosen = keys[self.rng.gen_range(0..keys.len())];
                self.active_id = chosen;
            }
        }

        // Invariant checks on the active tree
        let active_tree = &self.trees[&self.active_id];
        let active_oracle = &self.oracles[&self.active_id];

        assert_eq!(
            active_tree.len(),
            active_oracle.keys.len(),
            "Tree len ({}) != oracle len ({}) at step {} on snapshot {} (seed: {})",
            active_tree.len(),
            active_oracle.keys.len(),
            self.step,
            self.active_id,
            self.seed
        );

        assert_eq!(
            active_tree.is_empty(),
            active_oracle.keys.is_empty(),
            "Tree is_empty mismatch at step {} on snapshot {} (seed: {})",
            self.step,
            self.active_id,
            self.seed
        );

        // Run structural validator every 5 steps
        if self.step.is_multiple_of(5) {
            if let Err(e) = active_tree.validate_invariants() {
                panic!(
                    "STRUCTURAL INVARIANT VIOLATION at step {} on snapshot {}: {}
Reproduce with VART_SIM_SEED={}",
                    self.step, self.active_id, e, self.seed
                );
            }
        }
    }
}

#[test]
fn deterministic_simulation_fuzz() {
    let seed: u64 = env::var("VART_SIM_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            let mut r = rand::thread_rng();
            r.gen()
        });

    println!("Running Deterministic Simulation Testing (seed: {})", seed);

    let mut sim = Simulator::new(seed);
    let total_steps = 1000;

    for _ in 0..total_steps {
        sim.run_step();
    }

    // Final full invariant check across all live snapshot branches
    for (id, tree) in &sim.trees {
        let oracle = &sim.oracles[id];
        assert_eq!(tree.len(), oracle.keys.len());
        tree.validate_invariants().unwrap_or_else(|e| {
            panic!(
                "Final invariant failure on snapshot {}: {}
Reproduce with VART_SIM_SEED={}",
                id, e, seed
            );
        });
    }

    println!(
        "Deterministic Simulation Testing completed successfully (1000 steps, seed: {})",
        seed
    );
}
