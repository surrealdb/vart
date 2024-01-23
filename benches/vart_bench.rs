use std::time::Instant;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::prelude::SliceRandom;
use rand::SeedableRng;
use rand::{rngs::StdRng, Rng};

use vart::art::Tree;
use vart::FixedSizeKey;

fn seeded_rng(alter: u64) -> impl Rng {
    StdRng::seed_from_u64(0xEA3C47920F94A980 ^ alter)
}

pub fn seq_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("seq_insert");
    group.throughput(Throughput::Elements(1));
    group.bench_function("seq_insert", |b| {
        let mut tree = Tree::<FixedSizeKey<16>, _>::new();
        let mut key = 0u64;
        b.iter(|| {
            let _ = tree.insert(&key.into(), key, 0, 0);
            key += 1;
        })
    });

    group.finish();
}

pub fn rand_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("rand_insert");
    group.throughput(Throughput::Elements(1));

    let keys = gen_keys(3, 2, 3);

    group.bench_function("art", |b| {
        let mut tree = Tree::<FixedSizeKey<16>, _>::new();
        let mut rng = seeded_rng(0xE080D1A42C207DAF);
        b.iter(|| {
            let key = &keys[rng.gen_range(0..keys.len())];
            let _ = tree.insert(&key.into(), key.clone(), 0, 0);
        })
    });

    group.finish();
}

pub fn seq_delete(c: &mut Criterion) {
    let mut group = c.benchmark_group("seq_delete");
    group.throughput(Throughput::Elements(1));
    group.bench_function("art", |b| {
        let mut tree = Tree::<FixedSizeKey<16>, _>::new();
        b.iter_custom(|iters| {
            for i in 0..iters {
                let _ = tree.insert(&i.into(), i, 0, 0);
            }
            let start = Instant::now();
            for i in 0..iters {
                let _ = tree.remove(&i.into());
            }
            start.elapsed()
        })
    });

    group.finish();
}

pub fn rand_delete(c: &mut Criterion) {
    let mut group = c.benchmark_group("rand_delete");
    let keys = gen_keys(3, 2, 3);

    group.throughput(Throughput::Elements(1));
    group.bench_function("art", |b| {
        let mut tree = Tree::<FixedSizeKey<16>, _>::new();
        let mut rng = seeded_rng(0xE080D1A42C207DAF);
        for key in &keys {
            let _ = tree.insert(&key.into(), key, 0, 0);
        }
        b.iter(|| {
            let key = &keys[rng.gen_range(0..keys.len())];
            let _ = criterion::black_box(tree.remove(&key.into()));
        })
    });

    group.finish();
}

pub fn rand_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_get");

    group.throughput(Throughput::Elements(1));
    {
        let size = 1_000_000;
        let mut tree = Tree::<FixedSizeKey<16>, _>::new();
        for i in 0..size {
            tree.insert(&i.into(), i, 0, 0).unwrap();
        }
        group.bench_with_input(BenchmarkId::new("art", size), &size, |b, size| {
            let mut rng = seeded_rng(0xE080D1A42C207DAF);
            b.iter(|| {
                let key: u64 = rng.gen_range(0..*size);
                let _ = criterion::black_box(tree.get(&key.into(), 0));
            })
        });
    }

    group.finish();
}

pub fn rand_get_str(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_get_str");
    let keys = gen_keys(3, 2, 3);

    {
        let size = 1_000_000;
        let mut tree = Tree::<FixedSizeKey<16>, _>::new();
        for (i, key) in keys.iter().enumerate() {
            tree.insert(&key.into(), i, 0, 0).unwrap();
        }
        group.bench_with_input(BenchmarkId::new("art", size), &size, |b, _size| {
            let mut rng = seeded_rng(0xE080D1A42C207DAF);
            b.iter(|| {
                let key = &keys[rng.gen_range(0..keys.len())];
                let _ = criterion::black_box(tree.get(&key.into(), 0));
            })
        });
    }

    group.finish();
}

pub fn seq_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("seq_get");

    group.throughput(Throughput::Elements(1));
    {
        let size = 1_000_000;
        let mut tree = Tree::<FixedSizeKey<16>, _>::new();
        for i in 0..size as u64 {
            tree.insert(&i.into(), i, 0, 0).unwrap();
        }
        group.bench_with_input(BenchmarkId::new("art", size), &size, |b, _size| {
            let mut key = 0u64;
            b.iter(|| {
                let _ = criterion::black_box(tree.get(&key.into(), 0));
                key += 1;
            })
        });
    }

    group.finish();
}

fn gen_keys(l1_prefix: usize, l2_prefix: usize, suffix: usize) -> Vec<String> {
    let mut keys = Vec::new();
    let chars: Vec<char> = ('a'..='z').collect();
    let mut rng = seeded_rng(0x740A11E72FDC215D);
    for i in 0..chars.len() {
        let level1_prefix = chars[i].to_string().repeat(l1_prefix);
        for i in 0..chars.len() {
            let level2_prefix = chars[i].to_string().repeat(l2_prefix);
            let key_prefix = level1_prefix.clone() + &level2_prefix;
            for _ in 0..=u8::MAX {
                let suffix: String = (0..suffix)
                    .map(|_| chars[rng.gen_range(0..chars.len())])
                    .collect();
                let k = key_prefix.clone() + &suffix;
                keys.push(k);
            }
        }
    }

    keys.shuffle(&mut rng);
    keys
}

criterion_group!(delete_benches, seq_delete, rand_delete);
criterion_group!(insert_benches, seq_insert, rand_insert);
criterion_group!(read_benches, seq_get, rand_get, rand_get_str);
criterion_main!(insert_benches, read_benches);
