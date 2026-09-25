use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::collections::{BTreeMap, HashMap};
use vart::art::Tree;
use vart::FixedSizeKey;

const SAMPLE_SIZE: usize = 100_000;

fn seeded_rng(seed: u64) -> StdRng {
    StdRng::seed_from_u64(seed)
}

fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    group.throughput(Throughput::Elements(1));

    // VART in-place (insert_unchecked)
    group.bench_function("vart_inplace", |b| {
        let mut tree = Tree::<FixedSizeKey<16>, u64>::new();
        let mut key = 0u64;
        b.iter(|| {
            let k: FixedSizeKey<16> = key.into();
            let _ = tree.insert_unchecked(&k, key, 0, 0);
            key += 1;
        })
    });

    // VART CoW (insert)
    group.bench_function("vart_cow", |b| {
        let mut tree = Tree::<FixedSizeKey<16>, u64>::new();
        let mut key = 0u64;
        b.iter(|| {
            let k: FixedSizeKey<16> = key.into();
            let _ = tree.insert(&k, key, 0, 0);
            key += 1;
        })
    });

    // BTreeMap
    group.bench_function("btreemap", |b| {
        let mut btree = BTreeMap::new();
        let mut key = 0u64;
        b.iter(|| {
            btree.insert(key, key);
            key += 1;
        })
    });

    // HashMap
    group.bench_function("hashmap", |b| {
        let mut hmap = HashMap::new();
        let mut key = 0u64;
        b.iter(|| {
            hmap.insert(key, key);
            key += 1;
        })
    });

    // im::OrdMap
    group.bench_function("im_ordmap", |b| {
        let mut im_map = im::OrdMap::new();
        let mut key = 0u64;
        b.iter(|| {
            im_map.insert(key, key);
            key += 1;
        })
    });

    // imbl::OrdMap
    group.bench_function("imbl_ordmap", |b| {
        let mut imbl_map = imbl::OrdMap::new();
        let mut key = 0u64;
        b.iter(|| {
            imbl_map.insert(key, key);
            key += 1;
        })
    });

    group.finish();
}

fn bench_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_get");
    group.throughput(Throughput::Elements(1));

    let mut vart_tree = Tree::<FixedSizeKey<16>, u64>::new();
    let mut btree = BTreeMap::new();
    let mut hmap = HashMap::new();
    let mut im_map = im::OrdMap::new();
    let mut imbl_map = imbl::OrdMap::new();

    for i in 0..SAMPLE_SIZE as u64 {
        let k: FixedSizeKey<16> = i.into();
        let _ = vart_tree.insert_unchecked(&k, i, 0, 0);
        btree.insert(i, i);
        hmap.insert(i, i);
        im_map.insert(i, i);
        imbl_map.insert(i, i);
    }

    group.bench_function("vart", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let key = rng.gen_range(0..SAMPLE_SIZE as u64);
            let k: FixedSizeKey<16> = key.into();
            black_box(vart_tree.get(&k, 0))
        })
    });

    group.bench_function("vart_slice", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let key = rng.gen_range(0..SAMPLE_SIZE as u64);
            let bytes = key.to_be_bytes();
            black_box(vart_tree.get_by_slice(&bytes, 0))
        })
    });

    group.bench_function("btreemap", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let key = rng.gen_range(0..SAMPLE_SIZE as u64);
            black_box(btree.get(&key))
        })
    });

    group.bench_function("hashmap", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let key = rng.gen_range(0..SAMPLE_SIZE as u64);
            black_box(hmap.get(&key))
        })
    });

    group.bench_function("im_ordmap", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let key = rng.gen_range(0..SAMPLE_SIZE as u64);
            black_box(im_map.get(&key))
        })
    });

    group.bench_function("imbl_ordmap", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let key = rng.gen_range(0..SAMPLE_SIZE as u64);
            black_box(imbl_map.get(&key))
        })
    });

    group.finish();
}

fn bench_scan(c: &mut Criterion) {
    let mut group = c.benchmark_group("range_scan_100");
    group.throughput(Throughput::Elements(100));

    let mut vart_tree = Tree::<FixedSizeKey<16>, u64>::new();
    let mut btree = BTreeMap::new();
    let mut im_map = im::OrdMap::new();
    let mut imbl_map = imbl::OrdMap::new();

    for i in 0..SAMPLE_SIZE as u64 {
        let k: FixedSizeKey<16> = i.into();
        let _ = vart_tree.insert_unchecked(&k, i, 0, 0);
        btree.insert(i, i);
        im_map.insert(i, i);
        imbl_map.insert(i, i);
    }

    group.bench_function("vart", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let start = rng.gen_range(0..(SAMPLE_SIZE - 200) as u64);
            let start_k: FixedSizeKey<16> = start.into();
            let end_k: FixedSizeKey<16> = (start + 100).into();
            let count = vart_tree.range(&start_k..&end_k).count();
            black_box(count)
        })
    });

    group.bench_function("btreemap", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let start = rng.gen_range(0..(SAMPLE_SIZE - 200) as u64);
            let count = btree.range(start..start + 100).count();
            black_box(count)
        })
    });

    group.bench_function("im_ordmap", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let start = rng.gen_range(0..(SAMPLE_SIZE - 200) as u64);
            let count = im_map.range(start..start + 100).count();
            black_box(count)
        })
    });

    group.bench_function("imbl_ordmap", |b| {
        let mut rng = seeded_rng(0x12345678);
        b.iter(|| {
            let start = rng.gen_range(0..(SAMPLE_SIZE - 200) as u64);
            let count = imbl_map.range(start..start + 100).count();
            black_box(count)
        })
    });

    group.finish();
}

fn bench_snapshot(c: &mut Criterion) {
    let mut group = c.benchmark_group("snapshot_clone");
    group.throughput(Throughput::Elements(1));

    let mut vart_tree = Tree::<FixedSizeKey<16>, u64>::new();
    let mut btree = BTreeMap::new();
    let mut im_map = im::OrdMap::new();
    let mut imbl_map = imbl::OrdMap::new();

    for i in 0..SAMPLE_SIZE as u64 {
        let k: FixedSizeKey<16> = i.into();
        let _ = vart_tree.insert_unchecked(&k, i, 0, 0);
        btree.insert(i, i);
        im_map.insert(i, i);
        imbl_map.insert(i, i);
    }

    group.bench_function("vart", |b| b.iter(|| black_box(vart_tree.clone())));

    group.bench_function("btreemap", |b| b.iter(|| black_box(btree.clone())));

    group.bench_function("im_ordmap", |b| b.iter(|| black_box(im_map.clone())));

    group.bench_function("imbl_ordmap", |b| b.iter(|| black_box(imbl_map.clone())));

    group.finish();
}

criterion_group!(benches, bench_insert, bench_get, bench_scan, bench_snapshot);
criterion_main!(benches);
