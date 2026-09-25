use std::collections::{BTreeMap, HashMap};
use vart::art::Tree;
use vart::FixedSizeKey;

#[global_allocator]
static ALLOC: divan::AllocProfiler = divan::AllocProfiler::system();

fn main() {
    divan::main();
}

const COUNTS: &[usize] = &[100_000];

#[divan::bench(args = COUNTS)]
fn alloc_vart_insert_inplace(bencher: divan::Bencher<'_, '_>, count: usize) {
    let mut tree = Tree::<FixedSizeKey<16>, usize>::new();
    let mut key = 0usize;

    bencher.counter(count).bench_local(|| {
        let k: FixedSizeKey<16> = (key as u64).into();
        let _ = tree.insert_unchecked(&k, key, 0, 0);
        key += 1;
    });
}

#[divan::bench(args = COUNTS)]
fn alloc_vart_insert_cow(bencher: divan::Bencher<'_, '_>, count: usize) {
    let mut tree = Tree::<FixedSizeKey<16>, usize>::new();
    let mut key = 0usize;

    bencher.counter(count).bench_local(|| {
        let k: FixedSizeKey<16> = (key as u64).into();
        let _ = tree.insert(&k, key, 0, 0);
        key += 1;
    });
}

#[divan::bench(args = COUNTS)]
fn alloc_btreemap_insert(bencher: divan::Bencher<'_, '_>, count: usize) {
    let mut map = BTreeMap::new();
    let mut key = 0usize;

    bencher.counter(count).bench_local(|| {
        map.insert(key, key);
        key += 1;
    });
}

#[divan::bench(args = COUNTS)]
fn alloc_hashmap_insert(bencher: divan::Bencher<'_, '_>, count: usize) {
    let mut map = HashMap::new();
    let mut key = 0usize;

    bencher.counter(count).bench_local(|| {
        map.insert(key, key);
        key += 1;
    });
}

#[divan::bench(args = COUNTS)]
fn alloc_im_ordmap_insert(bencher: divan::Bencher<'_, '_>, count: usize) {
    let mut map = im::OrdMap::new();
    let mut key = 0usize;

    bencher.counter(count).bench_local(|| {
        map.insert(key, key);
        key += 1;
    });
}

#[divan::bench(args = COUNTS)]
fn alloc_imbl_ordmap_insert(bencher: divan::Bencher<'_, '_>, count: usize) {
    let mut map = imbl::OrdMap::new();
    let mut key = 0usize;

    bencher.counter(count).bench_local(|| {
        map.insert(key, key);
        key += 1;
    });
}

#[divan::bench]
fn alloc_vart_range_scan_zero_alloc(bencher: divan::Bencher<'_, '_>) {
    let mut tree = Tree::<FixedSizeKey<16>, usize>::new();
    for i in 0..10_000usize {
        let k: FixedSizeKey<16> = (i as u64).into();
        let _ = tree.insert_unchecked(&k, i, 0, 0);
    }

    let start: FixedSizeKey<16> = 1000u64.into();
    let end: FixedSizeKey<16> = 2000u64.into();

    bencher
        .counter(1000usize)
        .bench_local(|| divan::black_box(tree.range(&start..&end).count()));
}
