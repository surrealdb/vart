use rand::Rng;

use vart::art::Tree;
use vart::VariableSizeKey;

#[global_allocator]
static ALLOC: divan::AllocProfiler = divan::AllocProfiler::system();

fn main() {
    divan::main();
}

const COUNTS: &[usize] = &[10_000, 100_000, 1_000_000];

#[divan::bench(
    args = COUNTS,
)]
pub fn seq_insert(b: divan::Bencher<'_, '_>, count: usize) {
    let mut tree = Tree::<VariableSizeKey, _>::new();
    let mut rng = rand::thread_rng();

    b.counter(count).bench_local(|| {
        let key: [u8; 20] = rng.gen();
        let key = VariableSizeKey::from_slice(&key);
        let _ = tree.insert(&key, 1, 0, 0);
    });
}
