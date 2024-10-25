use art::{trie::mutable::art::Tree, VecArray};
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::mem;
use art::{ArrayPrefix, VectorKey};

fn bench_vec_array_push(c: &mut Criterion) {
    let mut vec_array: VecArray<u64, 1000> = VecArray::new();
    c.bench_function("vec_array_push", |b| {
        b.iter(|| {
            for i in 0..1000 {
                vec_array.set(i, i as u64);
            }
        })
    });

    let memory_usage = mem::size_of_val(&vec_array);
    println!("vec_array_memory: {}", memory_usage);
}

fn bench_vec_array_get(c: &mut Criterion) {
    let mut vec_array: VecArray<u32, 1000> = VecArray::new();
    for i in 0..1000 {
        vec_array.push(i);
    }
    c.bench_function("vec_array_get", |b| {
        b.iter(|| {
            for i in 0..1000 {
                black_box(vec_array.get(i));
            }
        })
    });
}

fn generate_data(
    num_keys: usize,
    key_size: usize,
    value_size: usize,
) -> Vec<(VectorKey, Vec<u32>)> {
    let mut data = Vec::with_capacity(num_keys);

    for i in 0..num_keys {
        // Generate key
        let mut key = vec![0xFF; key_size];
        key[0..8.min(key_size)].copy_from_slice(&i.to_le_bytes()[0..8.min(key_size)]);

        // Generate value
        let value = vec![0x42; value_size];

        data.push((VectorKey::from_slice(&key), value));
    }

    data
}

fn variable_size_bulk_insert_mut(c: &mut Criterion) {
    let mut group = c.benchmark_group("vart_insert");

    // Test different combinations of key sizes, value sizes, and number of keys
    // let key_sizes = vec![16, 32, 64, 128];
    let key_sizes = vec![32];

    // let num_keys_list = vec![100_000, 500_000, 1_000_000];
    // let num_keys_list = vec![100, 1000];
    let num_keys_list = vec![1000];

    for &num_keys in &num_keys_list {
        for &key_size in &key_sizes {
            let benchmark_id = BenchmarkId::new(format!("k{}_v{}", key_size, key_size), num_keys);

            group.bench_with_input(benchmark_id, &num_keys, |b, &num_keys| {
                // Generate test data outside the benchmark loop
                let data = generate_data(num_keys, key_size, key_size);

                b.iter(|| {
                    let mut tree = Tree::<ArrayPrefix<32>, Vec<u32>>::new();
                    for (key, value) in data.iter() {
                        tree.insert(key, value.to_vec());
                    }
                    black_box(tree)
                });
            });
        }
    }

    group.finish();
}


criterion_group!(benches, variable_size_bulk_insert_mut);
criterion_main!(benches);
