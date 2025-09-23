use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use utils::add_multilinears;

type F = KoalaBear;

fn generate_random_multilinear(log_size: usize, seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..1 << log_size).map(|_| rng.random()).collect()
}

fn bench_add_multilinears(c: &mut Criterion) {
    let mut group = c.benchmark_group("add_multilinears_fn");

    // Test different polynomial sizes: 2^10, 2^14, 2^18, 2^20
    let log_sizes = [10, 14, 18, 20];

    for &log_size in &log_sizes {
        let size = 1 << log_size;
        let pol1 = generate_random_multilinear(log_size, 42);
        let pol2 = generate_random_multilinear(log_size, 43);

        group.throughput(Throughput::Elements(size as u64));

        // Benchmark optimized version
        group.bench_with_input(
            BenchmarkId::new("optimized", log_size),
            &(pol1.clone(), pol2.clone()),
            |b, (p1, p2)| {
                b.iter(|| {
                    let result = add_multilinears(black_box(p1), black_box(p2));
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

fn bench_add_multilinears_sparse(c: &mut Criterion) {
    let mut group = c.benchmark_group("add_multilinears_sparse");

    let log_size = 16;
    let sparsity_levels = [0.1, 0.5, 0.9, 1.0]; // Fraction of non-zero elements

    for &sparsity in &sparsity_levels {
        let mut rng = StdRng::seed_from_u64(42);
        let size = 1 << log_size;

        let mut pol1 = vec![F::ZERO; size];
        let mut pol2 = vec![F::ZERO; size];

        // Fill with random non-zero values according to sparsity
        let non_zero_count = (size as f64 * sparsity) as usize;
        for i in 0..non_zero_count {
            pol1[i] = rng.random();
            pol2[i] = rng.random();
        }

        group.throughput(Throughput::Elements(size as u64));

        group.bench_function(
            BenchmarkId::new("optimized", (sparsity * 100.0) as u32),
            |b| {
                b.iter(|| {
                    let result = add_multilinears(black_box(&pol1), black_box(&pol2));
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_add_multilinears,
    bench_add_multilinears_sparse
);
criterion_main!(benches);
