use std::{hint::black_box, time::Duration};

use criterion::{Criterion, criterion_group, criterion_main};
use rec_aggregation::bench_recursion;

fn bench_recursion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("recursion");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(60));
    group.warm_up_time(Duration::from_secs(10));

    group.bench_function("recursion", |b| {
        b.iter(|| {
            let duration = bench_recursion();
            black_box(duration);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_recursion_benchmark);
criterion_main!(benches);
