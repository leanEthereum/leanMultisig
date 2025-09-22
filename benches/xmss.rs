use std::{hint::black_box, time::Duration};

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use rec_aggregation::bench_xmss;

fn bench_xmss_benchmark(c: &mut Criterion) {
    const N: usize = 500;
    const LOG_LIFETIME: usize = 32;

    let mut group = c.benchmark_group("xmss");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(60));
    group.warm_up_time(Duration::from_secs(10));
    group.throughput(Throughput::Elements(N as u64));

    group.bench_function("xmss", |b| {
        b.iter(|| {
            let duration = bench_xmss(N, LOG_LIFETIME);
            black_box(duration);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_xmss_benchmark);
criterion_main!(benches);
