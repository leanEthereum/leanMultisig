use std::{hint::black_box, time::Duration};

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use whir_p3::whir::config::{FoldingFactor, SecurityAssumption};
use whirlaway::examples::prove_poseidon2::{Poseidon2Config, prove_poseidon2};

fn bench_poseidon2(c: &mut Criterion) {
    const L16: usize = 17;
    const L24: usize = 17;

    let mut group = c.benchmark_group("poseidon2");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(60));
    group.warm_up_time(Duration::from_secs(10));
    group.throughput(Throughput::Elements((1u64 << L16) + (1u64 << L24)));

    let config = Poseidon2Config {
        log_n_poseidons_16: L16,
        log_n_poseidons_24: L24,
        univariate_skips: 4,
        folding_factor: FoldingFactor::new(7, 4),
        log_inv_rate: 1,
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        security_level: 128,
        rs_domain_initial_reduction_factor: 5,
        max_num_variables_to_send_coeffs: 3,
        display_logs: false,
    };

    group.bench_function("poseidon2", |b| {
        b.iter(|| {
            let result = prove_poseidon2(black_box(&config));
            black_box(result.prover_time);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_poseidon2);
criterion_main!(benches);
