use std::hint::black_box;
use std::time::Instant;

use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;

use crate::{Goldilocks, default_goldilocks_poseidon1_8};

type FPacking = <Goldilocks as Field>::Packing;
const PACKING_WIDTH: usize = <FPacking as PackedValue>::WIDTH;

#[test]
#[ignore]
fn bench_poseidon() {
    // cargo test --release --package mt-goldilocks --lib -- benchmark_poseidons_goldilocks::bench_poseidon --exact --nocapture --ignored

    let n = 1 << 23;
    let poseidon1_8 = default_goldilocks_poseidon1_8();

    // warming
    let mut state_8: [FPacking; 8] = [FPacking::ZERO; 8];
    for _ in 0..1 << 15 {
        poseidon1_8.compress_in_place(&mut state_8);
    }
    let _ = black_box(state_8);

    let time = Instant::now();
    for _ in 0..n / PACKING_WIDTH {
        poseidon1_8.compress_in_place(&mut state_8);
    }
    let _ = black_box(state_8);
    let time_p1_simd = time.elapsed();
    println!(
        "Poseidon1 8 SIMD (width {}): {:.2}M hashes/s",
        PACKING_WIDTH,
        (n as f64 / time_p1_simd.as_secs_f64() / 1_000_000.0)
    );
}
