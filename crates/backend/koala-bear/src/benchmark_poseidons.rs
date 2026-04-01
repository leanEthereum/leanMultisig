use std::hint::black_box;
use std::time::Instant;

use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;

use crate::default_koalabear_poseidon1_24;
use crate::{KoalaBear, default_koalabear_poseidon1_16};

type FPacking = <KoalaBear as Field>::Packing;
const PACKING_WIDTH: usize = <FPacking as PackedValue>::WIDTH;

#[test]
#[ignore]
fn bench_poseidon() {
    // cargo test --release --package mt-koala-bear --lib -- benchmark_poseidons::bench_poseidon --exact --nocapture --ignored

    let n = 1 << 23;
    let poseidon1_16 = default_koalabear_poseidon1_16();
    let poseidon1_24 = default_koalabear_poseidon1_24();

    // warming
    let mut state_16: [FPacking; 16] = [FPacking::ZERO; 16];
    let mut state_24: [FPacking; 24] = [FPacking::ZERO; 24];
    for _ in 0..1 << 15 {
        poseidon1_16.compress_in_place(&mut state_16);
        poseidon1_24.compress_in_place(&mut state_24);
    }
    let _ = black_box(state_16);
    let _ = black_box(state_24);

    let time = Instant::now();
    for _ in 0..n / PACKING_WIDTH {
        poseidon1_16.compress_in_place(&mut state_16);
    }
    let _ = black_box(state_16);
    let time_p1_simd = time.elapsed();
    println!(
        "Poseidon1 16 SIMD (width {}): {:.2}M hashes/s",
        PACKING_WIDTH,
        (n as f64 / time_p1_simd.as_secs_f64() / 1_000_000.0)
    );

    let time = Instant::now();
    for _ in 0..n / PACKING_WIDTH {
        poseidon1_24.compress_in_place(&mut state_24);
    }
    let _ = black_box(state_24);
    let time_p1_simd = time.elapsed();
    println!(
        "Poseidon1 24 SIMD (width {}): {:.2}M hashes/s",
        PACKING_WIDTH,
        (n as f64 / time_p1_simd.as_secs_f64() / 1_000_000.0)
    );
}
