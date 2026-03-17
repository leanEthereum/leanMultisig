use std::hint::black_box;
use std::time::Instant;

use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;

use crate::{KoalaBear, default_koalabear_poseidon1_16, default_koalabear_poseidon2_16};

type FPacking = <KoalaBear as Field>::Packing;
const PACKING_WIDTH: usize = <FPacking as PackedValue>::WIDTH;

#[test]
fn test_poseidon1_packed() {
    let poseidon1 = default_koalabear_poseidon1_16();
    let mut state = [FPacking::ZERO; 16];
    poseidon1.compress_in_place(&mut state);
    let _ = black_box(state);
}

#[test]
#[ignore]
fn bench_poseidon_1_vs_2_plaintext() {
    // cargo test --release --package mt-koala-bear --lib -- benchmark_poseidons::bench_poseidon_1_vs_2_plaintext --exact --nocapture --ignored

    let n = 1 << 23;
    let poseidon1 = default_koalabear_poseidon1_16();
    let poseidon2 = default_koalabear_poseidon2_16();

    // warming
    let mut state = [FPacking::ZERO; 16];
    for _ in 0..1 << 20 {
        poseidon1.compress_in_place(&mut state);
    }
    let _ = black_box(state);

    let time = Instant::now();
    let mut state = [FPacking::ZERO; 16];
    for _ in 0..n / PACKING_WIDTH {
        poseidon1.compress_in_place(&mut state);
    }
    let _ = black_box(state);
    let time_p1_simd = time.elapsed();
    println!(
        "Poseidon1 SIMD (width {}): {:.2}M hashes/s",
        PACKING_WIDTH,
        (n as f64 / time_p1_simd.as_secs_f64() / 1_000_000.0)
    );

    let time = Instant::now();
    let mut state = [FPacking::ZERO; 16];
    for _ in 0..n / PACKING_WIDTH {
        poseidon2.compress_in_place(&mut state);
    }
    let _ = black_box(state);
    let time_p2_simd = time.elapsed();
    println!(
        "Poseidon2 SIMD (width {}): {:.2}M hashes/s ({:.2}x faster than P1)",
        PACKING_WIDTH,
        (n as f64 / time_p2_simd.as_secs_f64() / 1_000_000.0),
        (time_p1_simd.as_secs_f64() / time_p2_simd.as_secs_f64())
    );
}
