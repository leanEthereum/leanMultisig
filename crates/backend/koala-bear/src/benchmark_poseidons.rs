use std::time::Instant;

use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;
use rayon::prelude::*;

use crate::{KoalaBear, Poseidon1KoalaBear16, default_koalabear_poseidon2_16};

type F = KoalaBear;
type FPacking = <KoalaBear as Field>::Packing;
const PACKING_WIDTH: usize = <FPacking as PackedValue>::WIDTH;

#[test]
#[ignore]
fn bench_koalabear_1_vs_2_plaintext() {
    let n = 1 << 22;
    let poseidon1 = Poseidon1KoalaBear16 {};
    let poseidon2 = default_koalabear_poseidon2_16();

    // single threaded, no SIMD
    let time = Instant::now();
    let mut state = [F::ZERO; 16];
    for _ in 0..n {
        poseidon1.compress_in_place(&mut state);
    }
    let time_p1 = time.elapsed();
    println!(
        "Poseidon1, single-threaded, no SIMD: {:.2}M hashes / s",
        (n as f64 / time_p1.as_secs_f64() / 1_000_000.0)
    );

    let time = Instant::now();
    let mut state = [F::ZERO; 16];
    for _ in 0..n {
        poseidon2.compress_in_place(&mut state);
    }
    let time_p2 = time.elapsed();
    println!(
        "Poseidon2, single-threaded, no SIMD: {:.2}M hashes / s ({:.1}x faster than Poseidon1)",
        (n as f64 / time_p2.as_secs_f64() / 1_000_000.0),
        (time_p1.as_secs_f64() / time_p2.as_secs_f64())
    );

    // SIMD, single-threaded
    let time = Instant::now();
    let mut state = [FPacking::ZERO; 16];
    for _ in 0..n / PACKING_WIDTH {
        poseidon1.compress_in_place(&mut state);
    }
    let time_p1_simd = time.elapsed();
    println!(
        "Poseidon1, single-threaded, SIMD: {:.2}M hashes / s",
        (n as f64 / time_p1_simd.as_secs_f64() / 1_000_000.0)
    );

    let time = Instant::now();
    let mut state = [FPacking::ZERO; 16];
    for _ in 0..n / PACKING_WIDTH {
        poseidon2.compress_in_place(&mut state);
    }
    let time_p2_simd = time.elapsed();
    println!(
        "Poseidon2, single-threaded, SIMD: {:.2}M hashes / s ({:.1}x faster than Poseidon1)",
        (n as f64 / time_p2_simd.as_secs_f64() / 1_000_000.0),
        (time_p1_simd.as_secs_f64() / time_p2_simd.as_secs_f64())
    );

    // SIMD, multi-threaded
    let time = Instant::now();
    (0..n / PACKING_WIDTH).into_par_iter().for_each(|i| {
        let mut state = [FPacking::ZERO; 16];
        state[0] = FPacking::from_usize(i);
        poseidon1.compress_in_place(&mut state);
    });
    let time_p1_simd_mt = time.elapsed();
    println!(
        "Poseidon1, multi-threaded, SIMD: {:.2}M hashes / s",
        (n as f64 / time_p1_simd_mt.as_secs_f64() / 1_000_000.0)
    );

    let time = Instant::now();
    (0..n / PACKING_WIDTH).into_par_iter().for_each(|i| {
        let mut state = [FPacking::ZERO; 16];
        state[0] = FPacking::from_usize(i);
        poseidon2.compress_in_place(&mut state);
    });
    let time_p2_simd_mt = time.elapsed();
    println!(
        "Poseidon2, multi-threaded, SIMD: {:.2}M hashes / s ({:.1}x faster than Poseidon1)",
        (n as f64 / time_p2_simd_mt.as_secs_f64() / 1_000_000.0),
        (time_p1_simd_mt.as_secs_f64() / time_p2_simd_mt.as_secs_f64())
    );
}
