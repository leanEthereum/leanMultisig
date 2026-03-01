use std::hint::black_box;
use std::time::Instant;

use field::{Field, PackedValue, PrimeCharacteristicRing};

use crate::KoalaBear;

type F = KoalaBear;
type FPacking = <KoalaBear as Field>::Packing;
const PACKING_WIDTH: usize = <FPacking as PackedValue>::WIDTH;

#[test]
#[ignore]
fn bench_add_vs_mul_packed() {
    let n: usize = 1 << 26;

    // --- Packed additions ---
    {
        let mut a = FPacking::from(F::new(123456));
        let b = FPacking::from(F::new(789012));
        let time = Instant::now();
        for _ in 0..n {
            a = a + b;
        }
        let elapsed = time.elapsed();
        let _ = black_box(a);
        let total_ops = n as f64 * PACKING_WIDTH as f64;
        println!(
            "Packed ADD: {:.2}M ops/s  ({} iters × {} lanes = {:.0}M scalar adds in {:.3}s)",
            total_ops / elapsed.as_secs_f64() / 1e6,
            n,
            PACKING_WIDTH,
            total_ops / 1e6,
            elapsed.as_secs_f64(),
        );
    }

    // --- Packed multiplications (by packed) ---
    {
        let mut a = FPacking::from(F::new(123456));
        let b = FPacking::from(F::new(789012));
        let time = Instant::now();
        for _ in 0..n {
            a = a * b;
        }
        let elapsed = time.elapsed();
        let _ = black_box(a);
        let total_ops = n as f64 * PACKING_WIDTH as f64;
        println!(
            "Packed MUL: {:.2}M ops/s  ({} iters × {} lanes = {:.0}M scalar muls in {:.3}s)",
            total_ops / elapsed.as_secs_f64() / 1e6,
            n,
            PACKING_WIDTH,
            total_ops / 1e6,
            elapsed.as_secs_f64(),
        );
    }

    // --- Packed multiplication by scalar KoalaBear ---
    {
        let mut a = FPacking::from(F::new(123456));
        let b = F::new(789012);
        let time = Instant::now();
        for _ in 0..n {
            a = a * b;
        }
        let elapsed = time.elapsed();
        let _ = black_box(a);
        let total_ops = n as f64 * PACKING_WIDTH as f64;
        println!(
            "Packed MUL (by scalar): {:.2}M ops/s  ({} iters × {} lanes = {:.0}M scalar muls in {:.3}s)",
            total_ops / elapsed.as_secs_f64() / 1e6,
            n,
            PACKING_WIDTH,
            total_ops / 1e6,
            elapsed.as_secs_f64(),
        );
    }

    // --- Packed a+a (by value, to compare with .double()) ---
    {
        let mut a = FPacking::from(F::new(123456));
        let time = Instant::now();
        for _ in 0..n {
            a = a + a;
        }
        let elapsed = time.elapsed();
        let _ = black_box(a);
        let total_ops = n as f64 * PACKING_WIDTH as f64;
        println!(
            "Packed A+A: {:.2}M ops/s  ({} iters × {} lanes = {:.0}M scalar adds in {:.3}s)",
            total_ops / elapsed.as_secs_f64() / 1e6,
            n,
            PACKING_WIDTH,
            total_ops / 1e6,
            elapsed.as_secs_f64(),
        );
    }

    // --- Packed double (.double() takes &self) ---
    {
        let mut a = FPacking::from(F::new(123456));
        let time = Instant::now();
        for _ in 0..n {
            a = a.double();
        }
        let elapsed = time.elapsed();
        let _ = black_box(a);
        let total_ops = n as f64 * PACKING_WIDTH as f64;
        println!(
            "Packed DBL: {:.2}M ops/s  ({} iters × {} lanes = {:.0}M scalar doubles in {:.3}s)",
            total_ops / elapsed.as_secs_f64() / 1e6,
            n,
            PACKING_WIDTH,
            total_ops / 1e6,
            elapsed.as_secs_f64(),
        );
    }

    // --- Scalar additions (for reference) ---
    {
        let mut a = F::new(123456);
        let b = F::new(789012);
        let time = Instant::now();
        for _ in 0..n {
            a = a + b;
        }
        let elapsed = time.elapsed();
        let _ = black_box(a);
        println!(
            "Scalar ADD: {:.2}M ops/s  ({:.0}M adds in {:.3}s)",
            n as f64 / elapsed.as_secs_f64() / 1e6,
            n as f64 / 1e6,
            elapsed.as_secs_f64(),
        );
    }

    // --- Scalar multiplications (for reference) ---
    {
        let mut a = F::new(123456);
        let b = F::new(789012);
        let time = Instant::now();
        for _ in 0..n {
            a = a * b;
        }
        let elapsed = time.elapsed();
        let _ = black_box(a);
        println!(
            "Scalar MUL: {:.2}M ops/s  ({:.0}M muls in {:.3}s)",
            n as f64 / elapsed.as_secs_f64() / 1e6,
            n as f64 / 1e6,
            elapsed.as_secs_f64(),
        );
    }
}
