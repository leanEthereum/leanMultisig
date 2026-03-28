use field::{ExtensionField, PackedFieldExtension, PackedValue};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use poly::{PFPacking, pack_extension};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use std::hint::black_box;
use std::time::Instant;

use mt_sumcheck::{
    compute_product_sumcheck_polynomial, compute_product_sumcheck_polynomial_base_ext_packed,
    compute_product_sumcheck_polynomial_ext_ext_packed,
};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
type PF = <F as field::Field>::Packing;
type EFP = <EF as ExtensionField<F>>::ExtensionPacking;

fn packing_decompose(e: EFP) -> Vec<EF> {
    <EFP as PackedFieldExtension<F, EF>>::to_ext_iter([e]).collect()
}

#[test]
fn bench_product_sumcheck() {
    let mut rng = StdRng::seed_from_u64(42);

    println!("\n=== Base × Extension (packed) ===");
    for log_n in [20, 25] {
        let n = 1usize << log_n;
        let pol_0: Vec<F> = (0..n).map(|_| rng.random()).collect();
        let pol_1: Vec<EF> = (0..n).map(|_| rng.random()).collect();
        let sum: EF = pol_0.iter().zip(pol_1.iter()).map(|(&a, &b)| b * a).sum();
        let n_iters = 20;

        let pol_0_packed = PFPacking::<EF>::pack_slice(&pol_0);
        let pol_1_packed = pack_extension::<EF>(&pol_1);

        let start = Instant::now();
        for _ in 0..n_iters {
            black_box(compute_product_sumcheck_polynomial(
                black_box(pol_0_packed),
                black_box(&pol_1_packed),
                sum,
                packing_decompose,
            ));
        }
        let us_old = start.elapsed().as_micros() as f64 / n_iters as f64;

        let start = Instant::now();
        for _ in 0..n_iters {
            black_box(compute_product_sumcheck_polynomial_base_ext_packed::<5, _, _, _, EF>(
                black_box(pol_0_packed),
                black_box(&pol_1_packed),
                sum,
            ));
        }
        let us_new = start.elapsed().as_micros() as f64 / n_iters as f64;

        let r_old = compute_product_sumcheck_polynomial(pol_0_packed, &pol_1_packed, sum, packing_decompose);
        let r_new =
            compute_product_sumcheck_polynomial_base_ext_packed::<5, _, _, _, EF>(pol_0_packed, &pol_1_packed, sum);
        assert_eq!(r_old.coeffs, r_new.coeffs, "base×ext mismatch at log_n={log_n}");

        println!(
            "  log_n={log_n:2}  old={us_old:>6.0}µs  new={us_new:>6.0}µs  speedup={:.2}x",
            us_old / us_new
        );
    }

    println!("\n=== Extension × Extension (packed) ===");
    for log_n in [20, 25] {
        let n = 1usize << log_n;
        let pol_0: Vec<EF> = (0..n).map(|_| rng.random()).collect();
        let pol_1: Vec<EF> = (0..n).map(|_| rng.random()).collect();
        let sum: EF = pol_0.iter().zip(pol_1.iter()).map(|(&a, &b)| b * a).sum();
        let n_iters = 20;

        let pol_0_packed = pack_extension::<EF>(&pol_0);
        let pol_1_packed = pack_extension::<EF>(&pol_1);

        let start = Instant::now();
        for _ in 0..n_iters {
            black_box(compute_product_sumcheck_polynomial(
                black_box(&pol_0_packed),
                black_box(&pol_1_packed),
                sum,
                packing_decompose,
            ));
        }
        let us_old = start.elapsed().as_micros() as f64 / n_iters as f64;

        let start = Instant::now();
        for _ in 0..n_iters {
            black_box(compute_product_sumcheck_polynomial_ext_ext_packed::<F, EFP, EF>(
                black_box(&pol_0_packed),
                black_box(&pol_1_packed),
                sum,
            ));
        }
        let us_new = start.elapsed().as_micros() as f64 / n_iters as f64;

        let r_old = compute_product_sumcheck_polynomial(&pol_0_packed, &pol_1_packed, sum, packing_decompose);
        let r_new = compute_product_sumcheck_polynomial_ext_ext_packed::<F, EFP, EF>(&pol_0_packed, &pol_1_packed, sum);
        assert_eq!(r_old.coeffs, r_new.coeffs, "ext×ext mismatch at log_n={log_n}");

        println!(
            "  log_n={log_n:2}  old={us_old:>6.0}µs  new={us_new:>6.0}µs  speedup={:.2}x",
            us_old / us_new
        );
    }
}
