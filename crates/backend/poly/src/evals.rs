use crate::*;
use crate::{EFPacking, PF};
use field::{ExtensionField, Field, PrimeCharacteristicRing};
use itertools::Itertools;
use rayon::{join, prelude::*};
use std::borrow::Borrow;

pub trait EvaluationsList<F: Field> {
    fn num_variables(&self) -> usize;
    fn num_evals(&self) -> usize;
    fn evaluate<EF: ExtensionField<F>>(&self, point: &MultilinearPoint<EF>) -> EF;
    fn evaluate_sequential<EF: ExtensionField<F>>(&self, point: &MultilinearPoint<EF>) -> EF;
    fn as_constant(&self) -> F;
    fn evaluate_sparse<EF: ExtensionField<F>>(&self, selector: usize, point: &MultilinearPoint<EF>) -> EF;
}

impl<F: Field, EL: Borrow<[F]>> EvaluationsList<F> for EL {
    fn num_variables(&self) -> usize {
        self.borrow().len().ilog2() as usize
    }

    fn num_evals(&self) -> usize {
        self.borrow().len()
    }

    fn evaluate<EF: ExtensionField<F>>(&self, point: &MultilinearPoint<EF>) -> EF {
        eval_multilinear::<_, _, true>(self.borrow(), point)
    }

    fn evaluate_sequential<EF: ExtensionField<F>>(&self, point: &MultilinearPoint<EF>) -> EF {
        eval_multilinear::<_, _, false>(self.borrow(), point)
    }

    fn as_constant(&self) -> F {
        assert_eq!(self.borrow().len(), 1);
        self.borrow()[0]
    }

    fn evaluate_sparse<EF: ExtensionField<F>>(&self, selector: usize, point: &MultilinearPoint<EF>) -> EF {
        (&self.borrow()[selector << point.len()..][..(1 << point.len())]).evaluate(point)
    }
}

/// Multiply the polynomial by a scalar factor.
#[must_use]
pub fn scale_poly<F: Field, EF: ExtensionField<F>>(poly: &[F], factor: EF) -> Vec<EF> {
    if poly.len() < PARALLEL_THRESHOLD {
        poly.iter().map(|&e| factor * e).collect()
    } else {
        poly.par_iter().map(|&e| factor * e).collect()
    }
}

fn eval_multilinear<F, EF, const PARALLEL: bool>(evals: &[F], point: &[EF]) -> EF
where
    F: Field,
    EF: ExtensionField<F>,
{
    eval_multilinear_generic::<_, _, _, _, _, _, PARALLEL>(
        evals,
        point,
        &|a: F, b: EF| b * a,
        &|a: EF, b: F| a + b,
        &|a: EF, b: EF| a * b,
    )
}

// Turns out to be slower than non packed version:

// fn eval_multilinear_packed_base<EF>(evals: &[PFPacking<EF>], point: &[EF]) -> EF
// where
//     EF: ExtensionField<PF<EF>>,
// {
//     let log_width = packing_log_width::<EF>();
//     let res_packed: EFPacking<EF> = eval_multilinear_generic(
//         evals,
//         &point[..point.len() - log_width],
//         &|a: PFPacking<EF>, b: EF| EFPacking::<EF>::from(a) * b,
//         &|a: EFPacking<EF>, b: PFPacking<EF>| a + b,
//         &|a: EFPacking<EF>, b: EF| a * b,
//     );
//     let res_unpacked: Vec<EF> = unpack_extension(&[res_packed]);
//     eval_multilinear(&res_unpacked, &point[point.len() - log_width..])
// }

pub fn eval_packed<EF, const PARALLEL: bool>(evals: &[EFPacking<EF>], point: &[EF]) -> EF
where
    EF: ExtensionField<PF<EF>>,
{
    let log_width = packing_log_width::<EF>();
    let res_packed: EFPacking<EF> = eval_multilinear_generic::<_, _, _, _, _, _, PARALLEL>(
        evals,
        &point[..point.len() - log_width],
        &|a: EFPacking<EF>, b: EF| a * b,
        &|a: EFPacking<EF>, b: EFPacking<EF>| a + b,
        &|a: EFPacking<EF>, b: EF| a * b,
    );
    let res_unpacked: Vec<EF> = unpack_extension(&[res_packed]);
    eval_multilinear::<_, _, PARALLEL>(&res_unpacked, &point[point.len() - log_width..])
}

fn eval_multilinear_generic<Coeffs, Point, Res, MCP, ARC, MRP, const PARALLEL: bool>(
    evals: &[Coeffs],
    point: &[Point],
    mul_coeffs_point: &MCP,
    add_res_coeffs: &ARC,
    mul_res_point: &MRP,
) -> Res
where
    Coeffs: Copy + PrimeCharacteristicRing + Sync + Send,
    Point: Field,
    Res: Copy + PrimeCharacteristicRing + From<Coeffs> + Sync + Send,
    MCP: Fn(Coeffs, Point) -> Res + Sync + Send,
    ARC: Fn(Res, Coeffs) -> Res + Sync + Send,
    MRP: Fn(Res, Point) -> Res + Sync + Send,
{
    // Ensure that the number of evaluations matches the number of variables in the point.
    //
    // This is a critical invariant: `evals.len()` must be exactly `2^point.len()`.
    debug_assert_eq!(evals.len(), 1 << point.len());

    // Select the optimal evaluation strategy based on the number of variables.
    match point {
        // Case: 0 Variables (Constant Polynomial)
        //
        // A polynomial with zero variables is just a constant.
        [] => evals[0].into(),

        // Case: 1 Variable (Linear Interpolation)
        //
        // This is the base case for the recursion: f(x) = f(0) * (1-x) + f(1) * x.
        // The expression is an optimized form: f(0) + x * (f(1) - f(0)).
        [x] => add_res_coeffs(mul_coeffs_point(evals[1] - evals[0], *x), evals[0]),

        [x0, x1] => {
            // Interpolate along the x1-axis for x0=0 to get `a0`.
            let a0 = add_res_coeffs(mul_coeffs_point(evals[1] - evals[0], *x1), evals[0]);
            // Interpolate along the x1-axis for x0=1 to get `a1`.
            let a1 = add_res_coeffs(mul_coeffs_point(evals[3] - evals[2], *x1), evals[2]);
            // Finally, interpolate between `a0` and `a1` along the x0-axis.
            mul_res_point(a1 - a0, *x0) + a0
        }

        [x0, x1, x2] => {
            let a00 = add_res_coeffs(mul_coeffs_point(evals[1] - evals[0], *x2), evals[0]);
            let a01 = add_res_coeffs(mul_coeffs_point(evals[3] - evals[2], *x2), evals[2]);
            let a10 = add_res_coeffs(mul_coeffs_point(evals[5] - evals[4], *x2), evals[4]);
            let a11 = add_res_coeffs(mul_coeffs_point(evals[7] - evals[6], *x2), evals[6]);
            let a0 = a00 + mul_res_point(a01 - a00, *x1);
            let a1 = a10 + mul_res_point(a11 - a10, *x1);
            a0 + mul_res_point(a1 - a0, *x0)
        }

        [x0, x1, x2, x3] => {
            let a000 = add_res_coeffs(mul_coeffs_point(evals[1] - evals[0], *x3), evals[0]);
            let a001 = add_res_coeffs(mul_coeffs_point(evals[3] - evals[2], *x3), evals[2]);
            let a010 = add_res_coeffs(mul_coeffs_point(evals[5] - evals[4], *x3), evals[4]);
            let a011 = add_res_coeffs(mul_coeffs_point(evals[7] - evals[6], *x3), evals[6]);
            let a100 = add_res_coeffs(mul_coeffs_point(evals[9] - evals[8], *x3), evals[8]);
            let a101 = add_res_coeffs(mul_coeffs_point(evals[11] - evals[10], *x3), evals[10]);
            let a110 = add_res_coeffs(mul_coeffs_point(evals[13] - evals[12], *x3), evals[12]);
            let a111 = add_res_coeffs(mul_coeffs_point(evals[15] - evals[14], *x3), evals[14]);
            let a00 = a000 + mul_res_point(a001 - a000, *x2);
            let a01 = a010 + mul_res_point(a011 - a010, *x2);
            let a10 = a100 + mul_res_point(a101 - a100, *x2);
            let a11 = a110 + mul_res_point(a111 - a110, *x2);
            let a0 = a00 + mul_res_point(a01 - a00, *x1);
            let a1 = a10 + mul_res_point(a11 - a10, *x1);
            a0 + mul_res_point(a1 - a0, *x0)
        }
        // General Case (5+ Variables)
        //
        // This handles all other cases, using one of two different strategies.
        [x, tail @ ..] => {
            // For a very large number of variables, the recursive approach is not the most efficient.
            //
            // We switch to a more direct, non-recursive algorithm that is better suited for wide parallelization.
            if point.len() >= 20 {
                // The `evals` are ordered lexicographically, meaning the first variable's bit changes the slowest.
                //
                // To align our computation with this memory layout, we process the point's coordinates in reverse.
                let mut point_rev = point.to_vec();
                point_rev.reverse();

                // Split the reversed point's coordinates into two halves:
                // - `z0` (low-order vars)
                // - `z1` (high-order vars).
                let mid = point_rev.len() / 2;
                let (z0, z1) = point_rev.split_at(mid);

                // Precomputation of Basis Polynomials
                //
                // The basis polynomial eq(v, p) can be split: eq(v, p) = eq(v_low, p_low) * eq(v_high, p_high).
                //
                // We precompute all `2^|z0|` values of eq(v_low, p_low) and store them in `left`.
                // We precompute all `2^|z1|` values of eq(v_high, p_high) and store them in `right`.

                // Allocate uninitialized memory for the low-order basis polynomial evaluations.
                let mut left = unsafe { uninitialized_vec(1 << z0.len()) };
                // Allocate uninitialized memory for the high-order basis polynomial evaluations.
                let mut right = unsafe { uninitialized_vec(1 << z1.len()) };

                // The `eval_eq` function requires the variables in their original order, so we reverse the halves back.
                let mut z0_ordered = z0.to_vec();
                z0_ordered.reverse();
                // Compute all eq(v_low, p_low) values and fill the `left` vector.
                compute_eval_eq::<_, _, false>(&z0_ordered, &mut left, Point::ONE);

                // Repeat the process for the high-order variables.
                let mut z1_ordered = z1.to_vec();
                z1_ordered.reverse();
                // Compute all eq(v_high, p_high) values and fill the `right` vector.
                compute_eval_eq::<_, _, false>(&z1_ordered, &mut right, Point::ONE);

                if PARALLEL {
                    // Parallelized Final Summation
                    //
                    // This chain of operations computes the regrouped sum:
                    // Σ_{v_high} eq(v_high, p_high) * (Σ_{v_low} f(v_high, v_low) * eq(v_low, p_low))
                    evals
                        .par_chunks(left.len())
                        .zip_eq(right.par_iter())
                        .map(|(part, &c)| {
                            // This is the inner sum: a dot product between the evaluation chunk and the `left` basis values.
                            mul_res_point(
                                part.iter()
                                    .zip_eq(left.iter())
                                    .map(|(&a, &b)| mul_coeffs_point(a, b))
                                    .sum::<Res>(),
                                c,
                            )
                        })
                        .sum()
                } else {
                    evals
                        .chunks(left.len())
                        .zip_eq(right.iter())
                        .map(|(part, &c)| {
                            // This is the inner sum: a dot product between the evaluation chunk and the `left` basis values.
                            mul_res_point(
                                part.iter()
                                    .zip_eq(left.iter())
                                    .map(|(&a, &b)| mul_coeffs_point(a, b))
                                    .sum::<Res>(),
                                c,
                            )
                        })
                        .sum()
                }
            } else {
                // For moderately sized inputs (5 to 19 variables), use the recursive strategy.
                //
                // Split the evaluations into two halves, corresponding to the first variable being 0 or 1.
                let (f0, f1) = evals.split_at(evals.len() / 2);

                // Recursively evaluate on the two smaller hypercubes.
                let (f0_eval, f1_eval) = {
                    // Only spawn parallel tasks if the subproblem is large enough to overcome
                    // the overhead of threading.
                    let work_size: usize = (1 << 15) / std::mem::size_of::<Coeffs>();
                    if evals.len() > work_size && PARALLEL {
                        join(
                            || {
                                eval_multilinear_generic::<_, _, _, _, _, _, PARALLEL>(
                                    f0,
                                    tail,
                                    mul_coeffs_point,
                                    add_res_coeffs,
                                    mul_res_point,
                                )
                            },
                            || {
                                eval_multilinear_generic::<_, _, _, _, _, _, PARALLEL>(
                                    f1,
                                    tail,
                                    mul_coeffs_point,
                                    add_res_coeffs,
                                    mul_res_point,
                                )
                            },
                        )
                    } else {
                        // For smaller subproblems, execute sequentially.
                        (
                            eval_multilinear_generic::<_, _, _, _, _, _, false>(
                                f0,
                                tail,
                                mul_coeffs_point,
                                add_res_coeffs,
                                mul_res_point,
                            ),
                            eval_multilinear_generic::<_, _, _, _, _, _, false>(
                                f1,
                                tail,
                                mul_coeffs_point,
                                add_res_coeffs,
                                mul_res_point,
                            ),
                        )
                    }
                };
                // Perform the final linear interpolation for the first variable `x`.
                f0_eval + mul_res_point(f1_eval - f0_eval, *x)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use koala_bear::QuinticExtensionFieldKB;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    type F = QuinticExtensionFieldKB;
    type EF = QuinticExtensionFieldKB;

    use super::*;

    #[test]
    fn test_evaluate() {
        let n_vars = 24;
        let mut rng = StdRng::seed_from_u64(0);
        let poly = (0..(1 << n_vars)).map(|_| rng.random()).collect::<Vec<F>>();
        let point = MultilinearPoint((0..n_vars).map(|_| rng.random()).collect::<Vec<EF>>());

        let time = Instant::now();
        let res_normal = eval_multilinear::<_, _, true>(&poly, &point);
        println!("Normal eval time: {:?}", time.elapsed());

        let packed_poly = pack_extension(&poly);
        let time = Instant::now();
        let res_packed = eval_packed::<_, true>(&packed_poly, &point);
        println!("Packed eval time: {:?}", time.elapsed());

        assert_eq!(res_normal, res_packed);
    }
}
