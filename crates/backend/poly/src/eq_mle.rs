use crate::*;
use crate::{EFPacking, PF};
use ::utils::{iter_array_chunks_padded, log2_strict_usize};
use field::*;
use rayon::prelude::*;

/// Log of number of threads to spawn.
/// Long term this should be a modifiable parameter and potentially be in an optimization file somewhere.
/// I've chosen 32 here as my machine has 20 logical cores.
const LOG_NUM_THREADS: usize = 5;

/// The number of threads to spawn for parallel computations.
const NUM_THREADS: usize = 1 << LOG_NUM_THREADS;

/// Given `evals` = (α_1, ..., α_n), returns a multilinear polynomial P in n variables,
/// defined on the boolean hypercube by: ∀ (x_1, ..., x_n) ∈ {0, 1}^n,
/// P(x_1, ..., x_n) = Π_{i=1}^{n} (x_i.α_i + (1 - x_i).(1 - α_i))
/// (often denoted as P(x) = eq(x, evals))
pub fn eval_eq<F: ExtensionField<PF<F>>>(eval: &[F]) -> Vec<F> {
    eval_eq_scaled(eval, F::ONE)
}

pub fn eval_eq_scaled<F: ExtensionField<PF<F>>>(eval: &[F], scalar: F) -> Vec<F> {
    // Alloc memory without initializing it to zero.
    // This is safe because we overwrite it inside `eval_eq`.
    let mut out = unsafe { uninitialized_vec(1 << eval.len()) };
    compute_eval_eq::<PF<F>, F, false>(eval, &mut out, scalar);
    out
}

pub fn eval_eq_packed<F: ExtensionField<PF<F>>>(eval: &[F]) -> Vec<EFPacking<F>> {
    eval_eq_packed_scaled(eval, F::ONE)
}

pub fn eval_eq_packed_scaled<F: ExtensionField<PF<F>>>(eval: &[F], scalar: F) -> Vec<EFPacking<F>> {
    // Alloc memory without initializing it to zero.
    // This is safe because we overwrite it inside `eval_eq`.
    let mut out = unsafe { uninitialized_vec(1 << (eval.len() - packing_log_width::<F>())) };
    compute_eval_eq_packed::<F, false>(eval, &mut out, scalar);
    out
}

pub fn compute_sparse_eval_eq<F: ExtensionField<PF<F>>>(selector: usize, eval: &[F], out: &mut [F], scalar: F) {
    if eval.is_empty() {
        out[selector] += scalar;
        return;
    }

    let new_out_size = 1 << eval.len();
    let out = &mut out[selector * new_out_size..][..new_out_size];

    compute_eval_eq::<PF<F>, F, true>(eval, out, scalar);
}

pub fn compute_sparse_eval_eq_packed<EF>(selector: usize, eval: &[EF], out: &mut [EFPacking<EF>], scalar: EF)
where
    EF: ExtensionField<PF<EF>>,
{
    let log_packing = packing_log_width::<EF>();
    if eval.len() < log_packing {
        let shift = log_packing - eval.len();
        let packed = &mut out[selector >> shift];
        let mut unpacked: Vec<EF> = unpack_extension(&[*packed]);
        compute_sparse_eval_eq::<EF>(selector & ((1 << shift) - 1), eval, &mut unpacked, scalar);
        *packed = pack_extension(&unpacked)[0];
        return;
    }

    let new_out_size = 1 << (eval.len() - log_packing);
    let out = &mut out[selector * new_out_size..][..new_out_size];
    compute_eval_eq_packed::<EF, true>(eval, out, scalar);
}

/// Computes the equality polynomial evaluations efficiently.
///
/// Given an evaluation point vector `eval`, the function computes
/// the equality polynomial recursively using the formula:
///
/// ```text
/// eq(X) = ∏ (1 - X_i + 2X_i z_i)
/// ```
///
/// where `z_i` are the constraint points.
///
/// If INITIALIZED is:
/// - false: the result is directly set to the `out` buffer
/// - true: the result is added to the `out` buffer
#[inline]
pub fn compute_eval_eq<F, EF, const INITIALIZED: bool>(eval: &[EF], out: &mut [EF], scalar: EF)
where
    F: Field,
    EF: ExtensionField<F>,
{
    // It's possible for this to be called with F = EF (Despite F actually being an extension field).
    //
    // IMPORTANT: We previously checked here that `packing_width > 1`,
    // but this check is **not viable** for Goldilocks on Neon or when not using `target-cpu=native`.
    //
    // Why? Because Neon SIMD vectors are 128 bits and Goldilocks elements are already 64 bits,
    // so no packing happens (width stays 1), and there's no performance advantage.
    //
    // Be careful: this means code relying on packing optimizations should **not assume**
    // `packing_width > 1` is always true.
    let packing_width = F::Packing::WIDTH;
    // debug_assert!(packing_width > 1);

    // Ensure that the output buffer size is correct:
    // It should be of size `2^n`, where `n` is the number of variables.
    debug_assert_eq!(out.len(), 1 << eval.len());

    // If the number of variables is small, there is no need to use
    // parallelization or packings.
    if eval.len() <= packing_width + 1 + LOG_NUM_THREADS {
        // A basic recursive approach.
        eval_eq_basic::<_, _, _, INITIALIZED>(eval, out, scalar);
    } else {
        let log_packing_width = log2_strict_usize(packing_width);
        let eval_len_min_packing = eval.len() - log_packing_width;

        // We split eval into three parts:
        // - eval[..LOG_NUM_THREADS] (the first LOG_NUM_THREADS elements)
        // - eval[LOG_NUM_THREADS..eval_len_min_packing] (the middle elements)
        // - eval[eval_len_min_packing..] (the last log_packing_width elements)

        // The middle elements are the ones which will be computed in parallel.
        // The last log_packing_width elements are the ones which will be packed.

        // We make a buffer of elements of size `NUM_THREADS`.
        let mut parallel_buffer = EF::ExtensionPacking::zero_vec(NUM_THREADS);
        let out_chunk_size = out.len() / NUM_THREADS;

        // Compute the equality polynomial corresponding to the last log_packing_width elements
        // and pack these.
        parallel_buffer[0] = packed_eq_poly(&eval[eval_len_min_packing..], scalar);

        // Update the buffer so it contains the evaluations of the equality polynomial
        // with respect to parts one and three.
        fill_buffer(eval[..LOG_NUM_THREADS].iter().rev(), &mut parallel_buffer);

        // Finally do all computations involving the middle elements in parallel.
        out.par_chunks_exact_mut(out_chunk_size)
            .zip(parallel_buffer.par_iter())
            .for_each(|(out_chunk, buffer_val)| {
                eval_eq_with_packed_scalar::<_, _, INITIALIZED>(
                    &eval[LOG_NUM_THREADS..(eval.len() - log_packing_width)],
                    out_chunk,
                    *buffer_val,
                );
            });
    }
}

#[inline]
pub fn compute_eval_eq_packed<EF, const INITIALIZED: bool>(eval: &[EF], out: &mut [EF::ExtensionPacking], scalar: EF)
where
    EF: ExtensionField<PF<EF>>,
{
    // It's possible for this to be called with F = EF (Despite F actually being an extension field).
    //
    // IMPORTANT: We previously checked here that `packing_width > 1`,
    // but this check is **not viable** for Goldilocks on Neon or when not using `target-cpu=native`.
    //
    // Why? Because Neon SIMD vectors are 128 bits and Goldilocks elements are already 64 bits,
    // so no packing happens (width stays 1), and there's no performance advantage.
    //
    // Be careful: this means code relying on packing optimizations should **not assume**
    // `packing_width > 1` is always true.
    let packing_width = packing_width::<EF>();
    let log_packing_width = log2_strict_usize(packing_width);

    assert!(log_packing_width <= eval.len());
    assert_eq!(out.len(), 1 << (eval.len() - log_packing_width));

    // If the number of variables is small, there is no need to use
    // parallelization or packings.
    if eval.len() <= packing_width + 1 + LOG_NUM_THREADS {
        // A basic recursive approach.
        let mut output_no_packing = EF::zero_vec(1 << eval.len());
        eval_eq_basic::<_, _, _, false>(eval, &mut output_no_packing, scalar);
        out.par_iter_mut()
            .zip(output_no_packing.into_par_iter().chunks(packing_width))
            .for_each(|(out_elem, chunk)| {
                if INITIALIZED {
                    *out_elem += EF::ExtensionPacking::from_ext_slice(&chunk);
                } else {
                    *out_elem = EF::ExtensionPacking::from_ext_slice(&chunk);
                }
            });
    } else {
        let log_packing_width = log2_strict_usize(packing_width);
        let eval_len_min_packing = eval.len() - log_packing_width;

        // We split eval into three parts:
        // - eval[..LOG_NUM_THREADS] (the first LOG_NUM_THREADS elements)
        // - eval[LOG_NUM_THREADS..eval_len_min_packing] (the middle elements)
        // - eval[eval_len_min_packing..] (the last log_packing_width elements)

        // The middle elements are the ones which will be computed in parallel.
        // The last log_packing_width elements are the ones which will be packed.

        // We make a buffer of elements of size `NUM_THREADS`.
        let mut parallel_buffer = EF::ExtensionPacking::zero_vec(NUM_THREADS);
        let out_chunk_size = out.len() / NUM_THREADS;

        // Compute the equality polynomial corresponding to the last log_packing_width elements
        // and pack these.
        parallel_buffer[0] = packed_eq_poly(&eval[eval_len_min_packing..], scalar);

        // Update the buffer so it contains the evaluations of the equality polynomial
        // with respect to parts one and three.
        fill_buffer(eval[..LOG_NUM_THREADS].iter().rev(), &mut parallel_buffer);

        // Finally do all computations involving the middle elements in parallel.
        out.par_chunks_exact_mut(out_chunk_size)
            .zip(parallel_buffer.par_iter())
            .for_each(|(out_chunk, buffer_val)| {
                eval_eq_with_packed_output::<_, _, INITIALIZED>(
                    &eval[LOG_NUM_THREADS..(eval.len() - log_packing_width)],
                    out_chunk,
                    *buffer_val,
                );
            });
    }
}

/// Computes the equality polynomial evaluations efficiently.
///
/// This function is similar to [`eval_eq`], but it assumes that we want to evaluate
/// at a base field point instead of an extension field point. This leads to a different
/// strategy which can better minimize data transfers.
///
/// Given an evaluation point vector `eval`, the function computes
/// the equality polynomial recursively using the formula:
///
/// ```text
/// eq(X) = ∏ (1 - X_i + 2X_i z_i)
/// ```
///
/// where `z_i` are the constraint points.
///
/// If INITIALIZED is:
/// - false: the result is directly set to the `out` buffer
/// - true: the result is added to the `out` buffer
#[inline]
pub fn compute_eval_eq_base<F, EF, const INITIALIZED: bool>(eval: &[F], out: &mut [EF], scalar: EF)
where
    F: Field,
    EF: ExtensionField<F>,
{
    // we assume that packing_width is a power of 2.
    let packing_width = F::Packing::WIDTH;

    // Ensure that the output buffer size is correct:
    // It should be of size `2^n`, where `n` is the number of variables.
    debug_assert_eq!(out.len(), 1 << eval.len());

    // If the number of variables is small, there is no need to use
    // parallelization or packings.
    if eval.len() <= packing_width + 1 + LOG_NUM_THREADS {
        // A basic recursive approach.
        eval_eq_basic::<_, _, _, INITIALIZED>(eval, out, scalar);
    } else {
        let log_packing_width = log2_strict_usize(packing_width);
        let eval_len_min_packing = eval.len() - log_packing_width;

        // We split eval into three parts:
        // - eval[..LOG_NUM_THREADS] (the first LOG_NUM_THREADS elements)
        // - eval[LOG_NUM_THREADS..eval_len_min_packing] (the middle elements)
        // - eval[eval_len_min_packing..] (the last log_packing_width elements)

        // The middle elements are the ones which will be computed in parallel.
        // The last log_packing_width elements are the ones which will be packed.

        // We make a buffer of PackedField elements of size `NUM_THREADS`.
        // Note that this is a slightly different strategy to `eval_eq` which instead
        // uses PackedExtensionField elements. Whilst this involves slightly more mathematical
        // operations, it seems to be faster in practice due to less data moving around.
        let mut parallel_buffer = F::Packing::zero_vec(NUM_THREADS);
        let out_chunk_size = out.len() / NUM_THREADS;

        // Compute the equality polynomial corresponding to the last log_packing_width elements
        // and pack these.
        parallel_buffer[0] = packed_eq_poly(&eval[eval_len_min_packing..], F::ONE);

        // Update the buffer so it contains the evaluations of the equality polynomial
        // with respect to parts one and three.
        fill_buffer(eval[..LOG_NUM_THREADS].iter().rev(), &mut parallel_buffer);

        // Finally do all computations involving the middle elements in parallel.
        out.par_chunks_exact_mut(out_chunk_size)
            .zip(parallel_buffer.par_iter())
            .for_each(|(out_chunk, buffer_val)| {
                base_eval_eq_packed::<_, _, INITIALIZED>(
                    &eval[LOG_NUM_THREADS..(eval.len() - log_packing_width)],
                    out_chunk,
                    *buffer_val,
                    scalar,
                );
            });
    }
}

#[inline]
pub fn compute_eval_eq_base_packed<F, EF, const INITIALIZED: bool>(
    eval: &[F],
    out: &mut [EF::ExtensionPacking],
    scalar: EF,
) where
    F: Field,
    EF: ExtensionField<F>,
{
    // we assume that packing_width is a power of 2.
    let packing_width = F::Packing::WIDTH;
    let log_packing_width = log2_strict_usize(packing_width);
    assert!(log_packing_width <= eval.len());
    assert_eq!(out.len(), 1 << (eval.len() - log_packing_width));

    // Ensure that the output buffer size is correct:
    // It should be of size `2^n`, where `n` is the number of variables.
    debug_assert_eq!(out.len(), 1 << (eval.len() - log_packing_width));

    // If the number of variables is small, there is no need to use
    // parallelization or packings.
    if eval.len() <= packing_width + 1 + LOG_NUM_THREADS {
        // A basic recursive approach.
        let mut output_no_packing = EF::zero_vec(1 << eval.len());
        eval_eq_basic::<_, _, _, false>(eval, &mut output_no_packing, scalar);
        out.par_iter_mut()
            .zip(output_no_packing.into_par_iter().chunks(packing_width))
            .for_each(|(out_elem, chunk)| {
                if INITIALIZED {
                    *out_elem += EF::ExtensionPacking::from_ext_slice(&chunk);
                } else {
                    *out_elem = EF::ExtensionPacking::from_ext_slice(&chunk);
                }
            });
    } else {
        let log_packing_width = log2_strict_usize(packing_width);
        let eval_len_min_packing = eval.len() - log_packing_width;

        // We split eval into three parts:
        // - eval[..LOG_NUM_THREADS] (the first LOG_NUM_THREADS elements)
        // - eval[LOG_NUM_THREADS..eval_len_min_packing] (the middle elements)
        // - eval[eval_len_min_packing..] (the last log_packing_width elements)

        // The middle elements are the ones which will be computed in parallel.
        // The last log_packing_width elements are the ones which will be packed.

        // We make a buffer of PackedField elements of size `NUM_THREADS`.
        // Note that this is a slightly different strategy to `eval_eq` which instead
        // uses PackedExtensionField elements. Whilst this involves slightly more mathematical
        // operations, it seems to be faster in practice due to less data moving around.
        let mut parallel_buffer = F::Packing::zero_vec(NUM_THREADS);
        let out_chunk_size = out.len() / NUM_THREADS;

        // Compute the equality polynomial corresponding to the last log_packing_width elements
        // and pack these.
        parallel_buffer[0] = packed_eq_poly(&eval[eval_len_min_packing..], F::ONE);

        // Update the buffer so it contains the evaluations of the equality polynomial
        // with respect to parts one and three.
        fill_buffer(eval[..LOG_NUM_THREADS].iter().rev(), &mut parallel_buffer);

        // Finally do all computations involving the middle elements in parallel.
        let scalar_packed = EF::ExtensionPacking::from(scalar);
        out.par_chunks_exact_mut(out_chunk_size)
            .zip(parallel_buffer.par_iter())
            .for_each(|(out_chunk, buffer_val)| {
                base_eval_eq_packed_with_packed_output::<F, EF, INITIALIZED>(
                    &eval[LOG_NUM_THREADS..(eval.len() - log_packing_width)],
                    out_chunk,
                    *buffer_val,
                    scalar_packed,
                );
            });
    }
}

/// Fills the `buffer` with evaluations of the equality polynomial
/// of degree `points.len()` multiplied by the value at `buffer[0]`.
///
/// Assume that `buffer[0]` contains `{eq(i, x)}` for `i \in \{0, 1\}^j` packed into a single
/// PackedExtensionField element. This function fills out the remainder of the buffer so that
/// `buffer[ind]` contains `{eq(ind, points) * eq(i, x)}` for `i \in \{0, 1\}^j`. Note that
/// `ind` is interpreted as an element of `\{0, 1\}^{points.len()}`.
#[allow(clippy::inline_always)] // Adding inline(always) seems to give a small performance boost.
#[inline(always)]
fn fill_buffer<'a, F, A>(points: impl ExactSizeIterator<Item = &'a F>, buffer: &mut [A])
where
    F: Field,
    A: Algebra<F> + Copy,
{
    for (ind, &entry) in points.enumerate() {
        let stride = 1 << ind;

        for index in 0..stride {
            let val = buffer[index];
            let scaled_val = val * entry;
            let new_val = val - scaled_val;

            buffer[index] = new_val;
            buffer[index + stride] = scaled_val;
        }
    }
}

/// Compute the scaled multilinear equality polynomial over `{0,1}` for a single variable.
///
/// This is the hardcoded base case for the equality polynomial `eq(x, z)`
/// in the case of a single variable `z = [z_0] ∈ 𝔽`, and returns:
///
/// \begin{equation}
/// [α ⋅ (1 - z_0), α ⋅ z_0]
/// \end{equation}
///
/// corresponding to the evaluations:
///
/// \begin{equation}
/// [α ⋅ eq(0, z), α ⋅ eq(1, z)]
/// \end{equation}
///
/// where the multilinear equality function is:
///
/// \begin{equation}
/// eq(x, z) = x ⋅ z + (1 - x)(1 - z)
/// \end{equation}
///
/// Concretely:
/// - For `x = 0`, we have:
///   \begin{equation}
///   eq(0, z_0) = 0 ⋅ z_0 + (1 - 0)(1 - z_0) = 1 - z_0
///   \end{equation}
/// - For `x = 1`, we have:
///   \begin{equation}
///   eq(1, z_0) = 1 ⋅ z_0 + (1 - 1)(1 - z_0) = z_0
///   \end{equation}
///
/// So the return value is:
/// - `[α ⋅ (1 - z_0), α ⋅ z_0]`
///
/// # Arguments
/// - `eval`: Slice containing the evaluation point `[z_0]` (must have length 1)
/// - `scalar`: A scalar multiplier `α` to scale the result by
///
/// # Returns
/// An array `[α ⋅ (1 - z_0), α ⋅ z_0]` representing the scaled evaluations
/// of `eq(x, z)` for `x ∈ {0,1}`.
#[allow(clippy::inline_always)] // Adding inline(always) seems to give a small performance boost.
#[inline(always)]
fn eval_eq_1<F, FP>(eval: &[F], scalar: FP) -> [FP; 2]
where
    F: Field,
    FP: Algebra<F> + Copy,
{
    assert_eq!(eval.len(), 1);

    // Extract the evaluation point z_0
    let z_0 = eval[0];

    // Compute α ⋅ z_0 = α ⋅ eq(1, z) and α ⋅ (1 - z_0) = α - α ⋅ z_0 = α ⋅ eq(0, z)
    let eq_1 = scalar * z_0;
    let eq_0 = scalar - eq_1;

    [eq_0, eq_1]
}

/// Compute the scaled multilinear equality polynomial over `{0,1}^2`.
///
/// This is the hardcoded base case for the multilinear equality polynomial `eq(x, z)`
/// when the evaluation point has 2 variables: `z = [z_0, z_1] ∈ 𝔽²`.
///
/// It computes and returns the vector:
///
/// \begin{equation}
/// [α ⋅ eq((0,0), z), α ⋅ eq((0,1), z), α ⋅ eq((1,0), z), α ⋅ eq((1,1), z)]
/// \end{equation}
///
/// where the multilinear equality polynomial is:
///
/// \begin{equation}
/// eq(x, z) = ∏_{i=0}^{1} (x_i ⋅ z_i + (1 - x_i)(1 - z_i))
/// \end{equation}
///
/// Concretely, this gives:
/// - `eq((0,0), z) = (1 - z_0)(1 - z_1)`
/// - `eq((0,1), z) = (1 - z_0)(z_1)`
/// - `eq((1,0), z) = z_0(1 - z_1)`
/// - `eq((1,1), z) = z_0(z_1)`
///
/// Then all outputs are scaled by `α`.
///
/// # Arguments
/// - `eval`: Slice `[z_0, z_1]`, the evaluation point in `𝔽²`
/// - `scalar`: The scalar multiplier `α ∈ 𝔽`
///
/// # Returns
/// An array `[α ⋅ eq((0,0), z), α ⋅ eq((0,1), z), α ⋅ eq((1,0), z), α ⋅ eq((1,1), z)]`
#[allow(clippy::inline_always)] // Helps with performance in tight loops
#[inline(always)]
fn eval_eq_2<F, FP>(eval: &[F], scalar: FP) -> [FP; 4]
where
    F: Field,
    FP: Algebra<F> + Copy,
{
    assert_eq!(eval.len(), 2);

    // Extract z_0, z_1 from the evaluation point
    let z_0 = eval[0];
    let z_1 = eval[1];

    // Compute s1 = α ⋅ z_0 = α ⋅ eq(1, -) and s0 = α - s1 = α ⋅ (1 - z_0) = α ⋅ eq(0, -)
    let s1 = scalar * z_0;
    let s0 = scalar - s1;

    // For x_0 = 0:
    // - s01 = s0 ⋅ z_1 = α ⋅ (1 - z_0) ⋅ z_1 = α ⋅ eq((0,1), z)
    // - s00 = s0 - s01 = α ⋅ (1 - z_0)(1 - z_1) = α ⋅ eq((0,0), z)
    let s01 = s0 * z_1;
    let s00 = s0 - s01;

    // For x_0 = 1:
    // - s11 = s1 ⋅ z_1 = α ⋅ z_0 ⋅ z_1 = α ⋅ eq((1,1), z)
    // - s10 = s1 - s11 = α ⋅ z_0(1 - z_1) = α ⋅ eq((1,0), z)
    let s11 = s1 * z_1;
    let s10 = s1 - s11;

    // Return values in lexicographic order of x = (x_0, x_1)
    [s00, s01, s10, s11]
}

/// Compute the scaled multilinear equality polynomial over `{0,1}³` for 3 variables.
///
/// This is the hardcoded base case for the equality polynomial `eq(x, z)`
/// in the case of three variables `z = [z_0, z_1, z_2] ∈ 𝔽³`, and returns:
///
/// \begin{equation}
/// [α ⋅ eq((0,0,0), z), α ⋅ eq((0,0,1), z), ..., α ⋅ eq((1,1,1), z)]
/// \end{equation}
///
/// where the multilinear equality function is defined as:
///
/// \begin{equation}
/// \mathrm{eq}(x, z) = \prod_{i=0}^{2} \left( x_i z_i + (1 - x_i)(1 - z_i) \right)
/// \end{equation}
///
/// For each binary vector `x ∈ {0,1}³`, this returns the scaled evaluation `α ⋅ eq(x, z)`,
/// in lexicographic order: `(0,0,0), (0,0,1), ..., (1,1,1)`.
///
/// # Arguments
/// - `eval`: A slice containing `[z_0, z_1, z_2]`, the evaluation point.
/// - `scalar`: A scalar multiplier `α` to apply to all results.
///
/// # Returns
/// An array of 8 values `[α ⋅ eq(x, z)]` for all `x ∈ {0,1}³`, in lex order.
#[allow(clippy::inline_always)] // Adding inline(always) seems to give a small performance boost.
#[inline(always)]
fn eval_eq_3<F, FP>(eval: &[F], scalar: FP) -> [FP; 8]
where
    F: Field,
    FP: Algebra<F> + Copy,
{
    assert_eq!(eval.len(), 3);

    // Extract z_0, z_1, z_2 from the evaluation point
    let z_0 = eval[0];
    let z_1 = eval[1];
    let z_2 = eval[2];

    // First dimension split: scalar * z_0 and scalar * (1 - z_0)
    let s1 = scalar * z_0; // α ⋅ z_0
    let s0 = scalar - s1; // α ⋅ (1 - z_0)

    // Second dimension split:
    // Group (0, x1) branch using s0 = α ⋅ (1 - z_0)
    let s01 = s0 * z_1; // α ⋅ (1 - z_0) ⋅ z_1
    let s00 = s0 - s01; // α ⋅ (1 - z_0) ⋅ (1 - z_1)

    // Group (1, x1) branch using s1 = α ⋅ z_0
    let s11 = s1 * z_1; // α ⋅ z_0 ⋅ z_1
    let s10 = s1 - s11; // α ⋅ z_0 ⋅ (1 - z_1)

    // Third dimension split:
    // For (0,0,x2) branch
    let s001 = s00 * z_2; // α ⋅ (1 - z_0)(1 - z_1) ⋅ z_2
    let s000 = s00 - s001; // α ⋅ (1 - z_0)(1 - z_1) ⋅ (1 - z_2)

    // For (0,1,x2) branch
    let s011 = s01 * z_2; // α ⋅ (1 - z_0) ⋅ z_1 ⋅ z_2
    let s010 = s01 - s011; // α ⋅ (1 - z_0) ⋅ z_1 ⋅ (1 - z_2)

    // For (1,0,x2) branch
    let s101 = s10 * z_2; // α ⋅ z_0 ⋅ (1 - z_1) ⋅ z_2
    let s100 = s10 - s101; // α ⋅ z_0 ⋅ (1 - z_1) ⋅ (1 - z_2)

    // For (1,1,x2) branch
    let s111 = s11 * z_2; // α ⋅ z_0 ⋅ z_1 ⋅ z_2
    let s110 = s11 - s111; // α ⋅ z_0 ⋅ z_1 ⋅ (1 - z_2)

    // Return all 8 evaluations in lexicographic order of x ∈ {0,1}³
    [s000, s001, s010, s011, s100, s101, s110, s111]
}

/// Computes the equality polynomial evaluations via a simple recursive algorithm.
///
/// Given an evaluation point vector `eval`, the function computes
/// the equality polynomial recursively using the formula:
///
/// ```text
/// eq(X) = scalar * ∏ (1 - X_i + 2X_i z_i)
/// ```
///
/// where `z_i` are the constraint points.
///
/// If INITIALIZED is:
/// - false: the result is directly set to the `out` buffer
/// - true: the result is added to the `out` buffer
#[allow(clippy::too_many_lines)]
#[inline]
fn eval_eq_basic<F, IF, EF, const INITIALIZED: bool>(eval: &[IF], out: &mut [EF], scalar: EF)
where
    F: Field,
    IF: Field,
    EF: ExtensionField<F> + Algebra<IF>,
{
    // Ensure that the output buffer size is correct:
    // It should be of size `2^n`, where `n` is the number of variables.
    debug_assert_eq!(out.len(), 1 << eval.len());

    match eval.len() {
        0 => {
            if INITIALIZED {
                out[0] += scalar;
            } else {
                out[0] = scalar;
            }
        }
        1 => {
            // Manually unroll for single variable case
            let eq_evaluations = eval_eq_1(eval, scalar);

            add_or_set_f::<_, INITIALIZED>(out, &eq_evaluations);
        }
        2 => {
            // Manually unroll for two variable case
            let eq_evaluations = eval_eq_2(eval, scalar);

            add_or_set_f::<_, INITIALIZED>(out, &eq_evaluations);
        }
        3 => {
            // Manually unroll for three variable case
            let eq_evaluations = eval_eq_3(eval, scalar);

            add_or_set_f::<_, INITIALIZED>(out, &eq_evaluations);
        }
        _ => {
            let (&x, tail) = eval.split_first().unwrap();

            // Divide the output buffer into two halves: one for `X_i = 0` and one for `X_i = 1`
            let (low, high) = out.split_at_mut(out.len() / 2);

            // Compute weight updates for the two branches:
            // - `s0` corresponds to the case when `X_i = 0`
            // - `s1` corresponds to the case when `X_i = 1`
            //
            // Mathematically, this follows the recurrence:
            // ```text
            // eq_{X1, ..., Xn}(X) = (1 - X_1) * eq_{X2, ..., Xn}(X) + X_1 * eq_{X2, ..., Xn}(X)
            // ```
            let s1 = scalar * x; // Contribution when `X_i = 1`
            let s0 = scalar - s1; // Contribution when `X_i = 0`

            // The recursive approach turns out to be faster than the iterative one here.
            // Probably related to nice cache locality.
            eval_eq_basic::<_, _, _, INITIALIZED>(tail, low, s0);
            eval_eq_basic::<_, _, _, INITIALIZED>(tail, high, s1);
        }
    }
}

/// Computes the equality polynomial evaluations via a simple recursive algorithm.
///
/// Unlike [`eval_eq_basic`], this function makes heavy use of packed values to speed up computations.
/// In particular `scalar` should be passed in as a packed value coming from [`packed_eq_poly`].
///
/// Essentially using packings this functions computes
///
/// ```text
/// eq(X) = scalar[j] * ∏ (1 - X_i + 2X_i z_i)
/// ```
///
/// for a collection of `i` at the same time. Here `scalar[j]` should be thought of as evaluations of an equality
/// polynomial over different variables so `eq(X)` ends up being the evaluation of the equality polynomial over
/// the combined set of variables.
///
/// It then updates the output buffer `out` with the computed values by adding them in.
#[allow(clippy::too_many_lines)]
#[inline]
fn eval_eq_with_packed_scalar<F: Field, EF: ExtensionField<F>, const INITIALIZED: bool>(
    eval: &[EF],
    out: &mut [EF],
    scalar: EF::ExtensionPacking,
) {
    // Ensure that the output buffer size is correct:
    // It should be of size `2^n`, where `n` is the number of variables.
    let width = F::Packing::WIDTH;
    debug_assert_eq!(out.len(), width << eval.len());

    match eval.len() {
        0 => {
            let result: Vec<EF> = EF::ExtensionPacking::to_ext_iter([scalar]).collect();
            add_or_set_f::<_, INITIALIZED>(out, &result);
        }
        1 => {
            // Manually unroll for single variable case
            let eq_evaluations = eval_eq_1(eval, scalar);

            let result: Vec<EF> = EF::ExtensionPacking::to_ext_iter(eq_evaluations).collect();
            add_or_set_f::<_, INITIALIZED>(out, &result);
        }
        2 => {
            // Manually unroll for two variables case
            let eq_evaluations = eval_eq_2(eval, scalar);

            let result: Vec<EF> = EF::ExtensionPacking::to_ext_iter(eq_evaluations).collect();
            add_or_set_f::<_, INITIALIZED>(out, &result);
        }
        3 => {
            const EVAL_LEN: usize = 8;

            // Manually unroll for three variable case
            let eq_evaluations = eval_eq_3(eval, scalar);

            // Unpack the evaluations back into EF elements and add to output.
            // We use `iter_array_chunks_padded` to allow us to use `add_slices` without
            // needing a vector allocation. Note that `eq_evaluations: [EF::ExtensionPacking: 8]`
            // so we know that `out.len() = 8 * F::Packing::WIDTH` meaning we can use `chunks_exact_mut`
            // and `iter_array_chunks_padded` will never actually pad anything.
            // This avoids the allocation used to accumulate `result` in the other branches. We could
            // do a similar strategy in those branches but, those branches should only be hit
            // infrequently in small cases which are already sufficiently fast.
            iter_array_chunks_padded::<_, EVAL_LEN>(EF::ExtensionPacking::to_ext_iter(eq_evaluations), EF::ZERO)
                .zip(out.chunks_exact_mut(EVAL_LEN))
                .for_each(|(res, out_chunk)| {
                    if INITIALIZED {
                        EF::add_slices(out_chunk, &res);
                    } else {
                        out_chunk.copy_from_slice(&res);
                    }
                });
        }
        _ => {
            let (&x, tail) = eval.split_first().unwrap();

            // Divide the output buffer into two halves: one for `X_i = 0` and one for `X_i = 1`
            let (low, high) = out.split_at_mut(out.len() / 2);

            // Compute weight updates for the two branches:
            // - `s0` corresponds to the case when `X_i = 0`
            // - `s1` corresponds to the case when `X_i = 1`
            //
            // Mathematically, this follows the recurrence:
            // ```text
            // eq_{X1, ..., Xn}(X) = (1 - X_1) * eq_{X2, ..., Xn}(X) + X_1 * eq_{X2, ..., Xn}(X)
            // ```
            let s1 = scalar * x; // Contribution when `X_i = 1`
            let s0 = scalar - s1; // Contribution when `X_i = 0`

            // The recursive approach turns out to be faster than the iterative one here.
            // Probably related to nice cache locality.
            eval_eq_with_packed_scalar::<_, _, INITIALIZED>(tail, low, s0);
            eval_eq_with_packed_scalar::<_, _, INITIALIZED>(tail, high, s1);
        }
    }
}

#[allow(clippy::too_many_lines)]
#[inline]
fn eval_eq_with_packed_output<F: Field, EF: ExtensionField<F>, const INITIALIZED: bool>(
    eval: &[EF],
    out: &mut [EF::ExtensionPacking],
    scalar: EF::ExtensionPacking,
) {
    // Ensure that the output buffer size is correct:
    // It should be of size `2^n`, where `n` is the number of variables.
    debug_assert_eq!(out.len(), 1 << eval.len());

    match eval.len() {
        0 => {
            add_or_set_pf::<_, INITIALIZED>(out, &[scalar]);
        }
        1 => {
            // Manually unroll for single variable case
            let eq_evaluations = eval_eq_1(eval, scalar);
            add_or_set_pf::<_, INITIALIZED>(out, &eq_evaluations);
        }
        2 => {
            // Manually unroll for two variables case
            let eq_evaluations = eval_eq_2(eval, scalar);
            add_or_set_pf::<_, INITIALIZED>(out, &eq_evaluations);
        }
        3 => {
            // Manually unroll for three variable case
            let eq_evaluations = eval_eq_3(eval, scalar);
            add_or_set_pf::<_, INITIALIZED>(out, &eq_evaluations);
        }
        _ => {
            let (&x, tail) = eval.split_first().unwrap();

            // Divide the output buffer into two halves: one for `X_i = 0` and one for `X_i = 1`
            let (low, high) = out.split_at_mut(out.len() / 2);

            // Compute weight updates for the two branches:
            // - `s0` corresponds to the case when `X_i = 0`
            // - `s1` corresponds to the case when `X_i = 1`
            //
            // Mathematically, this follows the recurrence:
            // ```text
            // eq_{X1, ..., Xn}(X) = (1 - X_1) * eq_{X2, ..., Xn}(X) + X_1 * eq_{X2, ..., Xn}(X)
            // ```
            let s1 = scalar * x; // Contribution when `X_i = 1`
            let s0 = scalar - s1; // Contribution when `X_i = 0`

            // The recursive approach turns out to be faster than the iterative one here.
            // Probably related to nice cache locality.
            eval_eq_with_packed_output::<_, _, INITIALIZED>(tail, low, s0);
            eval_eq_with_packed_output::<_, _, INITIALIZED>(tail, high, s1);
        }
    }
}

/// Computes the equality polynomial evaluations via a simple recursive algorithm.
///
/// Unlike [`eval_eq_basic`], this function makes heavy use of packed values to speed up computations.
/// In particular `scalar` should be passed in as a packed value coming from [`packed_eq_poly`].
///
/// Essentially using packings this functions computes
///
/// ```text
/// eq(X) = scalar[j] * ∏ (1 - X_i + 2X_i z_i)
/// ```
///
/// for a collection of `i` at the same time. Here `scalar[j]` should be thought of as evaluations of an equality
/// polynomial over different variables so `eq(X)` ends up being the evaluation of the equality polynomial over
/// the combined set of variables.
///
/// It then updates the output buffer `out` with the computed values by adding them in.
#[allow(clippy::too_many_lines)]
#[inline]
fn base_eval_eq_packed<F, EF, const INITIALIZED: bool>(
    eval_points: &[F],
    out: &mut [EF],
    eq_evals: F::Packing,
    scalar: EF,
) where
    F: Field,
    EF: ExtensionField<F>,
{
    // Ensure that the output buffer size is correct:
    // It should be of size `2^n`, where `n` is the number of variables.
    let width = F::Packing::WIDTH;
    debug_assert_eq!(out.len(), width << eval_points.len());

    match eval_points.len() {
        0 => {
            scale_and_add::<_, _, INITIALIZED>(out, eq_evals.as_slice(), scalar);
        }
        1 => {
            let eq_evaluations = eval_eq_1(eval_points, eq_evals);

            scale_and_add::<_, _, INITIALIZED>(out, F::Packing::unpack_slice(&eq_evaluations), scalar);
        }
        2 => {
            let eq_evaluations = eval_eq_2(eval_points, eq_evals);

            scale_and_add::<_, _, INITIALIZED>(out, F::Packing::unpack_slice(&eq_evaluations), scalar);
        }
        3 => {
            let eq_evaluations = eval_eq_3(eval_points, eq_evals);

            scale_and_add::<_, _, INITIALIZED>(out, F::Packing::unpack_slice(&eq_evaluations), scalar);
        }
        _ => {
            let (&x, tail) = eval_points.split_first().unwrap();

            // Divide the output buffer into two halves: one for `X_i = 0` and one for `X_i = 1`
            let (low, high) = out.split_at_mut(out.len() / 2);

            // Compute weight updates for the two branches:
            // - `s0` corresponds to the case when `X_i = 0`
            // - `s1` corresponds to the case when `X_i = 1`
            //
            // Mathematically, this follows the recurrence:
            // ```text
            // eq_{X1, ..., Xn}(X) = (1 - X_1) * eq_{X2, ..., Xn}(X) + X_1 * eq_{X2, ..., Xn}(X)
            // ```
            let s1 = eq_evals * x; // Contribution when `X_i = 1`
            let s0 = eq_evals - s1; // Contribution when `X_i = 0`

            // The recursive approach turns out to be faster than the iterative one here.
            // Probably related to nice cache locality.
            base_eval_eq_packed::<_, _, INITIALIZED>(tail, low, s0, scalar);
            base_eval_eq_packed::<_, _, INITIALIZED>(tail, high, s1, scalar);
        }
    }
}

#[allow(clippy::too_many_lines)]
#[inline]
fn base_eval_eq_packed_with_packed_output<F, EF, const INITIALIZED: bool>(
    eval_points: &[F],
    out: &mut [EF::ExtensionPacking],
    eq_evals: F::Packing,
    packed_scalar: EF::ExtensionPacking, // repeated F::Packing::WIDTH times
) where
    F: Field,
    EF: ExtensionField<F>,
{
    // Ensure that the output buffer size is correct:
    // It should be of size `2^n`, where `n` is the number of variables.
    let width = F::Packing::WIDTH;
    let log_packing_width = log2_strict_usize(width);
    debug_assert_eq!(out.len(), 1 << eval_points.len());
    debug_assert!(log_packing_width <= eval_points.len());

    match eval_points.len() {
        0 => {
            debug_assert_eq!(F::Packing::WIDTH, 1);
            let base_vals = F::Packing::pack_slice(eq_evals.as_slice());
            scale_and_add_pf::<F, EF, INITIALIZED>(out, base_vals, packed_scalar);
        }
        1 => {
            let eq_evaluations = eval_eq_1(eval_points, eq_evals);
            scale_and_add_pf::<F, EF, INITIALIZED>(out, eq_evaluations.as_slice(), packed_scalar);
        }
        2 => {
            let eq_evaluations = eval_eq_2(eval_points, eq_evals);
            scale_and_add_pf::<F, EF, INITIALIZED>(out, eq_evaluations.as_slice(), packed_scalar);
        }
        3 => {
            let eq_evaluations = eval_eq_3(eval_points, eq_evals);
            scale_and_add_pf::<F, EF, INITIALIZED>(out, eq_evaluations.as_slice(), packed_scalar);
        }
        _ => {
            let (&x, tail) = eval_points.split_first().unwrap();

            // Divide the output buffer into two halves: one for `X_i = 0` and one for `X_i = 1`
            let (low, high) = out.split_at_mut(out.len() / 2);

            // Compute weight updates for the two branches:
            // - `s0` corresponds to the case when `X_i = 0`
            // - `s1` corresponds to the case when `X_i = 1`
            //
            // Mathematically, this follows the recurrence:
            // ```text
            // eq_{X1, ..., Xn}(X) = (1 - X_1) * eq_{X2, ..., Xn}(X) + X_1 * eq_{X2, ..., Xn}(X)
            // ```
            let s1 = eq_evals * x; // Contribution when `X_i = 1`
            let s0 = eq_evals - s1; // Contribution when `X_i = 0`

            // The recursive approach turns out to be faster than the iterative one here.
            // Probably related to nice cache locality.
            base_eval_eq_packed_with_packed_output::<F, EF, INITIALIZED>(tail, low, s0, packed_scalar);
            base_eval_eq_packed_with_packed_output::<F, EF, INITIALIZED>(tail, high, s1, packed_scalar);
        }
    }
}

/// Adds or sets the equality polynomial evaluations in the output buffer.
///
/// If the output buffer is already initialized, it adds the evaluations otherwise
/// it copies the evaluations into the buffer directly.
#[inline]
fn add_or_set_f<F: Field, const INITIALIZED: bool>(out: &mut [F], evaluations: &[F]) {
    debug_assert_eq!(out.len(), evaluations.len());
    if INITIALIZED {
        F::add_slices(out, evaluations);
    } else {
        out.copy_from_slice(evaluations);
    }
}

#[inline]
fn add_or_set_pf<F: PrimeCharacteristicRing + Copy, const INITIALIZED: bool>(out: &mut [F], evaluations: &[F]) {
    debug_assert_eq!(out.len(), evaluations.len());
    if INITIALIZED {
        out.iter_mut().zip(evaluations).for_each(|(o, &e)| *o += e);
    } else {
        out.copy_from_slice(evaluations);
    }
}

/// Scales the evaluations by scalar and either adds the result to the output buffer or
/// sets the output buffer directly depending on the `INITIALIZED` flag.
///
/// If the output buffer is already initialized, it adds the evaluations otherwise
/// it copies the evaluations into the buffer directly.
#[inline]
fn scale_and_add<F: Field, EF: ExtensionField<F>, const INITIALIZED: bool>(
    out: &mut [EF],
    base_vals: &[F],
    scalar: EF,
) {
    // TODO: We can probably add a custom method to Plonky3 to handle this more efficiently (and use packings).
    // This approach is faster than collecting `scalar * eq_eval` into a vector and using `add_slices`. Presumably
    // this is because we avoid the allocation.
    if INITIALIZED {
        out.iter_mut().zip(base_vals).for_each(|(out, &eq_eval)| {
            *out += scalar * eq_eval;
        });
    } else {
        out.iter_mut().zip(base_vals).for_each(|(out, &eq_eval)| {
            *out = scalar * eq_eval;
        });
    }
}

#[inline]
fn scale_and_add_pf<F: Field, EF: ExtensionField<F>, const INITIALIZED: bool>(
    out: &mut [EF::ExtensionPacking],
    base_vals: &[F::Packing],
    packed_scalar: EF::ExtensionPacking, // repeated F::Packing::WIDTH times
) {
    // TODO: We can probably add a custom method to Plonky3 to handle this more efficiently (and use packings).
    // This approach is faster than collecting `scalar * eq_eval` into a vector and using `add_slices`. Presumably
    // this is because we avoid the allocation.
    base_vals.iter().zip(out.iter_mut()).for_each(|(chunk, out)| {
        let res = packed_scalar * *chunk;
        if INITIALIZED {
            *out += res;
        } else {
            *out = res;
        }
    });
}

/// Computes equality polynomial evaluations and packs them into a `PackedFieldExtension`.
///
/// Note that when `F = EF` is a PrimeField, `EF::ExtensionPacking = F::Packing` so this can
/// also be used to compute initial packed evaluations of the equality polynomial over base
/// field elements (instead of extension field elements).
///
/// The length of `eval` must be equal to the `log2` of `F::Packing::WIDTH`.
#[allow(clippy::inline_always)] // Adding inline(always) seems to give a small performance boost.
#[inline(always)]
fn packed_eq_poly<F: Field, EF: ExtensionField<F>>(eval: &[EF], scalar: EF) -> EF::ExtensionPacking {
    // As this function is only available in this file, debug_assert should be fine here.
    // If this function becomes public, this should be changed to an assert.
    debug_assert_eq!(F::Packing::WIDTH, 1 << eval.len());

    // We build up the evaluations of the equality polynomial in buffer.
    let mut buffer = EF::zero_vec(1 << eval.len());
    buffer[0] = scalar;

    fill_buffer(eval.iter().rev(), &mut buffer);

    // Finally we need to do a "transpose" to get a `PackedFieldExtension` element.
    EF::ExtensionPacking::from_ext_slice(&buffer)
}

pub fn parallel_inner_repeat<A: Copy + Send + Sync>(src: &[A], n: usize) -> Vec<A> {
    if src.len() * n <= 1 << 12 {
        // sequential repeat
        src.iter().flat_map(|&v| std::iter::repeat_n(v, n)).collect()
    } else {
        let res = unsafe { uninitialized_vec::<A>(src.len() * n) };
        src.par_iter().enumerate().for_each(|(i, &v)| {
            for j in 0..n {
                unsafe {
                    std::ptr::write(res.as_ptr().cast_mut().add(i * n + j), v);
                }
            }
        });
        res
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use field::Field;
    use koala_bear::QuinticExtensionFieldKB;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    use super::*;
    type F = koala_bear::KoalaBear;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_compute_sparse_eval() {
        let eval = vec![
            F::ZERO,
            F::ONE,
            F::ONE,
            F::ZERO,
            F::new(96),
            F::new(85),
            F::new(1),
            F::new(854),
            F::new(2),
        ];
        let scalar = F::new(789);
        let mut out_structured = F::zero_vec(1 << eval.len());
        let mut out_unstructured = F::zero_vec(1 << eval.len());
        compute_sparse_eval_eq(6, &eval[4..], &mut out_structured, scalar);
        compute_eval_eq::<F, F, true>(&eval, &mut out_unstructured, scalar);
        assert_eq!(out_structured, out_unstructured);
    }

    #[test]
    fn test_compute_sparse_eval_packed() {
        let n_vars: usize = 16;
        assert!(n_vars.is_multiple_of(2));
        let starts = vec![
            vec![EF::ZERO, EF::ONE, EF::ONE, EF::ZERO, EF::ZERO],
            vec![],
            vec![EF::ZERO, EF::ZERO, EF::ZERO, EF::ZERO],
            vec![EF::ONE, EF::ONE, EF::ONE, EF::ONE],
            vec![EF::ONE; n_vars - 1],
            vec![EF::ZERO; n_vars],
            [EF::ZERO, EF::ONE].repeat(n_vars / 2),
            [EF::ONE, EF::ZERO].repeat(n_vars / 2),
        ];
        let mut rng = StdRng::seed_from_u64(0);
        let scalar: EF = rng.random();
        for mut point in starts {
            while point.len() < n_vars {
                point.push(rng.random());
            }
            let mut out_no_packing = EF::zero_vec(1 << n_vars);
            let mut out_packed = EFPacking::<EF>::zero_vec(1 << (n_vars - packing_log_width::<EF>()));
            compute_eval_eq::<F, EF, true>(&point, &mut out_no_packing, scalar);
            let boolean_starts = point
                .iter()
                .take_while(|&&x| x.is_zero() || x.is_one())
                .map(|&x| x.is_one())
                .collect::<Vec<_>>();
            let starts_big_endian = boolean_starts.iter().fold(0, |acc, &bit| (acc << 1) | (bit as usize));
            let point = &point[boolean_starts.len()..];
            compute_sparse_eval_eq_packed(starts_big_endian, point, &mut out_packed, scalar);
            let unpacked: Vec<EF> = unpack_extension(&out_packed);
            assert_eq!(out_no_packing, unpacked);
        }
    }

    #[test]
    fn test_packed_eval_eq() {
        let packing_width = <F as Field>::Packing::WIDTH;
        let log_packing_width = log2_strict_usize(packing_width);
        for n_vars in log_packing_width..20 {
            println!("\nn_vars = {}", n_vars);
            {
                // EXTENSION

                let mut rng = StdRng::seed_from_u64(0);
                let eval = (0..n_vars).map(|_| rng.random()).collect::<Vec<EF>>();
                let scalar: EF = rng.random();

                let mut out_1 = EF::zero_vec(1 << n_vars);
                let time = Instant::now();
                compute_eval_eq::<F, EF, true>(&eval, &mut out_1, scalar);
                println!("EXTENSION NOT PACKED: {:?}", time.elapsed());

                let packing_width = <F as Field>::Packing::WIDTH;
                let log_packing_width = log2_strict_usize(packing_width);
                let mut out_2 =
                    <EF as ExtensionField<F>>::ExtensionPacking::zero_vec(1 << (n_vars - log_packing_width));
                let time = Instant::now();
                compute_eval_eq_packed::<_, true>(&eval, &mut out_2, scalar);
                println!("EXTENSION PACKED: {:?}", time.elapsed());

                let unpacked_out_2: Vec<EF> =
                    <EF as ExtensionField<F>>::ExtensionPacking::to_ext_iter_vec(out_2.clone());
                assert_eq!(out_1, unpacked_out_2);

                let mut out_3 = EF::zero_vec(1 << n_vars);
                let time = Instant::now();
                compute_eval_eq::<F, EF, true>(&eval, &mut out_3, scalar);
                let out_3_packed = out_3
                    .par_chunks_exact(packing_width)
                    .map(<EF as ExtensionField<F>>::ExtensionPacking::from_ext_slice)
                    .collect::<Vec<_>>();
                println!("EXTENSION PACKED AFTER: {:?}", time.elapsed());

                assert_eq!(out_2, out_3_packed);
            }
            {
                // BASE

                let mut rng = StdRng::seed_from_u64(0);
                let eval = (0..n_vars).map(|_| rng.random()).collect::<Vec<F>>();
                let scalar: EF = rng.random();

                let mut out_1 = EF::zero_vec(1 << n_vars);
                let time = Instant::now();
                compute_eval_eq_base::<F, EF, true>(&eval, &mut out_1, scalar);
                println!("BASE NOT PACKED: {:?}", time.elapsed());

                let packing_width = <F as Field>::Packing::WIDTH;
                let log_packing_width = log2_strict_usize(packing_width);
                let mut out_2 =
                    <EF as ExtensionField<F>>::ExtensionPacking::zero_vec(1 << (n_vars - log_packing_width));
                let time = Instant::now();
                compute_eval_eq_base_packed::<F, _, true>(&eval, &mut out_2, scalar);
                println!("BASE PACKED: {:?}", time.elapsed());

                let unpacked_out_2: Vec<EF> =
                    <EF as ExtensionField<F>>::ExtensionPacking::to_ext_iter_vec(out_2.clone());
                assert_eq!(out_1, unpacked_out_2);

                let mut out_3 = EF::zero_vec(1 << n_vars);
                let time = Instant::now();
                compute_eval_eq_base::<F, EF, true>(&eval, &mut out_3, scalar);
                let out_3_packed = out_3
                    .par_chunks_exact(packing_width)
                    .map(<EF as ExtensionField<F>>::ExtensionPacking::from_ext_slice)
                    .collect::<Vec<_>>();
                println!("BASE PACKED AFTER: {:?}", time.elapsed());

                assert_eq!(out_2, out_3_packed);
            }
        }
    }
}
