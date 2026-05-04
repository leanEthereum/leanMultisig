// Credits:
// - whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

/* DFT (Discrete Fourier Transform) on "evaluations".

Often, the polynomial used in the PIOP is represented by its evaluations on the boolean hypercube.
It turns out we also need this representation in the Sumcheck of WHIR.

When the prover must "Reed Solomon" encode a multilinear polynomial `P(x_1, ..., x_n)`,
i.e compute `P(α, α², α⁴, ..., α^(2^(n-1)))` for every `α` such that `α^(2^(n + log_inv_rate)) = 1`,
the more straightforward approach is to convert the polynomial represented by its evals to
the coefficients representation (canonical basis), and then to apply a well known DFT algorithm.

However this approach is not the most efficient because the conversion evals -> coeffs is `n * log(n)`.

To avoid dealing with the coeffs, we can directly perform the DFT on the evals, using the fact that:
```text
    P(α, α², α⁴, ..., α^(2^(n-1))) = (1-α) * P(0, α², α⁴, ..., α^(2^(n-1))) + α * P(1, α², α⁴, ..., α^(2^(n-1)))
                = P(0, α², α⁴, ..., α^(2^(n-1))) + α * (P(1, α², α⁴, ..., α^(2^(n-1))) - P(0, α², α⁴, ..., α^(2^(n-1))))
```

Credits: https://github.com/Plonky3/Plonky3 (radix_2_small_batch.rs)

*/
use std::sync::RwLock;

#[cfg(test)]
use field::BasedVectorSpace;
use field::PackedValue;
use field::{Field, PackedField, TwoAdicField};
use itertools::Itertools;
use poly::uninitialized_vec;

use rayon::prelude::*;
use tracing::instrument;
use utils::{as_base_slice, log2_strict_usize};

use crate::{Matrix, RowMajorMatrix, RowMajorMatrixViewMut};

/// The number of layers to compute in each parallelization.
const LAYERS_PER_GROUP: usize = 3;

#[derive(Default, Debug)]
pub(crate) struct EvalsDft<F> {
    twiddles: RwLock<Vec<Vec<F>>>,
}

impl<F: TwoAdicField> EvalsDft<F> {
    pub(crate) fn max_n_twiddles(&self) -> usize {
        let guard = self.twiddles.read().unwrap();
        1 << guard.len()
    }

    fn roots_of_unity_table(&self, n: usize) -> Vec<Vec<F>> {
        let lg_n = log2_strict_usize(n);
        let generator = F::two_adic_generator(lg_n);
        let half_n = 1 << (lg_n - 1);
        // nth_roots = [1, g, g^2, g^3, ..., g^{n/2 - 1}]
        let nth_roots = generator.powers().collect_n(half_n);

        (0..lg_n)
            .map(|i| nth_roots.iter().step_by(1 << i).copied().collect())
            .collect()
    }

    pub(crate) fn update_twiddles(&self, fft_len: usize) {
        // TODO: This recomputes the entire table from scratch if we
        // need it to be larger, which is wasteful.
        let mut guard = self.twiddles.write().unwrap();
        let curr_max_fft_len = 1 << guard.len();
        if fft_len > curr_max_fft_len {
            *guard = self.roots_of_unity_table(fft_len);
        }
    }
}

impl<F> EvalsDft<F>
where
    F: TwoAdicField,
{
    pub(crate) fn dft_batch_by_evals_skip_initial_with_zero_tail(
        &self,
        mut mat: RowMajorMatrix<F>,
        skip_initial: usize,
        zero_start_rows: usize,
    ) -> RowMajorMatrix<F> {
        let h = mat.height();
        let w = mat.width();
        let log_h = log2_strict_usize(h);
        assert!(skip_initial < log_h);
        let effective_log_h = log_h - skip_initial;

        let zero_start_rows = zero_start_rows.min(h);
        let mut zero_start_elem = zero_start_rows.saturating_mul(w);

        self.update_twiddles(h);
        let root_table = self.twiddles.read().unwrap();
        let len = root_table.len();
        let root_table = &root_table[len - log_h..len - skip_initial];

        // Find the number of rows which can roughly fit in L1 cache.
        // The strategy is the same as `dft_batch` but in reverse.
        // We start by moving `num_par_rows` rows onto each thread and doing a handful of
        // consecutive layers within each chunk. After this we recombine and do a standard
        // round-by-round parallelization for the remaining layers.
        let num_par_rows = estimate_num_rows_in_l1::<F>(h, w);
        let log_num_par_rows = log2_strict_usize(num_par_rows);
        let chunk_size = num_par_rows * w;

        let par_initial_layer_count = log_num_par_rows.saturating_sub(skip_initial).min(effective_log_h);

        // For the initial blocks, they are small enough that we can split the matrix
        // into chunks of size `chunk_size` and process them in parallel.
        // This avoids passing data between threads, which can be expensive.
        if par_initial_layer_count > 0 {
            par_initial_layers(
                &mut mat.values,
                chunk_size,
                &root_table[root_table.len() - par_initial_layer_count..],
                w,
                zero_start_elem,
            );
            zero_start_elem = advance_zero_boundary(zero_start_elem, chunk_size);
        }

        // For the layers involving blocks larger than `num_par_rows`, we will
        // parallelize across the blocks.

        let multi_layer_dft = MyMultiLayerButterfly {};

        // If the total number of layers is not a multiple of `LAYERS_PER_GROUP`,
        // we need to handle a few extra layers separately before entering the main loop.
        let remaining = effective_log_h - par_initial_layer_count;
        let corr = remaining % LAYERS_PER_GROUP;
        if corr > 0 {
            let extra_root_table = &root_table
                [root_table.len() - par_initial_layer_count - corr..root_table.len() - par_initial_layer_count];
            dft_layer_par_extra_layers(
                &mut mat.as_view_mut(),
                extra_root_table,
                multi_layer_dft,
                w,
                zero_start_elem,
            );
            if !extra_root_table.is_empty() {
                let largest_block = extra_root_table[0].len() * 2 * w;
                zero_start_elem = advance_zero_boundary(zero_start_elem, largest_block);
            }
        }

        // We do `LAYERS_PER_GROUP` layers of the DFT at once, to minimize how much data we need to transfer
        // between threads.
        for (twiddles_small, twiddles_med, twiddles_large) in root_table
            [..root_table.len() - par_initial_layer_count - corr]
            .iter()
            .rev()
            .map(|slice| unsafe { as_base_slice::<EvalsButterfly<F>, F>(slice) })
            .tuples()
        {
            dft_layer_par_triple(
                &mut mat.as_view_mut(),
                twiddles_small,
                twiddles_med,
                twiddles_large,
                multi_layer_dft,
                w,
                zero_start_elem,
            );
            let largest_block = twiddles_large.len() * 2 * w;
            zero_start_elem = advance_zero_boundary(zero_start_elem, largest_block);
        }

        mat
    }

    #[cfg(test)]
    pub(crate) fn dft_algebra_batch_by_evals<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        mat: RowMajorMatrix<V>,
    ) -> RowMajorMatrix<V> {
        let init_width = mat.width();
        let base_mat = RowMajorMatrix::new(V::flatten_to_base(mat.values), init_width * V::DIMENSION);
        let base_dft_output = self.dft_batch_by_evals_skip_initial_with_zero_tail(base_mat, 0, usize::MAX);
        RowMajorMatrix::new(V::reconstitute_from_base(base_dft_output.values), init_width)
    }

    /// DFT of `source` duplicated `2^log_inv_rate` times along the row axis.
    ///
    /// Rather than materialise the `h = source_rows << log_inv_rate` expanded buffer, we
    /// note that layers `0..log_inv_rate` of the size-`h` FFT act on identical row pairs
    /// and are no-ops — so the first non-trivial layer is `log_inv_rate`, which pairs
    /// source rows `2c` and `2c+1` via `2^log_inv_rate` twiddles. This function fuses the
    /// expansion with that layer (and as many subsequent cache-resident layers as fit in
    /// an L1-sized "super-chunk") in one pass over the output buffer. Remaining layers are
    /// then handed to the standard parallel DFT.
    ///
    /// `non_zero_prefix_rows` promises that source rows past that index are zero, so the
    /// corresponding super-chunks are zero-filled and the later layers skip them.
    #[instrument(skip_all)]
    pub(crate) fn fused_prepare_and_dft(
        &self,
        source: &[F],
        w: usize,
        log_inv_rate: usize,
        non_zero_prefix_rows: usize,
    ) -> RowMajorMatrix<F> {
        debug_assert_eq!(source.len() % w, 0);
        let source_rows = source.len() / w;
        debug_assert!(source_rows.is_power_of_two());
        let h = source_rows << log_inv_rate;
        let log_h = log2_strict_usize(h);
        assert!(log_inv_rate < log_h);

        // Super-chunk must hold at least one layer-r chunk (`2 << log_inv_rate` output
        // rows). L1 budget above that improves cache locality for the in-chunk layers.
        let num_par_rows = estimate_num_rows_in_l1::<F>(h, w).max(2 << log_inv_rate).min(h);
        let log_num_par_rows = log2_strict_usize(num_par_rows);
        let super_chunk_size = num_par_rows * w;
        let layer_r_chunk_size = (2 << log_inv_rate) * w;
        let chunks_per_super = num_par_rows >> (log_inv_rate + 1);

        // Round up to pair boundary so each layer-r butterfly's two source rows are both
        // in the data region or both in the zero tail.
        let non_zero_rows = non_zero_prefix_rows.next_multiple_of(2).min(source_rows);
        let non_zero_chunks_r = non_zero_rows / 2;
        let non_zero_super_chunks = non_zero_chunks_r.div_ceil(chunks_per_super);

        self.update_twiddles(h);
        let root_table = self.twiddles.read().unwrap();
        let len = root_table.len();
        let layer_r_twiddles: &[EvalsButterfly<F>] = unsafe { as_base_slice(&root_table[len - 1 - log_inv_rate]) };
        let post_r_root_table = &root_table[len - log_num_par_rows..len - 1 - log_inv_rate];

        let mut out = unsafe { uninitialized_vec::<F>(h * w) };

        out.par_chunks_exact_mut(super_chunk_size)
            .enumerate()
            .for_each(|(sc, super_chunk)| {
                if sc >= non_zero_super_chunks {
                    super_chunk.fill(F::ZERO);
                    return;
                }
                // Phase 1: compute layer `log_inv_rate` for each layer-r chunk in this
                // super-chunk, reading directly from the compact source.
                for local_c in 0..chunks_per_super {
                    let global_c = sc * chunks_per_super + local_c;
                    let chunk_slot = &mut super_chunk[local_c * layer_r_chunk_size..(local_c + 1) * layer_r_chunk_size];
                    if global_c >= non_zero_chunks_r {
                        chunk_slot.fill(F::ZERO);
                        continue;
                    }
                    let src_left = &source[2 * global_c * w..(2 * global_c + 1) * w];
                    let src_right = &source[(2 * global_c + 1) * w..(2 * global_c + 2) * w];
                    let (left_half, right_half) = chunk_slot.split_at_mut(layer_r_chunk_size / 2);
                    for (j, twiddle) in layer_r_twiddles.iter().enumerate() {
                        let out_left = &mut left_half[j * w..(j + 1) * w];
                        let out_right = &mut right_half[j * w..(j + 1) * w];
                        if j == 0 {
                            butterfly_out_of_place(TwiddleFreeEvalsButterfly, src_left, src_right, out_left, out_right);
                        } else {
                            butterfly_out_of_place(*twiddle, src_left, src_right, out_left, out_right);
                        }
                    }
                }
                // Phase 2: remaining cache-local layers (strides fit in the super-chunk).
                if !post_r_root_table.is_empty() {
                    initial_layers(super_chunk, post_r_root_table, w);
                }
            });
        drop(root_table);

        let zero_start_rows = non_zero_super_chunks.saturating_mul(num_par_rows).min(h);
        if log_num_par_rows >= log_h {
            return RowMajorMatrix::new(out, w);
        }
        self.dft_batch_by_evals_skip_initial_with_zero_tail(
            RowMajorMatrix::new(out, w),
            log_num_par_rows,
            zero_start_rows,
        )
    }
}

/// Splits the matrix into chunks of size `chunk_size` and performs
/// the initial layers of the iFFT in parallel on each chunk.
///
/// This avoids passing data between threads, which can be expensive.
///
/// Basically identical to [par_remaining_layers] but in reverse and we
/// also divide by the height.
#[inline]
fn par_initial_layers<F: Field>(
    mat: &mut [F],
    chunk_size: usize,
    root_table: &[Vec<F>],
    width: usize,
    zero_start_elem: usize,
) {
    mat.par_chunks_exact_mut(chunk_size)
        .enumerate()
        .for_each(|(idx, chunk)| {
            if idx * chunk_size >= zero_start_elem {
                return;
            }
            initial_layers(chunk, root_table, width);
        });
}

#[inline]
fn advance_zero_boundary(zero_start_elem: usize, largest_block: usize) -> usize {
    zero_start_elem.div_ceil(largest_block) * largest_block
}

#[inline]
fn initial_layers<F: Field>(chunk: &mut [F], root_table: &[Vec<F>], width: usize) {
    for twiddles in root_table.iter().rev() {
        let twiddles: &[EvalsButterfly<F>] = unsafe { as_base_slice(twiddles) };
        dft_layer(chunk, twiddles, width);
    }
}

#[inline]
fn dft_layer<F: Field, B: Butterfly<F>>(vec: &mut [F], twiddles: &[B], width: usize) {
    vec.chunks_exact_mut(twiddles.len() * 2 * width).for_each(|block| {
        let (left, right) = block.split_at_mut(twiddles.len() * width);
        left.chunks_exact_mut(width)
            .zip(right.chunks_exact_mut(width))
            .zip(twiddles.iter())
            .enumerate()
            .for_each(|(i, ((hi_chunk, lo_chunk), twiddle))| {
                if i == 0 {
                    TwiddleFreeEvalsButterfly.apply_to_rows(hi_chunk, lo_chunk);
                } else {
                    twiddle.apply_to_rows(hi_chunk, lo_chunk);
                }
            });
    });
}

#[inline]
fn dft_layer_par<F: Field, B: Butterfly<F>>(vec: &mut [F], twiddles: &[B], width: usize, zero_start_elem: usize) {
    let block_size = twiddles.len() * 2 * width;
    vec.par_chunks_exact_mut(block_size)
        .enumerate()
        .for_each(|(idx, block)| {
            if idx * block_size >= zero_start_elem {
                return;
            }
            let (left, right) = block.split_at_mut(twiddles.len() * width);
            left.par_chunks_exact_mut(width)
                .zip(right.par_chunks_exact_mut(width))
                .zip(twiddles.par_iter())
                .for_each(|((hi_chunk, lo_chunk), twiddle)| {
                    twiddle.apply_to_rows(hi_chunk, lo_chunk);
                });
        });
}

/// Applies two layers of the Radix-2 FFT butterfly network making use of parallelization.
///
/// Splits the matrix into blocks of rows and performs in-place butterfly operations
/// on each block. Advantage of doing two layers at once is it reduces the amount of
/// data transferred between threads.
///
/// # Arguments
/// - `mat`: Mutable matrix whose height is a power of two.
/// - `twiddles_small`: Precomputed twiddle factors for the layer with the smallest block size.
/// - `twiddles_large`: Precomputed twiddle factors for the layer with the largest block size.
/// - `multi_butterfly`: Multi-layer butterfly which applies the two layers in the correct order.
#[inline]
fn dft_layer_par_double<F: Field, B: Butterfly<F>, M: MultiLayerButterfly<F, B>>(
    mat: &mut RowMajorMatrixViewMut<'_, F>,
    twiddles_small: &[B],
    twiddles_large: &[B],
    multi_butterfly: M,
    width: usize,
    zero_start_elem: usize,
) {
    debug_assert!(
        mat.height().is_multiple_of(twiddles_small.len()),
        "Matrix height must be divisible by the number of twiddles"
    );

    assert_eq!(twiddles_large.len(), twiddles_small.len() * 2);

    let block_size = twiddles_large.len() * 2 * width;
    // TODO optimal workload size with L1 cache
    mat.values
        .par_chunks_exact_mut(block_size)
        .enumerate()
        .filter(move |(idx, _)| idx * block_size < zero_start_elem)
        .for_each(|(_, block)| {
            // (0..twiddles_small.len()).into_par_iter().for_each(|ind| {
            //     let hi_hi = slice_ref_mut(block, ind * width, width);
            //     let hi_lo = slice_ref_mut(block, (ind + twiddles_small.len()) * width, width);
            //     let lo_hi = slice_ref_mut(block, (ind + 2 * twiddles_small.len()) * width, width);
            //     let lo_lo = slice_ref_mut(block, (ind + 3 * twiddles_small.len()) * width, width);
            //     multi_butterfly.apply_2_layers(
            //         ((hi_hi, hi_lo), (lo_hi, lo_lo)),
            //         ind,
            //         twiddles_small,
            //         twiddles_large,
            //     );
            // });
            let (hi_blocks, lo_blocks) = block.split_at_mut(twiddles_small.len() * width * 2);
            let (hi_hi_blocks, hi_lo_blocks) = hi_blocks.split_at_mut(twiddles_small.len() * width);
            let (lo_hi_blocks, lo_lo_blocks) = lo_blocks.split_at_mut(twiddles_small.len() * width);
            hi_hi_blocks
                .par_chunks_exact_mut(width)
                .zip(hi_lo_blocks.par_chunks_exact_mut(width))
                .zip(lo_hi_blocks.par_chunks_exact_mut(width))
                .zip(lo_lo_blocks.par_chunks_exact_mut(width))
                .enumerate()
                .for_each(|(ind, (((hi_hi, hi_lo), lo_hi), lo_lo))| {
                    multi_butterfly.apply_2_layers(
                        ((hi_hi, hi_lo), (lo_hi, lo_lo)),
                        ind,
                        twiddles_small,
                        twiddles_large,
                    );
                });
        });
}

/// Applies three layers of a Radix-2 FFT butterfly network making use of parallelization.
///
/// Splits the matrix into blocks of rows and performs in-place butterfly operations
/// on each block. Advantage of doing three layers at once is it reduces the amount of
/// data transferred between threads.
///
/// # Arguments
/// - `mat`: Mutable matrix whose height is a power of two.
/// - `twiddles_small`: Precomputed twiddle factors for the layer with the smallest block size.
/// - `twiddles_med`: Precomputed twiddle factors for the middle layer.
/// - `twiddles_large`: Precomputed twiddle factors for the layer with the largest block size.
/// - `multi_butterfly`: Multi-layer butterfly which applies the three layers in the correct order.
#[inline]
fn dft_layer_par_triple<F: Field, B: Butterfly<F>, M: MultiLayerButterfly<F, B>>(
    mat: &mut RowMajorMatrixViewMut<'_, F>,
    twiddles_small: &[B],
    twiddles_med: &[B],
    twiddles_large: &[B],
    multi_butterfly: M,
    width: usize,
    zero_start_elem: usize,
) {
    debug_assert!(
        mat.height().is_multiple_of(twiddles_small.len()),
        "Matrix height must be divisible by the number of twiddles"
    );
    assert_eq!(twiddles_large.len(), twiddles_med.len() * 2);
    assert_eq!(twiddles_med.len(), twiddles_small.len() * 2);

    // // Estimate the optimal size of the inner chunks so that all data fits in L1 cache.
    // // Note that 8 inner chunks are processed in each parallel thread so we divide by 8.
    // let inner_chunk_size =
    //     (workload_size::<F>().next_power_of_two() / 8).min(eighth_outer_block_size);

    let block_size = twiddles_large.len() * 2 * width;
    mat.values
        .par_chunks_exact_mut(block_size)
        .enumerate()
        .filter(move |(idx, _)| idx * block_size < zero_start_elem)
        .for_each(|(_, block)| {
            let (hi_blocks, lo_blocks) = block.split_at_mut(twiddles_small.len() * width * 4);
            let (hi_hi_blocks, hi_lo_blocks) = hi_blocks.split_at_mut(twiddles_small.len() * width * 2);
            let (lo_hi_blocks, lo_lo_blocks) = lo_blocks.split_at_mut(twiddles_small.len() * width * 2);
            let (hi_hi_hi_blocks, hi_hi_lo_blocks) = hi_hi_blocks.split_at_mut(twiddles_small.len() * width);
            let (hi_lo_hi_blocks, hi_lo_lo_blocks) = hi_lo_blocks.split_at_mut(twiddles_small.len() * width);
            let (lo_hi_hi_blocks, lo_hi_lo_blocks) = lo_hi_blocks.split_at_mut(twiddles_small.len() * width);
            let (lo_lo_hi_blocks, lo_lo_lo_blocks) = lo_lo_blocks.split_at_mut(twiddles_small.len() * width);
            hi_hi_hi_blocks
                .par_chunks_exact_mut(width)
                .zip(hi_hi_lo_blocks.par_chunks_exact_mut(width))
                .zip(hi_lo_hi_blocks.par_chunks_exact_mut(width))
                .zip(hi_lo_lo_blocks.par_chunks_exact_mut(width))
                .zip(lo_hi_hi_blocks.par_chunks_exact_mut(width))
                .zip(lo_hi_lo_blocks.par_chunks_exact_mut(width))
                .zip(lo_lo_hi_blocks.par_chunks_exact_mut(width))
                .zip(lo_lo_lo_blocks.par_chunks_exact_mut(width))
                .enumerate()
                .for_each(
                    |(
                        ind,
                        (((((((hi_hi_hi, hi_hi_lo), hi_lo_hi), hi_lo_lo), lo_hi_hi), lo_hi_lo), lo_lo_hi), lo_lo_lo),
                    )| {
                        multi_butterfly.apply_3_layers(
                            (
                                ((hi_hi_hi, hi_hi_lo), (hi_lo_hi, hi_lo_lo)),
                                ((lo_hi_hi, lo_hi_lo), (lo_lo_hi, lo_lo_lo)),
                            ),
                            ind,
                            twiddles_small,
                            twiddles_med,
                            twiddles_large,
                        );
                    },
                );
        });
}

/// Applies the remaining layers of the Radix-2 FFT butterfly network in parallel.
///
/// This function is used to correct for the fact that the total number of layers
/// may not be a multiple of `LAYERS_PER_GROUP`.
fn dft_layer_par_extra_layers<F: Field, B: Butterfly<F>, M: MultiLayerButterfly<F, B>>(
    mat: &mut RowMajorMatrixViewMut<'_, F>,
    root_table: &[Vec<F>],
    multi_layer: M,
    width: usize,
    zero_start_elem: usize,
) {
    match root_table.len() {
        1 => {
            // Safe as DitButterfly is #[repr(transparent)]
            let fft_layer: &[B] = unsafe { as_base_slice(&root_table[0]) };
            dft_layer_par(mat.values, fft_layer, width, zero_start_elem);
        }
        2 => {
            let twiddles_small: &[B] = unsafe { as_base_slice(&root_table[1]) };
            let twiddles_large: &[B] = unsafe { as_base_slice(&root_table[0]) };
            dft_layer_par_double(
                &mut mat.as_view_mut(),
                twiddles_small,
                twiddles_large,
                multi_layer,
                width,
                zero_start_elem,
            );
        }
        0 => {}
        _ => unreachable!("The number of layers must be 0, 1 or 2"),
    }
}

/// A type representing a decomposition of an FFT block into four sub-blocks.
type DoubleLayerBlockDecomposition<'a, F> = ((&'a mut [F], &'a mut [F]), (&'a mut [F], &'a mut [F]));

/// Performs an FFT layer on the sub-blocks using a single twiddle factor.
#[inline]
fn fft_double_layer_single_twiddle<F: Field, Fly: Butterfly<F>>(
    block: &mut DoubleLayerBlockDecomposition<'_, F>,
    butterfly: Fly,
) {
    butterfly.apply_to_rows(block.0.0, block.0.1);
    butterfly.apply_to_rows(block.1.0, block.1.1);
}

#[inline]
fn fft_double_layer_double_twiddle<F: Field, Fly0: Butterfly<F>, Fly1: Butterfly<F>>(
    block: &mut DoubleLayerBlockDecomposition<'_, F>,
    fly0: Fly0,
    fly1: Fly1,
) {
    fly0.apply_to_rows(block.0.0, block.1.0);
    fly1.apply_to_rows(block.0.1, block.1.1);
}

/// A type representing a decomposition of an FFT block into eight sub-blocks.
type TripleLayerBlockDecomposition<'a, F> = (
    ((&'a mut [F], &'a mut [F]), (&'a mut [F], &'a mut [F])),
    ((&'a mut [F], &'a mut [F]), (&'a mut [F], &'a mut [F])),
);

/// Performs an FFT layer on the sub-blocks using a single twiddle factor.
#[inline]
fn fft_triple_layer_single_twiddle<F: Field, Fly: Butterfly<F>>(
    block: &mut TripleLayerBlockDecomposition<'_, F>,
    butterfly: Fly,
) {
    butterfly.apply_to_rows(block.0.0.0, block.0.0.1);
    butterfly.apply_to_rows(block.0.1.0, block.0.1.1);
    butterfly.apply_to_rows(block.1.0.0, block.1.0.1);
    butterfly.apply_to_rows(block.1.1.0, block.1.1.1);
}

#[inline]
fn fft_triple_layer_double_twiddle<F: Field, Fly0: Butterfly<F>, Fly1: Butterfly<F>>(
    block: &mut TripleLayerBlockDecomposition<'_, F>,
    fly0: Fly0,
    fly1: Fly1,
) {
    fly0.apply_to_rows(block.0.0.0, block.0.1.0);
    fly1.apply_to_rows(block.0.0.1, block.0.1.1);
    fly0.apply_to_rows(block.1.0.0, block.1.1.0);
    fly1.apply_to_rows(block.1.0.1, block.1.1.1);
}

#[inline]
fn fft_triple_layer_quad_twiddle<F: Field, Fly: Butterfly<F>>(
    block: &mut TripleLayerBlockDecomposition<'_, F>,
    fly0: Fly,
    fly1: Fly,
    fly2: Fly,
    fly3: Fly,
) {
    fly0.apply_to_rows(block.0.0.0, block.1.0.0);
    fly1.apply_to_rows(block.0.0.1, block.1.0.1);
    fly2.apply_to_rows(block.0.1.0, block.1.1.0);
    fly3.apply_to_rows(block.0.1.1, block.1.1.1);
}

/// Estimates the optimal workload size for `T` to fit in L1 cache.
#[must_use]
const fn workload_size<T: Sized>() -> usize {
    system_info::L1_CACHE_SIZE / size_of::<T>()
}

/// Estimates the optimal number of rows of a `RowMajorMatrix<T>` to take in each parallel chunk.
///
/// Designed to ensure that `<T> * estimate_num_rows_par() * width` is roughly the size of the L1 cache.
///
/// Assumes that height is a power of two and always outputs a power of two.
#[must_use]
fn estimate_num_rows_in_l1<T: Sized>(height: usize, width: usize) -> usize {
    (workload_size::<T>() / width).next_power_of_two().min(height) // Ensure we don't exceed the height of the matrix.
}

trait MultiLayerButterfly<F: Field, B: Butterfly<F>>: Copy + Send + Sync {
    fn apply_2_layers(
        &self,
        chunk_decomposition: DoubleLayerBlockDecomposition<'_, F>,
        ind: usize,
        twiddles_small: &[B],
        twiddles_large: &[B],
    );

    fn apply_3_layers(
        &self,
        chunk_decomposition: TripleLayerBlockDecomposition<'_, F>,
        ind: usize,
        twiddles_small: &[B],
        twiddles_med: &[B],
        twiddles_large: &[B],
    );
}

#[derive(Debug, Clone, Copy)]
struct MyMultiLayerButterfly;

impl<F: Field> MultiLayerButterfly<F, EvalsButterfly<F>> for MyMultiLayerButterfly {
    #[inline]
    fn apply_2_layers(
        &self,
        mut blk_decomp: DoubleLayerBlockDecomposition<'_, F>,
        ind: usize,
        twiddles_small: &[EvalsButterfly<F>],
        twiddles_large: &[EvalsButterfly<F>],
    ) {
        fft_double_layer_single_twiddle(&mut blk_decomp, twiddles_small[ind]);
        fft_double_layer_double_twiddle(
            &mut blk_decomp,
            twiddles_large[ind],
            twiddles_large[ind + twiddles_small.len()],
        );
    }

    #[inline]
    fn apply_3_layers(
        &self,
        mut blk_decomp: TripleLayerBlockDecomposition<'_, F>,
        ind: usize,
        twiddles_small: &[EvalsButterfly<F>],
        twiddles_med: &[EvalsButterfly<F>],
        twiddles_large: &[EvalsButterfly<F>],
    ) {
        fft_triple_layer_single_twiddle(&mut blk_decomp, twiddles_small[ind]);
        fft_triple_layer_double_twiddle(
            &mut blk_decomp,
            twiddles_med[ind],
            twiddles_med[ind + twiddles_small.len()],
        );
        fft_triple_layer_quad_twiddle(
            &mut blk_decomp,
            twiddles_large[ind],
            twiddles_large[ind + twiddles_small.len()],
            twiddles_large[ind + 2 * twiddles_small.len()],
            twiddles_large[ind + 3 * twiddles_small.len()],
        );
    }
}

pub trait Butterfly<F: Field>: Copy + Send + Sync {
    fn apply<PF: PackedField<Scalar = F>>(&self, x_1: PF, x_2: PF) -> (PF, PF);
    #[inline]
    fn apply_in_place<PF: PackedField<Scalar = F>>(&self, x_1: &mut PF, x_2: &mut PF) {
        (*x_1, *x_2) = self.apply(*x_1, *x_2);
    }
    #[inline]
    fn apply_to_rows(&self, row_1: &mut [F], row_2: &mut [F]) {
        let (shorts_1, suffix_1) = F::Packing::pack_slice_with_suffix_mut(row_1);
        let (shorts_2, suffix_2) = F::Packing::pack_slice_with_suffix_mut(row_2);
        debug_assert_eq!(shorts_1.len(), shorts_2.len());
        debug_assert_eq!(suffix_1.len(), suffix_2.len());
        for (x_1, x_2) in shorts_1.iter_mut().zip(shorts_2) {
            self.apply_in_place(x_1, x_2);
        }
        for (x_1, x_2) in suffix_1.iter_mut().zip(suffix_2) {
            self.apply_in_place(x_1, x_2);
        }
    }
}

/// Out-of-place SIMD butterfly: reads two input rows, writes the butterfly results to two
/// separate destination rows. Used by `fused_prepare_and_dft` to duplicate each source row
/// into its butterfly outputs in a single pass (one read, one write per destination cell).
#[inline]
fn butterfly_out_of_place<F: Field, B: Butterfly<F>>(
    butterfly: B,
    in_1: &[F],
    in_2: &[F],
    out_1: &mut [F],
    out_2: &mut [F],
) {
    let width = F::Packing::WIDTH;
    let n_packed = in_1.len() / width;
    // SAFETY: `PackedField` is `#[repr(transparent)]` over `[F::Scalar; WIDTH]`, and the
    // prefix of length `n_packed * width` fits an exact number of SIMD lanes.
    let packed_in_1 = unsafe { std::slice::from_raw_parts(in_1.as_ptr().cast::<F::Packing>(), n_packed) };
    let packed_in_2 = unsafe { std::slice::from_raw_parts(in_2.as_ptr().cast::<F::Packing>(), n_packed) };
    let packed_out_1 = unsafe { std::slice::from_raw_parts_mut(out_1.as_mut_ptr().cast::<F::Packing>(), n_packed) };
    let packed_out_2 = unsafe { std::slice::from_raw_parts_mut(out_2.as_mut_ptr().cast::<F::Packing>(), n_packed) };
    for (((&i_1, &i_2), o_1), o_2) in packed_in_1.iter().zip(packed_in_2).zip(packed_out_1).zip(packed_out_2) {
        (*o_1, *o_2) = butterfly.apply(i_1, i_2);
    }
    for i in n_packed * width..in_1.len() {
        (out_1[i], out_2[i]) = butterfly.apply(in_1[i], in_2[i]);
    }
}

/// Butterfly with no twiddle factor (`twiddle = 1`).
#[derive(Copy, Clone, Debug)]
pub struct TwiddleFreeEvalsButterfly;

impl<F: Field> Butterfly<F> for TwiddleFreeEvalsButterfly {
    #[inline]
    fn apply<PF: PackedField<Scalar = F>>(&self, x_1: PF, x_2: PF) -> (PF, PF) {
        (x_2, x_1.double() - x_2)
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct EvalsButterfly<F>(pub F);

impl<F: Field> Butterfly<F> for EvalsButterfly<F> {
    #[inline]
    fn apply<PF: PackedField<Scalar = F>>(&self, x_1: PF, x_2: PF) -> (PF, PF) {
        // Use fused_sub_mul to skip intermediate modular reduction on (x_2 - x_1)
        let x_2_twiddle = x_2.fused_sub_mul(x_1, self.0);
        (x_1 + x_2_twiddle, x_1 - x_2_twiddle)
    }
}

#[cfg(test)]
mod tests {
    use field::{PrimeCharacteristicRing, TwoAdicField};
    use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
    use poly::*;
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    use crate::*;

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_eval_dft() {
        for n_vars in 1..=20 {
            println!("n_vars = {}", n_vars);
            let mut rng = StdRng::seed_from_u64(0);

            let evals = (0..(1 << n_vars)).map(|_| rng.random()).collect::<Vec<EF>>();

            let dft = EvalsDft::<F>::default();
            let evals_dft = dft.dft_algebra_batch_by_evals(RowMajorMatrix::new(evals.clone(), 1));
            let fft_values = evals_dft.values;
            for _ in 0..10 {
                let i = rng.random_range(0..(1 << n_vars));
                let point = MultilinearPoint::expand_from_univariate(
                    EF::from(F::two_adic_generator(n_vars)).exp_u64(i as u64),
                    n_vars,
                );
                if fft_values[i] != evals.evaluate(&point) {
                    panic!();
                }
            }
        }
    }
}
