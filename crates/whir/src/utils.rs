// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use fiat_shamir::{ChallengeSampler, FSProver};
use field::BasedVectorSpace;
use field::Field;
use field::PackedValue;
use field::{ExtensionField, TwoAdicField};
use poly::*;
use rayon::prelude::*;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};
use tracing::instrument;
use utils::log2_strict_usize;

use crate::EvalsDft;
use crate::RowMajorMatrix;

pub(crate) fn get_challenge_stir_queries<F: Field, Chal: ChallengeSampler<F>>(
    folded_domain_size: usize,
    num_queries: usize,
    challenger: &mut Chal,
) -> Vec<usize> {
    challenger.sample_in_range(folded_domain_size.ilog2() as usize, num_queries)
}

/// A utility function to sample Out-of-Domain (OOD) points and evaluate them.
///
/// This should be used on the prover side.
pub(crate) fn sample_ood_points<EF: ExtensionField<PF<EF>>, E>(
    prover_state: &mut impl FSProver<EF>,
    num_samples: usize,
    num_variables: usize,
    evaluate_fn: E,
) -> (Vec<EF>, Vec<EF>)
where
    E: Fn(&MultilinearPoint<EF>) -> EF,
{
    let mut ood_points = Vec::new();
    let mut ood_answers = Vec::new();

    if num_samples > 0 {
        // Generate OOD points from ProverState randomness
        ood_points = prover_state.sample_vec(num_samples);

        // Evaluate the function at each OOD point
        ood_answers.extend(
            ood_points
                .iter()
                .map(|ood_point| evaluate_fn(&MultilinearPoint::expand_from_univariate(*ood_point, num_variables))),
        );

        prover_state.add_extension_scalars(&ood_answers);
    }

    (ood_points, ood_answers)
}

pub(crate) enum DftInput<EF: Field> {
    Base(Vec<PF<EF>>),
    Extension(Vec<EF>),
}

pub(crate) enum DftOutput<EF: Field> {
    Base(RowMajorMatrix<PF<EF>>),
    Extension(RowMajorMatrix<EF>),
}

pub(crate) fn reorder_and_dft<EF: ExtensionField<PF<EF>>>(
    evals: &MleRef<'_, EF>,
    folding_factor: usize,
    log_inv_rate: usize,
    dft_n_cols: usize,
) -> DftOutput<EF>
where
    PF<EF>: TwoAdicField,
{
    let prepared_evals = prepare_evals_for_fft(evals, folding_factor, log_inv_rate, dft_n_cols);
    let dft = global_dft::<PF<EF>>();
    let dft_size = (1 << (evals.n_vars() + log_inv_rate)) >> folding_factor;
    if dft.max_n_twiddles() < dft_size {
        tracing::warn!("Twiddles have not been precomputed, for size = {}", dft_size);
    }
    match prepared_evals {
        DftInput::Base(evals) => {
            DftOutput::Base(dft.dft_algebra_batch_by_evals(RowMajorMatrix::new(evals, dft_n_cols)))
        }
        DftInput::Extension(evals) => {
            DftOutput::Extension(dft.dft_algebra_batch_by_evals(RowMajorMatrix::new(evals, dft_n_cols)))
        }
    }
}

fn prepare_evals_for_fft<EF: ExtensionField<PF<EF>>>(
    evals: &MleRef<'_, EF>,
    folding_factor: usize,
    log_inv_rate: usize,
    dft_n_cols: usize,
) -> DftInput<EF> {
    match evals {
        MleRef::Base(evals) => DftInput::Base(prepare_evals_for_fft_unpacked(
            evals,
            folding_factor,
            log_inv_rate,
            dft_n_cols,
        )),
        MleRef::BasePacked(evals) => DftInput::Base(prepare_evals_for_fft_unpacked(
            PFPacking::<EF>::unpack_slice(evals),
            folding_factor,
            log_inv_rate,
            dft_n_cols,
        )),
        MleRef::Extension(evals) => DftInput::Extension(prepare_evals_for_fft_unpacked(
            evals,
            folding_factor,
            log_inv_rate,
            dft_n_cols,
        )),
        MleRef::ExtensionPacked(evals) => DftInput::Extension(prepare_evals_for_fft_packed_extension(
            evals,
            folding_factor,
            log_inv_rate,
        )),
    }
}

#[instrument(skip_all)]
fn prepare_evals_for_fft_unpacked<A: Copy + Send + Sync + 'static>(
    evals: &[A],
    folding_factor: usize,
    log_inv_rate: usize,
    dft_n_cols: usize,
) -> Vec<A> {
    assert!(evals.len().is_multiple_of(1 << folding_factor));
    let n_blocks = 1 << folding_factor;
    let full_len = evals.len() << log_inv_rate;
    let block_size = full_len / n_blocks;
    let log_block_size = log2_strict_usize(block_size);
    let out_len = block_size * dft_n_cols;

    // GPU path: this is purely a scatter — gather pattern (no compute), so it's
    // entirely memory-bandwidth bound. On unified-memory Apple Silicon the GPU
    // achieves close to peak DRAM bandwidth here while the CPU version is gated
    // by gather-from-non-contiguous-indices and rayon `.collect()` overhead.
    //
    // Only activated when:
    //   - the GPU runtime is enabled,
    //   - the element type is `KoalaBear` (elem_size = 1) or its quintic extension
    //     (elem_size = 5) — these are the only types this prove pipeline ever
    //     instantiates `A` with — , and
    //   - the output is large enough to amortize the GPU dispatch (~1 MiB).
    if gpu_poseidon::gpu_enabled() && gpu_poseidon::metal_available() && out_len * std::mem::size_of::<A>() >= 1 << 20 {
        let kb_id = TypeId::of::<koala_bear::KoalaBear>();
        let kbe_id = TypeId::of::<koala_bear::QuinticExtensionFieldKB>();
        let a_id = TypeId::of::<A>();
        let elem_size: Option<usize> = if a_id == kb_id {
            Some(1)
        } else if a_id == kbe_id {
            Some(5)
        } else {
            None
        };
        if let Some(elem_size) = elem_size {
            // Allocate output (page-aligned via zk-alloc) and let the GPU kernel
            // fill it via no_copy. Cast both sides to `u32` slices — `KoalaBear` is
            // `#[repr(transparent)]` over a Montgomery-form `u32`; the quintic
            // extension is `#[repr(transparent)]` over `[KoalaBear; 5]`.
            // Avoid touching every element on the CPU (~25 ms wasted just zero-ing
            // for the big FFT). The GPU kernel writes every byte before we read it
            // back; we use `MaybeUninit` to keep the allocation cheap and skip
            // initialization.
            let mut out: Vec<std::mem::MaybeUninit<A>> = Vec::with_capacity(out_len);
            // SAFETY: we are about to overwrite the entire buffer via the GPU
            // kernel; the caller never observes the uninitialized region.
            unsafe { out.set_len(out_len) };
            let mut out: Vec<A> = unsafe { std::mem::transmute::<Vec<std::mem::MaybeUninit<A>>, Vec<A>>(out) };
            let evals_u32: &[u32] =
                unsafe { std::slice::from_raw_parts(evals.as_ptr() as *const u32, evals.len() * elem_size) };
            let out_u32: &mut [u32] =
                unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr() as *mut u32, out_len * elem_size) };
            tracing::info_span!("prepare_evals_for_fft_unpacked (GPU)").in_scope(|| {
                gpu_poseidon::prepare_evals_for_fft_gpu(
                    evals_u32,
                    out_u32,
                    dft_n_cols,
                    log_block_size,
                    log_inv_rate,
                    elem_size,
                );
            });
            return out;
        }
    }

    (0..out_len)
        .into_par_iter()
        .map(|i| {
            let block_index = i % dft_n_cols;
            let offset_in_block = i / dft_n_cols;
            let src_index = ((block_index << log_block_size) + offset_in_block) >> log_inv_rate;
            unsafe { *evals.get_unchecked(src_index) }
        })
        .collect()
}

#[instrument(skip_all)]
fn prepare_evals_for_fft_packed_extension<EF: ExtensionField<PF<EF>>>(
    evals: &[EFPacking<EF>],
    folding_factor: usize,
    log_inv_rate: usize,
) -> Vec<EF> {
    let log_packing = packing_log_width::<EF>();
    assert!((evals.len() << log_packing).is_multiple_of(1 << folding_factor));
    let n_blocks = 1 << folding_factor;
    let full_len = evals.len() << (log_inv_rate + log_packing);
    let block_size = full_len / n_blocks;
    let log_block_size = log2_strict_usize(block_size);
    let n_blocks_mask = n_blocks - 1;
    let packing_mask = (1 << log_packing) - 1;

    (0..full_len)
        .into_par_iter()
        .map(|i| {
            let block_index = i & n_blocks_mask;
            let offset_in_block = i >> folding_factor;
            let src_index = ((block_index << log_block_size) + offset_in_block) >> log_inv_rate;
            let packed_src_index = src_index >> log_packing;
            let offset_in_packing = src_index & packing_mask;
            let packed = unsafe { evals.get_unchecked(packed_src_index) };
            let unpacked: &[PFPacking<EF>] = packed.as_basis_coefficients_slice();
            EF::from_basis_coefficients_fn(|i| unsafe {
                let u: &PFPacking<EF> = unpacked.get_unchecked(i);
                *u.as_slice().get_unchecked(offset_in_packing)
            })
        })
        .collect()
}

type CacheKey = TypeId;
type CacheValue = Arc<OnceLock<Arc<dyn Any + Send + Sync>>>;
type SelectorsCache = Mutex<HashMap<CacheKey, CacheValue>>;

static DFT_CACHE: OnceLock<SelectorsCache> = OnceLock::new();

pub(crate) fn global_dft<F: Field>() -> Arc<EvalsDft<F>> {
    let key = TypeId::of::<F>();
    let mut map = DFT_CACHE.get_or_init(|| Mutex::new(HashMap::new())).lock().unwrap();
    let cell = map.entry(key).or_insert_with(|| Arc::new(OnceLock::new())).clone();
    cell.get_or_init(|| Arc::new(EvalsDft::<F>::default()) as Arc<dyn Any + Send + Sync>)
        .clone()
        .downcast::<EvalsDft<F>>()
        .unwrap()
}

pub fn precompute_dft_twiddles<F: TwoAdicField>(n: usize) {
    global_dft::<F>().update_twiddles(n);
}
