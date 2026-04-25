// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use fiat_shamir::{ChallengeSampler, FSProver};
use field::Field;
use field::{ExtensionField, TwoAdicField};
use poly::*;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

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
    reorder_and_dft_with_prefix_len(evals, folding_factor, log_inv_rate, dft_n_cols, 1 << evals.n_vars())
}

pub(crate) fn reorder_and_dft_with_prefix_len<EF: ExtensionField<PF<EF>>>(
    evals: &MleRef<'_, EF>,
    folding_factor: usize,
    log_inv_rate: usize,
    dft_n_cols: usize,
    non_zero_prefix_len: usize,
) -> DftOutput<EF>
where
    PF<EF>: TwoAdicField,
{
    let dft = global_dft::<PF<EF>>();
    let dft_size = (1 << (evals.n_vars() + log_inv_rate)) >> folding_factor;
    if dft.max_n_twiddles() < dft_size {
        tracing::warn!("Twiddles have not been precomputed, for size = {}", dft_size);
    }

    // Source rows in the pre-duplication base-field matrix. The DFT fuses prepare + layer
    // `log_inv_rate` into one pass that reads this compact source directly and writes the
    // size-`dft_size` post-layer output.
    let n_blocks = 1usize << folding_factor;
    let source_rows = evals.unpacked_len() / n_blocks;
    let non_zero_prefix_rows = non_zero_prefix_len.div_ceil(n_blocks).min(source_rows);

    // SAFETY: `MleRef::Base` owns `[PF<EF>]` and `MleRef::Extension` owns `[EF]`. Both are
    // `#[repr(transparent)]` over their base field coordinates; `as_base_slice` is the
    // canonical way to reinterpret an extension-field slice as a base-field slice. The
    // resulting width in base-field units is `dft_n_cols * DIMENSION`.
    match evals {
        MleRef::Base(src) => {
            let base_w = dft_n_cols;
            DftOutput::Base(dft.fused_prepare_and_dft(src, base_w, log_inv_rate, non_zero_prefix_rows))
        }
        MleRef::Extension(src) => {
            let base_w = dft_n_cols * <EF as field::BasedVectorSpace<PF<EF>>>::DIMENSION;
            let base_src: &[PF<EF>] = unsafe { utils::as_base_slice::<PF<EF>, EF>(src) };
            let base_result = dft.fused_prepare_and_dft(base_src, base_w, log_inv_rate, non_zero_prefix_rows);
            DftOutput::Extension(RowMajorMatrix::new(
                <EF as field::BasedVectorSpace<PF<EF>>>::reconstitute_from_base(base_result.values),
                dft_n_cols,
            ))
        }
        _ => unreachable!(),
    }
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
