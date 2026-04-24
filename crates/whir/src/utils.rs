// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use fiat_shamir::{ChallengeSampler, FSProver};
use field::Field;
use field::{ExtensionField, TwoAdicField};
use poly::*;
use rayon::prelude::*;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};
use tracing::instrument;

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
    let prepared_evals = prepare_evals_for_fft(evals, folding_factor, log_inv_rate);
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
) -> DftInput<EF> {
    match evals {
        MleRef::Base(evals) => DftInput::Base(prepare_evals_for_fft_helper(evals, folding_factor, log_inv_rate)),
        MleRef::Extension(evals) => {
            DftInput::Extension(prepare_evals_for_fft_helper(evals, folding_factor, log_inv_rate))
        }
        _ => unreachable!(),
    }
}

#[instrument(skip_all)]
fn prepare_evals_for_fft_helper<A: Copy + Send + Sync>(
    evals: &[A],
    folding_factor: usize,
    log_inv_rate: usize,
) -> Vec<A> {
    let n_blocks = 1 << folding_factor;
    assert!(evals.len().is_multiple_of(n_blocks));
    let out_len = evals.len() << log_inv_rate;

    let mut out = unsafe { uninitialized_vec::<A>(out_len) };
    out.par_chunks_mut(n_blocks).enumerate().for_each(|(row, dst)| {
        let src = (row >> log_inv_rate) << folding_factor;
        dst.copy_from_slice(&evals[src..src + n_blocks]);
    });
    out
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
