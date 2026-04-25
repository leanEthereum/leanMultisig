use std::borrow::Cow;

use backend::*;
use tracing::instrument;

use crate::{
    N_VARS_TO_SEND_GKR_COEFFS,
    quotient_gkr::{
        layers::LayerStorage,
        sumcheck_utils::{
            even_odd_split, quotient_sumcheck_prove_packed_br_base, run_phase1_sumcheck, run_phase2_sumcheck,
        },
    },
};

mod layers;
mod sumcheck_utils;

// GKR for Σ nᵢ/dᵢ
// Folding = 'right to left' (LSB first)  (x_0 = MSB, x_{L-1} = LSB)
// Phase 1 keeps data chunk-bit-reversed at chunk_log  and
// packed — a natural-LSB fold becomes a fold at the chunk-MSB, which stays
// above SIMD-lane while chunk_log > w (w = log(SIMD lane)). Once chunk_log
// drops to w we unpack and continue naturally.
//
// In this file, "br" means "bit reverse"

pub const ENDIANNESS_PIVOT_GKR: usize = 12;

#[instrument(skip_all, name = "prove GKR")]
pub fn prove_gkr_quotient<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    nums_br: &'a [PFPacking<EF>], // already bit-reversed at `pivot`, ACTIVE prefix only (i.e. length may not be a power of 2)
    dens_br: &'a [EFPacking<EF>], // same as above
    pivot: usize,
) -> (EF, MultilinearPoint<EF>) {
    let w = packing_log_width::<EF>();
    let total_n_vars = log2_ceil_usize(nums_br.len()) + w;
    assert!(total_n_vars > N_VARS_TO_SEND_GKR_COEFFS);
    assert!(pivot > w && total_n_vars > w);
    assert_eq!(nums_br.len(), dens_br.len());

    let initial = LayerStorage::Initial {
        nums: Cow::Borrowed(nums_br),
        dens: Cow::Borrowed(dens_br),
        chunk_log: pivot,
    };

    let mut layers: Vec<LayerStorage<'a, EF>> = vec![initial];

    let mut current_n_vars = total_n_vars;
    while current_n_vars > N_VARS_TO_SEND_GKR_COEFFS {
        let last_layer = layers.last().unwrap();
        if last_layer.chunk_log() == w {
            let last_layer_unreversed = last_layer.convert_to_natural();
            layers.push(last_layer_unreversed.sum_quotients_2_by_2());
        } else {
            layers.push(last_layer.sum_quotients_2_by_2());
        }

        current_n_vars -= 1;
    }

    let (top_nums, top_dens) = layers.pop().unwrap().materialise_in_full();
    prover_state.add_extension_scalars(&top_nums);
    prover_state.add_extension_scalars(&top_dens);
    let quotient = compute_quotient(&top_nums, &top_dens);

    let mut point = MultilinearPoint(prover_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
    let mut claim_num = top_nums.evaluate(&point);
    let mut claim_den = top_dens.evaluate(&point);

    for layer in layers.iter().rev() {
        (point, claim_num, claim_den) = prove_gkr_layer(prover_state, layer, &point, claim_num, claim_den);
    }

    (quotient, point)
}

fn prove_gkr_layer<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    layer: &LayerStorage<'_, EF>,
    claim_point: &MultilinearPoint<EF>, // K coords, natural order
    claim_num: EF,
    claim_den: EF,
) -> (MultilinearPoint<EF>, EF, EF) {
    let alpha = prover_state.sample();
    let expected_sum = claim_num + alpha * claim_den;

    let (mut q_natural, inner_evals) = match layer {
        LayerStorage::Initial { nums, dens, chunk_log } => quotient_sumcheck_prove_packed_br_base(
            prover_state,
            nums.as_ref(),
            dens.as_ref(),
            *chunk_log,
            &claim_point.0,
            alpha,
            expected_sum,
        ),
        LayerStorage::PackedBr { nums, dens, chunk_log } => run_phase1_sumcheck(
            prover_state,
            nums.as_ref().into(),
            dens.as_ref().into(),
            *chunk_log,
            claim_point.0.to_vec(),
            vec![],
            alpha,
            expected_sum,
            EF::ONE,
            None,
            None,
        ),
        LayerStorage::Natural { nums, dens } => {
            let (num_l, num_r) = even_odd_split(nums);
            let (den_l, den_r) = even_odd_split(dens);
            run_phase2_sumcheck(
                prover_state,
                num_l,
                num_r,
                den_l,
                den_r,
                claim_point.0.to_vec(),
                vec![],
                alpha,
                expected_sum,
                EF::ONE,
            )
        }
    };

    prover_state.add_extension_scalars(&inner_evals);
    let beta = prover_state.sample();
    let [nl_q, nr_q, dl_q, dr_q] = inner_evals;
    let one_minus_beta = EF::ONE - beta;
    let next_num = one_minus_beta * nl_q + beta * nr_q;
    let next_den = one_minus_beta * dl_q + beta * dr_q;

    q_natural.push(beta);
    (MultilinearPoint(q_natural), next_num, next_den)
}

fn compute_quotient<EF: ExtensionField<PF<EF>>>(numerators: &[EF], denominators: &[EF]) -> EF {
    numerators.iter().zip(denominators).map(|(&n, &d)| n / d).sum()
}

pub fn verify_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
) -> Result<(EF, MultilinearPoint<EF>, EF, EF), ProofError> {
    assert!(n_vars > N_VARS_TO_SEND_GKR_COEFFS);
    let send_len = 1 << N_VARS_TO_SEND_GKR_COEFFS;
    let last_nums = verifier_state.next_extension_scalars_vec(send_len)?;
    let last_dens = verifier_state.next_extension_scalars_vec(send_len)?;
    let quotient: EF = compute_quotient(&last_nums, &last_dens);
    let mut point = MultilinearPoint(verifier_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
    let mut claims_num = last_nums.evaluate(&point);
    let mut claims_den = last_dens.evaluate(&point);
    for i in N_VARS_TO_SEND_GKR_COEFFS..n_vars {
        (point, claims_num, claims_den) = verify_gkr_quotient_step(verifier_state, i, &point, claims_num, claims_den)?;
    }
    Ok((quotient, point, claims_num, claims_den))
}

fn verify_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
    point: &MultilinearPoint<EF>,
    claims_num: EF,
    claims_den: EF,
) -> Result<(MultilinearPoint<EF>, EF, EF), ProofError> {
    let alpha = verifier_state.sample();
    let expected_sum = claims_num + alpha * claims_den;
    let eq_alphas_rev: Vec<EF> = point.0.iter().rev().copied().collect();
    let mut postponed = sumcheck_verify(verifier_state, n_vars, 3, expected_sum, Some(&eq_alphas_rev))?;
    postponed.point.0.reverse();
    let inner_evals = verifier_state.next_extension_scalars_vec(4)?;
    let constraints_eval =
        alpha * inner_evals[2] * inner_evals[3] + (inner_evals[0] * inner_evals[3] + inner_evals[1] * inner_evals[2]);
    if postponed.value != point.eq_poly_outside(&postponed.point) * constraints_eval {
        return Err(ProofError::InvalidProof);
    }
    let beta = verifier_state.sample();
    let next_claims_numerators = (&inner_evals[..2]).evaluate(&MultilinearPoint(vec![beta]));
    let next_claims_denominators = (&inner_evals[2..]).evaluate(&MultilinearPoint(vec![beta]));
    let mut next_point = postponed.point.clone();
    next_point.0.push(beta);
    Ok((next_point, next_claims_numerators, next_claims_denominators))
}
