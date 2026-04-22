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

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::quotient_gkr::layers::bit_reverse_chunks;

    use super::*;
    use rand::{RngExt, SeedableRng, rngs::StdRng};
    use utils::{build_prover_state, build_verifier_state, init_tracing};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(nums: &[F], den: &[EF]) -> EF {
        nums.par_iter().zip(den).map(|(&n, &d)| EF::from(n) / d).sum()
    }

    fn bit_reverse_chunks_and_pack_ext<EF: ExtensionField<PF<EF>>>(v: &[EF], chunk_log: usize) -> Vec<EFPacking<EF>> {
        pack_extension(&bit_reverse_chunks(v, chunk_log))
    }

    fn bit_reverse_chunks_and_pack_base<EF: ExtensionField<PF<EF>>>(
        v: &[PF<EF>],
        chunk_log: usize,
    ) -> Vec<PFPacking<EF>> {
        let width: usize = packing_width::<EF>();
        let mut res = unsafe { uninitialized_vec::<PFPacking<EF>>(v.len() / width) };
        let unpacked = PFPacking::<EF>::unpack_slice_mut(&mut res);
        let out = bit_reverse_chunks(v, chunk_log);
        unpacked.copy_from_slice(&out);
        res
    }

    fn run_gkr_quotient(log_n: usize, active_chunks_frac: (usize, usize)) {
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);
        let pivot = ENDIANNESS_PIVOT_GKR.min(log_n);
        let total_chunks = 1usize << (log_n - pivot);
        let active_chunks = ((total_chunks * active_chunks_frac.0) / active_chunks_frac.1)
            .max(total_chunks / 2 + 1)
            .min(total_chunks);
        assert!(active_chunks <= total_chunks);
        let active_len = active_chunks << pivot;

        let mut numerators_raw: Vec<F> = (0..active_len).map(|_| rng.random()).collect();
        numerators_raw.extend(std::iter::repeat_n(F::ZERO, n - active_len));

        let c: EF = rng.random();
        let mut denominators_raw: Vec<EF> = (0..active_len)
            .map(|_| c - PF::<EF>::from_usize(rng.random_range(..n)))
            .collect();
        denominators_raw.extend(std::iter::repeat_n(EF::ONE, n - active_len));

        let real_quotient = sum_all_quotients(&numerators_raw, &denominators_raw);
        let mut prover_state = build_prover_state();

        // Keep natural-layout MLEs to check claims at `claim_point`.
        let numerators_nat = MleOwned::BasePacked(pack_extension(&numerators_raw));
        let denominators_nat = MleOwned::ExtensionPacked(pack_extension(&denominators_raw));

        // Pre-BR the inputs for `prove_gkr_quotient_br`.
        let nums_br = bit_reverse_chunks_and_pack_base::<EF>(&numerators_raw, pivot);
        let dens_br = bit_reverse_chunks_and_pack_ext::<EF>(&denominators_raw, pivot);

        // GKR only needs the active prefix — the trailing (0, 1) chunks are
        // handled symbolically.
        let w = packing_log_width::<EF>();
        let active_packed = active_chunks << (pivot - w);

        let time = Instant::now();
        let (quotient_prover, claim_point_prover) = prove_gkr_quotient::<EF>(
            &mut prover_state,
            &nums_br[..active_packed],
            &dens_br[..active_packed],
            pivot,
        );
        println!("Proving time: {:.3}s", time.elapsed().as_secs_f64());

        let mut verifier_state = build_verifier_state(prover_state).unwrap();
        let verifier_statements = verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
        let (retrieved_quotient, claim_point, claim_num, claim_den) = verifier_statements;
        assert_eq!(claim_point_prover, claim_point);
        assert_eq!(quotient_prover, retrieved_quotient);
        assert_eq!(retrieved_quotient, real_quotient);
        assert_eq!(numerators_nat.evaluate(&claim_point), claim_num);
        assert_eq!(denominators_nat.evaluate(&claim_point), claim_den);
    }

    #[test]
    #[ignore]
    fn bench_gkr_quotient() {
        // init_tracing();
        println!("100% active:");
        run_gkr_quotient(25, (1, 1));
        println!("75% active:");
        run_gkr_quotient(25, (3, 4));
        println!("51% active:");
        run_gkr_quotient(25, (51, 100));
    }

    #[test]
    fn test_gkr_quotient_with_padding() {
        init_tracing();
        for log_n in [11, 13, 15] {
            for frac in [(51, 100), (2, 3), (3, 4), (7, 8), (1, 1)] {
                run_gkr_quotient(log_n, frac);
            }
        }
    }
}
