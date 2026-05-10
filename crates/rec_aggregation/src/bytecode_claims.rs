use backend::*;
use lean_vm::*;
use utils::{build_prover_state, get_poseidon16, poseidon_compress_slice, poseidon16_compress_pair};

use crate::compilation::BYTECODE_CLAIM_OFFSET;
use crate::{InnerVerified, get_aggregation_bytecode};

pub(crate) struct ReducedBytecodeClaims {
    pub final_claim: Evaluation<EF>,
    pub sumcheck_transcript: Vec<F>,
}

impl ReducedBytecodeClaims {
    pub fn final_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.final_claim)
    }
}

pub(crate) fn flatten_bytecode_claim(claim: &Evaluation<EF>) -> Vec<F> {
    let mut ef_claim: Vec<EF> = claim.point.0.clone();
    ef_claim.push(claim.value);
    flatten_scalars_to_base::<F, EF>(&ef_claim)
}

pub(crate) fn compute_bytecode_value_at(point: &MultilinearPoint<EF>) -> EF {
    let bytecode = get_aggregation_bytecode();
    if point.iter().all(|x| x.is_zero()) {
        // fast path for multi-signatures coming from 100% raw XMSS (no recursion):
        EF::from(bytecode.instructions_multilinear[0])
    } else {
        bytecode.instructions_multilinear.evaluate(point)
    }
}

pub(crate) fn reduce_bytecode_claims(verified: &[InnerVerified]) -> ReducedBytecodeClaims {
    let bytecode = get_aggregation_bytecode();

    if verified.is_empty() {
        let zero_point = MultilinearPoint(vec![EF::ZERO; bytecode.cumulated_n_vars()]);
        let zero_value = compute_bytecode_value_at(&zero_point);
        return ReducedBytecodeClaims {
            final_claim: Evaluation::new(zero_point, zero_value),
            sumcheck_transcript: vec![],
        };
    }

    let mut claims = Vec::with_capacity(2 * verified.len());
    for v in verified {
        claims.push(extract_bytecode_claim_from_input_data(
            &v.input_data[BYTECODE_CLAIM_OFFSET..],
            bytecode.cumulated_n_vars(),
        ));
        claims.push(v.bytecode_evaluation.clone());
    }
    let claims_hash = hash_bytecode_claims(&claims);

    let mut reduction_prover = build_prover_state();
    reduction_prover.add_base_scalars(&claims_hash);
    let alpha: EF = reduction_prover.sample();

    let n_claims = claims.len();
    let alpha_powers: Vec<EF> = alpha.powers().take(n_claims).collect();

    let weights_packed = claims
        .par_iter()
        .zip(&alpha_powers)
        .map(|(eval, &alpha_i)| eval_eq_packed_scaled(&eval.point.0, alpha_i))
        .reduce_with(|mut acc, eq_i| {
            acc.par_iter_mut().zip(&eq_i).for_each(|(w, e)| *w += *e);
            acc
        })
        .unwrap();

    let claimed_sum: EF = dot_product(claims.iter().map(|c| c.value), alpha_powers.iter().copied());

    let (reduced_point, _, bytecode_folded, _) = run_product_sumcheck(
        &MleRef::BasePacked(FPacking::<F>::pack_slice(&bytecode.instructions_multilinear)),
        &MleRef::ExtensionPacked(&weights_packed),
        &mut reduction_prover,
        claimed_sum,
        bytecode.cumulated_n_vars(),
        0,
    );

    let reduced_value = bytecode_folded.as_constant();
    let bytecode_claim_output = flatten_bytecode_claim(&Evaluation::new(reduced_point.clone(), reduced_value));
    assert_eq!(bytecode_claim_output.len(), bytecode.bytecode_claim_size());

    let sumcheck_transcript = {
        let mut vs = VerifierState::<EF, _>::new(reduction_prover.into_proof(), get_poseidon16().clone()).unwrap();
        vs.next_base_scalars_vec(claims_hash.len()).unwrap();
        let _: EF = vs.sample();
        sumcheck_verify(&mut vs, bytecode.cumulated_n_vars(), 2, claimed_sum, None).unwrap();
        vs.into_raw_proof().transcript
    };
    assert_eq!(
        sumcheck_transcript.len(),
        bytecode_reduction_sumcheck_proof_size(bytecode.cumulated_n_vars()),
        "bytecode claim-reduction sumcheck transcript length disagrees with the formula",
    );

    ReducedBytecodeClaims {
        final_claim: Evaluation::new(reduced_point, reduced_value),
        sumcheck_transcript,
    }
}

pub(crate) fn extract_bytecode_claim_from_input_data(
    public_input: &[F],
    bytecode_point_n_vars: usize,
) -> Evaluation<EF> {
    let claim_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let packed = pack_scalars_to_extension(&public_input[..claim_size]);
    let point = MultilinearPoint(packed[..bytecode_point_n_vars].to_vec());
    let value = packed[bytecode_point_n_vars];
    Evaluation::new(point, value)
}

pub(crate) fn hash_bytecode_claims(claims: &[Evaluation<EF>]) -> [F; DIGEST_LEN] {
    let mut running_hash = [F::ZERO; DIGEST_LEN];
    for eval in claims {
        let mut ef_data: Vec<EF> = eval.point.0.clone();
        ef_data.push(eval.value);
        let mut data = flatten_scalars_to_base::<F, EF>(&ef_data);
        data.resize(data.len().next_multiple_of(DIGEST_LEN), F::ZERO);

        let claim_hash = poseidon_compress_slice(&data, false);
        running_hash = poseidon16_compress_pair(&running_hash, &claim_hash);
    }
    running_hash
}

pub(crate) fn bytecode_reduction_sumcheck_proof_size(bytecode_point_n_vars: usize) -> usize {
    let per_round = (3 * DIMENSION).next_multiple_of(DIGEST_LEN);
    DIGEST_LEN + bytecode_point_n_vars * per_round
}
