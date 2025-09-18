/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

with custom GKR

*/

use p3_field::PrimeCharacteristicRing;
use p3_field::{ExtensionField, PrimeField64};
use rayon::prelude::*;
use sumcheck::MleGroupRef;
use sumcheck::ProductComputation;
use tracing::instrument;
use utils::left_ref;
use utils::packing_log_width;
use utils::packing_width;
use utils::right_ref;
use utils::unpack_extension;
use utils::{EFPacking, Evaluation, FSProver, FSVerifier, PF};
use whir_p3::fiat_shamir::FSChallenger;
use whir_p3::fiat_shamir::errors::ProofError;
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::MultilinearPoint;

/*
Custom GKR to compute a product.

A: [a0, a1, a2, a3, a4, a5, a6, a7]
A': [a0*a4, a1*a5, a2*a6, a3*a7]
...

*/

#[instrument(skip_all)]
pub fn prove_gkr_product<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    final_layer: Vec<EFPacking<EF>>,
) -> (EF, Evaluation<EF>)
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let n = (final_layer.len() * packing_width::<EF>()).ilog2() as usize;
    let mut layers_packed = Vec::new();
    let mut layers_not_packed = Vec::new();
    let last_packed = n
        .checked_sub(6 + packing_log_width::<EF>())
        .expect("TODO small GKR, no packing");
    layers_packed.push(final_layer);
    for i in 0..last_packed {
        layers_packed.push(product_2_by_2(&layers_packed[i]));
    }
    layers_not_packed.push(product_2_by_2(&unpack_extension(
        &layers_packed[last_packed],
    )));
    for i in 0..n - last_packed - 2 {
        layers_not_packed.push(product_2_by_2(&layers_not_packed[i]));
    }

    assert_eq!(layers_not_packed[n - last_packed - 2].len(), 2);
    let product = layers_not_packed[n - last_packed - 2]
        .iter()
        .copied()
        .product::<EF>();
    prover_state.add_extension_scalars(&layers_not_packed[n - last_packed - 2]);

    let point = MultilinearPoint(vec![prover_state.sample()]);
    let mut claim = Evaluation {
        point: point.clone(),
        value: layers_not_packed[n - last_packed - 2].evaluate(&point),
    };

    for layer in layers_not_packed.iter().rev().skip(1) {
        claim = prove_gkr_product_step(prover_state, layer, &claim);
    }
    for layer in layers_packed.iter().rev() {
        claim = prove_gkr_product_step_packed(prover_state, layer, &claim);
    }

    (product, claim)
}

fn prove_gkr_product_step<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer: &[EF],
    claim: &Evaluation<EF>,
) -> Evaluation<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    assert_eq!(up_layer.len().ilog2() as usize - 1, claim.point.0.len());
    prove_gkr_product_step_core(
        prover_state,
        MleGroupRef::Extension(vec![left_ref(up_layer), right_ref(up_layer)]),
        claim,
    )
}

fn prove_gkr_product_step_packed<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer_packed: &[EFPacking<EF>],
    claim: &Evaluation<EF>,
) -> Evaluation<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    assert_eq!(
        up_layer_packed.len() * packing_width::<EF>(),
        2 << claim.point.0.len()
    );
    prove_gkr_product_step_core(
        prover_state,
        MleGroupRef::ExtensionPacked(vec![left_ref(up_layer_packed), right_ref(up_layer_packed)]),
        claim,
    )
}

fn prove_gkr_product_step_core<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer: MleGroupRef<'_, EF>,
    claim: &Evaluation<EF>,
) -> Evaluation<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let (sc_point, inner_evals, _) = sumcheck::prove::<EF, _, _, _>(
        1,
        up_layer,
        &ProductComputation,
        &ProductComputation,
        &[],
        Some((claim.point.0.clone(), None)),
        false,
        prover_state,
        claim.value,
        None,
    );

    prover_state.add_extension_scalars(&inner_evals);

    let mixing_challenge = prover_state.sample();

    let mut next_point = sc_point;
    next_point.0.insert(0, mixing_challenge);
    let next_claim =
        inner_evals[0] * (EF::ONE - mixing_challenge) + inner_evals[1] * mixing_challenge;

    (next_point, next_claim).into()
}

pub fn verify_gkr_product<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: usize,
) -> Result<(EF, Evaluation<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let [a, b] = verifier_state.next_extension_scalars_const()?;
    if b == EF::ZERO {
        return Err(ProofError::InvalidProof);
    }
    let product = a * b;

    let point = MultilinearPoint(vec![verifier_state.sample()]);
    let value = [a, b].evaluate(&point);
    let mut claim = Evaluation { point, value };

    for i in 1..n_vars {
        claim = verify_gkr_product_step(verifier_state, i, &claim)?;
    }

    Ok((product, claim))
}

fn verify_gkr_product_step<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    current_layer_log_len: usize,
    claim: &Evaluation<EF>,
) -> Result<Evaluation<EF>, ProofError>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let (sc_eval, postponed) = sumcheck::verify(verifier_state, current_layer_log_len, 3)
        .map_err(|_| ProofError::InvalidProof)?;

    if sc_eval != claim.value {
        return Err(ProofError::InvalidProof);
    }

    let [eval_left, eval_right] = verifier_state.next_extension_scalars_const()?;

    let postponed_target = claim.point.eq_poly_outside(&postponed.point) * eval_left * eval_right;
    if postponed_target != postponed.value {
        return Err(ProofError::InvalidProof);
    }

    let mixing_challenge = verifier_state.sample();

    let mut next_point = postponed.point;
    next_point.0.insert(0, mixing_challenge);

    let next_claim = eval_left * (EF::ONE - mixing_challenge) + eval_right * mixing_challenge;

    Ok((next_point, next_claim).into())
}

fn product_2_by_2<EF: PrimeCharacteristicRing + Sync + Send + Copy>(layer: &[EF]) -> Vec<EF> {
    let n = layer.len();
    (0..n / 2)
        .into_par_iter()
        .map(|i| layer[i] * layer[n / 2 + i])
        .collect()
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use p3_koala_bear::QuinticExtensionFieldKB;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use utils::{assert_eq_many, build_prover_state, build_verifier_state, pack_extension};

    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_gkr_product_step() {
        let log_n = 12;
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);

        let big = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let small = product_2_by_2(&big);

        let point = MultilinearPoint((0..log_n - 1).map(|_| rng.random()).collect::<Vec<EF>>());
        let eval = small.evaluate(&point);

        let mut prover_state = build_prover_state();

        let time = Instant::now();
        let claim = Evaluation { point, value: eval };
        prove_gkr_product_step_packed(&mut prover_state, &pack_extension(&big), &claim);
        dbg!(time.elapsed());

        let mut verifier_state = build_verifier_state(&prover_state);

        let postponed = verify_gkr_product_step(&mut verifier_state, log_n - 1, &claim).unwrap();
        assert_eq!(big.evaluate(&postponed.point), postponed.value);
    }

    #[test]
    fn test_gkr_product() {
        let log_n = 13;
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);

        let layer = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let real_product = layer.iter().copied().product::<EF>();

        let mut prover_state = build_prover_state();

        let time = Instant::now();
        let (product_prover, claim_prover) =
            prove_gkr_product(&mut prover_state, pack_extension(&layer));
        println!("GKR product took {:?}", time.elapsed());

        let mut verifier_state = build_verifier_state(&prover_state);

        let (product_verifier, claim_verifier) =
            verify_gkr_product::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(&claim_prover, &claim_verifier);
        assert_eq!(layer.evaluate(&claim_verifier.point), claim_verifier.value);
        assert_eq_many!(product_verifier, product_prover, real_product);
    }
}
