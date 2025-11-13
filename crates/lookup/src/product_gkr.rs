/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

with custom GKR

*/

use multilinear_toolkit::prelude::*;
use tracing::instrument;
use utils::left_ref;
use utils::right_ref;
use utils::{FSProver, FSVerifier};

use crate::MIN_VARS_FOR_PACKING;

/*
Custom GKR to compute a product.

A: [a0, a1, a2, a3, a4, a5, a6, a7]
A': [a0*a4, a1*a5, a2*a6, a3*a7]
...

*/

#[instrument(skip_all)]
pub fn prove_gkr_product<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    final_layer: &[EF],
) -> (EF, Evaluation<EF>)
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    assert!(log2_strict_usize(final_layer.len()) >= 1);
    if final_layer.len() == 2 {
        prover_state.add_extension_scalars(final_layer);
        let product = final_layer[0] * final_layer[1];
        let point = MultilinearPoint(vec![prover_state.sample()]);
        let claim = Evaluation {
            point: point.clone(),
            value: final_layer.evaluate(&point),
        };
        return (product, claim);
    }

    let final_layer: Mle<'_, EF> = if final_layer.len() >= 1 << MIN_VARS_FOR_PACKING {
        // TODO packing beforehand
        MleOwned::ExtensionPacked(pack_extension(final_layer)).into()
    } else {
        MleRef::Extension(final_layer).into()
    };

    let mut layers = vec![final_layer];
    loop {
        if layers.last().unwrap().n_vars() == 1 {
            break;
        }
        layers.push(product_2_by_2(&layers.last().unwrap().by_ref()).into());
    }

    let last_layer = match layers.last().unwrap().by_ref() {
        MleRef::Extension(slice) => slice,
        _ => unreachable!(),
    };
    assert_eq!(last_layer.len(), 2);
    let product = last_layer[0] * last_layer[1];
    prover_state.add_extension_scalars(last_layer);

    let point = MultilinearPoint(vec![prover_state.sample()]);
    let mut claim = Evaluation {
        point: point.clone(),
        value: last_layer.evaluate(&point),
    };

    for layer in layers.iter().rev().skip(1) {
        claim = match layer.by_ref() {
            MleRef::Extension(slice) => prove_gkr_product_step(prover_state, slice, &claim),
            MleRef::ExtensionPacked(slice) => {
                prove_gkr_product_step_packed(prover_state, slice, &claim)
            }
            _ => unreachable!(),
        }
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
    let (sc_point, inner_evals, _) = sumcheck_prove::<EF, _, _>(
        1,
        up_layer,
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

    Evaluation::new(next_point, next_claim)
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
    let (sc_eval, postponed) = sumcheck_verify(verifier_state, current_layer_log_len, 3)
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

    Ok(Evaluation::new(next_point, next_claim))
}

fn product_2_by_2<EF: ExtensionField<PF<EF>>>(layer: &MleRef<'_, EF>) -> MleOwned<EF> {
    match layer {
        MleRef::Extension(slice) => MleOwned::Extension(product_2_by_2_helper(slice)),
        MleRef::ExtensionPacked(slice) => {
            if slice.len() >= 1 << MIN_VARS_FOR_PACKING {
                MleOwned::ExtensionPacked(product_2_by_2_helper(slice))
            } else {
                MleOwned::Extension(product_2_by_2_helper(&unpack_extension(slice)))
            }
        }
        _ => unreachable!(),
    }
}

fn product_2_by_2_helper<EF: PrimeCharacteristicRing + Sync + Send + Copy>(
    layer: &[EF],
) -> Vec<EF> {
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
    use utils::{assert_eq_many, build_prover_state, build_verifier_state};

    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_gkr_product() {
        for log_n in 1..10 {
            test_gkr_product_helper(log_n);
        }
    }

    fn test_gkr_product_helper(log_n: usize) {
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);

        let layer = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let real_product = layer.iter().copied().product::<EF>();

        let mut prover_state = build_prover_state();

        let time = Instant::now();

        let (product_prover, claim_prover) = prove_gkr_product(&mut prover_state, &layer);
        println!("GKR product took {:?}", time.elapsed());

        let mut verifier_state = build_verifier_state(&prover_state);

        let (product_verifier, claim_verifier) =
            verify_gkr_product::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(&claim_prover, &claim_verifier);
        assert_eq!(layer.evaluate(&claim_verifier.point), claim_verifier.value);
        assert_eq_many!(product_verifier, product_prover, real_product);
    }
}
