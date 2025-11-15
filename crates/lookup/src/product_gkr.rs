/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

with custom GKR

*/

use multilinear_toolkit::prelude::*;
use tracing::instrument;
use utils::{FSProver, FSVerifier};

use crate::MIN_VARS_FOR_PACKING;

/*
Custom GKR to compute a product.

A: [a0, a1, a2, a3, a4, a5, a6, a7]
A': [a0*a4, a1*a5, a2*a6, a3*a7]
...

*/

#[instrument(skip_all)]
pub fn prove_gkr_product<EF, const N_GROUPS: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    final_layer: &[EF],
) -> (EF, Evaluation<EF>)
where
    EF: ExtensionField<PF<EF>>,
{
    assert!(
        log2_strict_usize(final_layer.len()) > log2_strict_usize(N_GROUPS),
        "TODO small case"
    );

    let final_layer: Mle<'_, EF> = if final_layer.len() >= 1 << MIN_VARS_FOR_PACKING {
        // TODO packing beforehand
        MleOwned::ExtensionPacked(pack_extension(final_layer)).into()
    } else {
        MleRef::Extension(final_layer).into()
    };

    let mut layers = vec![final_layer];
    layers.push(product_n_by_n::<_, N_GROUPS>(&layers.last().unwrap().by_ref()).into());
    loop {
        if layers.last().unwrap().n_vars() == 1 {
            break;
        }
        layers.push(product_n_by_n::<_, 2>(&layers.last().unwrap().by_ref()).into());
    }

    let last_layer = layers.pop().unwrap();
    let last_layer = match last_layer.by_ref() {
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

    for layer in layers[1..].iter().rev() {
        claim = prove_gkr_product_step::<_, 2>(prover_state, &layer.by_ref(), &claim);
    }
    claim = prove_gkr_product_step::<_, N_GROUPS>(prover_state, &layers[0].by_ref(), &claim);

    (product, claim)
}

fn prove_gkr_product_step<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer: &MleRef<'_, EF>,
    claim: &Evaluation<EF>,
) -> Evaluation<EF> {
    match up_layer {
        MleRef::Extension(slice) => {
            prove_gkr_product_step_unpacked::<_, N_GROUPS>(prover_state, slice, &claim)
        }
        MleRef::ExtensionPacked(slice) => {
            prove_gkr_product_step_packed::<_, N_GROUPS>(prover_state, slice, &claim)
        }
        _ => unreachable!(),
    }
}

fn prove_gkr_product_step_unpacked<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer: &[EF],
    claim: &Evaluation<EF>,
) -> Evaluation<EF> {
    assert_eq!(up_layer.len(), N_GROUPS << claim.point.0.len());
    prove_gkr_product_step_core::<_, N_GROUPS>(
        prover_state,
        MleGroupRef::Extension(split_at_many(
            up_layer,
            &(1..N_GROUPS)
                .map(|i| i * up_layer.len() / N_GROUPS)
                .collect::<Vec<_>>(),
        )),
        claim,
    )
}

fn prove_gkr_product_step_packed<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer_packed: &[EFPacking<EF>],
    claim: &Evaluation<EF>,
) -> Evaluation<EF> {
    assert_eq!(
        up_layer_packed.len() * packing_width::<EF>(),
        N_GROUPS << claim.point.0.len()
    );
    prove_gkr_product_step_core::<_, N_GROUPS>(
        prover_state,
        MleGroupRef::ExtensionPacked(split_at_many(
            up_layer_packed,
            &(1..N_GROUPS)
                .map(|i| i * up_layer_packed.len() / N_GROUPS)
                .collect::<Vec<_>>(),
        )),
        claim,
    )
}

fn prove_gkr_product_step_core<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer: MleGroupRef<'_, EF>,
    claim: &Evaluation<EF>,
) -> Evaluation<EF> {
    let _: () = assert!(N_GROUPS.is_power_of_two());
    assert_eq!(up_layer.n_columns(), N_GROUPS);
    let (sc_point, inner_evals, _) = sumcheck_prove::<EF, _, _>(
        1,
        up_layer,
        &MultiProductComputation::<N_GROUPS> {},
        &[],
        Some((claim.point.0.clone(), None)),
        false,
        prover_state,
        claim.value,
        None,
    );

    prover_state.add_extension_scalars(&inner_evals);

    let selectors = univariate_selectors::<PF<EF>>(log2_strict_usize(N_GROUPS));
    let mixing_challenge = prover_state.sample();

    let mut next_point = sc_point;
    next_point.0.insert(0, mixing_challenge);
    let next_claim: EF = inner_evals
        .iter()
        .enumerate()
        .map(|(i, &v)| v * selectors[i].evaluate(mixing_challenge))
        .sum();

    Evaluation::new(next_point, next_claim)
}

pub fn verify_gkr_product<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: usize,
) -> Result<(EF, Evaluation<EF>), ProofError> {
    assert!(n_vars > log2_strict_usize(N_GROUPS), "TODO small case");
    let [a, b] = verifier_state.next_extension_scalars_const()?;
    let product = a * b;

    let point = MultilinearPoint(vec![verifier_state.sample()]);
    let value = [a, b].evaluate(&point);
    let mut claim = Evaluation { point, value };

    for i in 1..n_vars - log2_strict_usize(N_GROUPS) {
        claim = verify_gkr_product_step::<_, 2>(verifier_state, i, &claim)?;
    }
    claim = verify_gkr_product_step::<_, N_GROUPS>(
        verifier_state,
        n_vars - log2_strict_usize(N_GROUPS),
        &claim,
    )?;

    Ok((product, claim))
}

fn verify_gkr_product_step<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    current_layer_log_len: usize,
    claim: &Evaluation<EF>,
) -> Result<Evaluation<EF>, ProofError> {
    let (sc_eval, postponed) =
        sumcheck_verify(verifier_state, current_layer_log_len, 1 + N_GROUPS)?;

    if sc_eval != claim.value {
        return Err(ProofError::InvalidProof);
    }

    let inner_evals = verifier_state.next_extension_scalars_const::<N_GROUPS>()?;

    let postponed_target =
        claim.point.eq_poly_outside(&postponed.point) * inner_evals.iter().copied().product::<EF>();
    if postponed_target != postponed.value {
        return Err(ProofError::InvalidProof);
    }

    let selectors = univariate_selectors::<PF<EF>>(log2_strict_usize(N_GROUPS));
    let mixing_challenge = verifier_state.sample();

    let mut next_point = postponed.point;
    next_point.0.insert(0, mixing_challenge);

    let next_claim: EF = inner_evals
        .iter()
        .enumerate()
        .map(|(i, &v)| v * selectors[i].evaluate(mixing_challenge))
        .sum();

    Ok(Evaluation::new(next_point, next_claim))
}

fn product_n_by_n<EF: ExtensionField<PF<EF>>, const N: usize>(
    layer: &MleRef<'_, EF>,
) -> MleOwned<EF> {
    match layer {
        MleRef::Extension(slice) => MleOwned::Extension(product_n_by_n_helper::<_, N>(slice)),
        MleRef::ExtensionPacked(slice) => {
            if slice.len() >= 1 << MIN_VARS_FOR_PACKING {
                MleOwned::ExtensionPacked(product_n_by_n_helper::<_, N>(slice))
            } else {
                MleOwned::Extension(product_n_by_n_helper::<_, N>(&unpack_extension(slice)))
            }
        }
        _ => unreachable!(),
    }
}

fn product_n_by_n_helper<EF: PrimeCharacteristicRing + Sync + Send + Copy, const N: usize>(
    layer: &[EF],
) -> Vec<EF> {
    assert!(layer.len().is_multiple_of(N));
    let size = layer.len();
    let size_div_n = size / N;
    (0..size / N)
        .into_par_iter()
        .map(|i| (0..N).map(|j| layer[i + j * size_div_n]).product())
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
        test_gkr_product_helper::<8>(20);
        test_gkr_product_helper::<4>(7);
        test_gkr_product_helper::<4>(3);
    }

    fn test_gkr_product_helper<const N_GROUPS: usize>(log_n: usize) {
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);

        let layer = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let real_product = layer.iter().copied().product::<EF>();

        let mut prover_state = build_prover_state();

        let time = Instant::now();

        let (product_prover, claim_prover) =
            prove_gkr_product::<_, N_GROUPS>(&mut prover_state, &layer);
        println!("GKR product took {:?}", time.elapsed());

        let mut verifier_state = build_verifier_state(&prover_state);

        let (product_verifier, claim_verifier) =
            verify_gkr_product::<_, N_GROUPS>(&mut verifier_state, log_n).unwrap();
        assert_eq!(&claim_prover, &claim_verifier);
        let selectors = univariate_selectors::<PF<EF>>(log2_strict_usize(N_GROUPS));
        assert_eq!(
            evaluate_univariate_multilinear::<_, _, _, true>(
                &layer,
                &claim_verifier.point,
                &selectors,
                None
            ),
            claim_verifier.value
        );
        assert_eq_many!(product_verifier, product_prover, real_product);
    }
}
