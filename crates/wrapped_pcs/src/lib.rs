use std::any::TypeId;
use std::array;

use p3_field::{ExtensionField, Field, dot_product};
use p3_koala_bear::KoalaBear;
use p3_util::log2_ceil_usize;
use rayon::iter::IntoParallelIterator;
use rayon::prelude::*;
use utils::{FSProver, FSVerifier, PF, localisation_in_poly_eq};
use whir_p3::utils::compute_sparse_eval_eq;
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofResult},
    poly::multilinear::Evaluation,
};

use crate::pcs::PCS;

/*

REF: https://2π.com/25/embedding-inner-products/

*/

mod pcs;

fn apply_matrix_b<const D: usize, F: Field>(b: &[F; D]) -> [F; D] {
    if D == 5 && TypeId::of::<F>() == TypeId::of::<KoalaBear>() {
        unsafe { std::mem::transmute_copy(&[b[1], b[0], b[4], b[3], b[2]]) }
    } else {
        unimplemented!()
    }
}

// d = EF::DIMENSION
// data has length d.2^n
pub fn wrap_pcs_commit<EF: ExtensionField<PF<EF>>, Pcs: PCS<EF, EF>, const D: usize>(
    data: &[PF<EF>],
    pcs: &Pcs,
    dft: &EvalsDft<PF<EF>>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
) -> (Pcs::Witness, Vec<EF>) {
    assert_eq!(EF::DIMENSION, D);
    assert!(data.len().is_multiple_of(D));
    assert!((data.len() / D).is_power_of_two());

    let two_pow_n = data.len() / D;

    let wrapped = (0..two_pow_n)
        .into_par_iter()
        .map(|i| {
            let chunk: [PF<EF>; D] = array::from_fn(|j| data[i + j * two_pow_n]);
            EF::from_basis_coefficients_slice(&apply_matrix_b::<D, PF<EF>>(&chunk)).unwrap()
        })
        .collect::<Vec<_>>();

    let witness = pcs.commit(dft, prover_state, &wrapped);
    (witness, wrapped)
}

// d = EF::DIMENSION
// data has length d.2^n
pub fn wrap_pcs_parse_commitment<EF: ExtensionField<PF<EF>>, Pcs: PCS<EF, EF>>(
    n: usize,
    pcs: &Pcs,
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
) -> ProofResult<Pcs::ParsedCommitment> {
    pcs.parse_commitment(verifier_state, n)
}

pub fn wrap_pcs_open<EF: ExtensionField<PF<EF>>, Pcs: PCS<EF, EF>, const D: usize>(
    data: &[PF<EF>],
    pcs: &Pcs,
    dft: &EvalsDft<PF<EF>>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    statements: Vec<Evaluation<EF>>,
    witness: Pcs::Witness,
    wrapped: &[EF],
) {
    assert_eq!(EF::DIMENSION, D);
    assert!(data.len().is_multiple_of(D));
    assert!((data.len() / D).is_power_of_two());
    for statement in statements.iter() {
        assert!(statement.num_variables() == log2_ceil_usize(data.len()));
        let (offset, size) = localisation_in_poly_eq(&statement.point);
        let right_bound = (offset + 1) * (1 << (statement.num_variables() - size));
        assert!(right_bound <= data.len());
    }

    let two_pow_n = data.len() / D;
    let batching_challenge = prover_state.sample();

    let mut batched_slice = EF::zero_vec(data.len());
    let mut batched_sum = EF::ZERO;
    for (statement, power) in statements.iter().zip(batching_challenge.powers()) {
        compute_sparse_eval_eq(&statement.point, &mut batched_slice, power);
        batched_sum += statement.value * power;
    }

    let alpha = prover_state.sample();
    let alpha_powers = alpha.powers().collect_n(D);

    let folded = (0..two_pow_n)
        .into_par_iter()
        .map(|i| {
            // TODO multiply by basis can be done faster
            (0..D)
                .map(|j| {
                    EF::ith_basis_element(j).unwrap()
                        * dot_product::<EF, _, _>(
                            alpha_powers.iter().copied(),
                            batched_slice[i + j * two_pow_n]
                                .as_basis_coefficients_slice()
                                .iter()
                                .copied(),
                        )
                })
                .sum::<EF>()
        })
        .collect::<Vec<_>>();

    pcs.open(
        dft,
        prover_state,
        vec![],
        Some((
            folded,
            dot_product::<EF, _, _>(
                alpha_powers.iter().copied(),
                batched_sum.as_basis_coefficients_slice().iter().copied(),
            ),
        )),
        witness,
        wrapped,
    );

    prover_state.add_extension_scalar(batched_sum);
}

#[cfg(test)]
mod tests {
    use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
    use p3_koala_bear::QuinticExtensionFieldKB;
    use rand::Rng;
    use rand::{SeedableRng, rngs::StdRng};
    use utils::{
        build_merkle_compress, build_merkle_hash, build_prover_state,
        padd_with_zero_to_next_power_of_two,
    };
    use whir_p3::poly::evals::EvaluationsList;
    use whir_p3::poly::multilinear::MultilinearPoint;
    use whir_p3::whir::config::{FoldingFactor, SecurityAssumption, WhirConfigBuilder};

    use super::*;

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;
    const D: usize = <EF as BasedVectorSpace<PF<EF>>>::DIMENSION;

    #[test]
    fn test_wrapped_pcs() {
        let n = 12;
        let mut rng = StdRng::seed_from_u64(0);
        let data = (0..(5 * (1 << n)))
            .map(|_| rng.random())
            .collect::<Vec<F>>();
        let data_padded = padd_with_zero_to_next_power_of_two(&data);

        let mut points = vec![
            vec![EF::ZERO; 1],
            vec![EF::ZERO, EF::ZERO],
            vec![EF::ZERO, EF::ONE],
            vec![EF::ZERO, EF::ONE, EF::ZERO],
            vec![EF::ONE, EF::ZERO, EF::ZERO],
        ];

        for point in points.iter_mut() {
            point.extend(
                (0..(n + log2_ceil_usize(D) - point.len()))
                    .map(|_| rng.random())
                    .collect::<Vec<EF>>(),
            );
        }

        let mut statements = vec![];
        for point in &points {
            statements.push(Evaluation::new(
                point.clone(),
                data_padded.evaluate(&MultilinearPoint(point.clone())),
            ));
        }

        let whir_config_builder = WhirConfigBuilder {
            folding_factor: FoldingFactor::new(5, 4),
            soundness_type: SecurityAssumption::CapacityBound,
            merkle_hash: build_merkle_hash(),
            merkle_compress: build_merkle_compress(),
            pow_bits: 10,
            max_num_variables_to_send_coeffs: 5,
            rs_domain_initial_reduction_factor: 1,
            security_level: 100,
            starting_log_inv_rate: 1,
        };

        let mut fs_prover = build_prover_state::<EF>();
        let dft = EvalsDft::default();

        let (witness, wrapped) =
            wrap_pcs_commit::<EF, _, 5>(&data, &whir_config_builder, &dft, &mut fs_prover);

        wrap_pcs_open::<EF, _, 5>(
            &data,
            &whir_config_builder,
            &dft,
            &mut fs_prover,
            statements,
            witness,
            &wrapped,
        );
    }
}
