use std::{cmp::Reverse, collections::BTreeMap};

use p3_field::{ExtensionField, Field};
use p3_util::{log2_ceil_usize, log2_strict_usize};
use rayon::prelude::*;
use tracing::instrument;
use utils::{Evaluation, FSProver, FSVerifier, PF, to_big_endian_in_field};
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::multilinear::MultilinearPoint,
};

use crate::PCS;

const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 10;

#[derive(Debug, Clone)]
struct CommittedChunk {
    original_poly_index: usize,
    vars: usize,
    index_in_original: usize, // 0 if first (biggest) chunk, 1 if second, etc.
    offset_in_packed: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct MultiCommitmentWitness<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>> {
    chunks_decomposition: BTreeMap<usize, Vec<CommittedChunk>>, // real polynomial index -> list of virtual polynomial indexes (chunks) in which it was split
    pub inner_witness: Pcs::Witness,
    pub packed_polynomial: Vec<F>,
}

#[derive(Debug, Clone, Copy)]
pub struct CommittedPol<'a, F: Field> {
    pub polynomial: &'a [F],
    pub vars: usize,            // polynomial.len() == 1 << vars
    pub relevant_length: usize, // polynomial[relevant_length..] = [default_value, ..., default_value]
    pub default_value: F,
}

impl<'a, F: Field> CommittedPol<'a, F> {
    pub fn dense(polynomial: &'a [F]) -> Self {
        Self {
            polynomial,
            vars: log2_strict_usize(polynomial.len()),
            relevant_length: polynomial.len(),
            default_value: F::ZERO,
        }
    }

    pub fn sparse(polynomial: &'a [F], relevant_length: usize, default_value: F) -> Self {
        assert!(relevant_length <= polynomial.len());
        debug_assert!(
            polynomial[relevant_length..]
                .par_iter()
                .all(|c| c == &default_value)
        );
        Self {
            polynomial,
            vars: log2_strict_usize(polynomial.len()),
            relevant_length,
            default_value,
        }
    }
}

fn split_in_chunks<F: Field>(poly_index: usize, poly: &CommittedPol<'_, F>) -> Vec<CommittedChunk> {
    let mut remaining = poly.relevant_length;
    let mut index_in_original = 0;
    let mut res = Vec::new();
    loop {
        let chunk_size =
            if remaining.next_power_of_two() - remaining <= 1 << LOG_SMALLEST_DECOMPOSITION_CHUNK {
                log2_ceil_usize(remaining)
            } else {
                remaining.ilog2() as usize
            };
        res.push(CommittedChunk {
            original_poly_index: poly_index,
            vars: chunk_size,
            index_in_original,
            offset_in_packed: None,
        });
        index_in_original += 1;
        if remaining <= 1 << chunk_size {
            return res;
        }
        remaining -= 1 << chunk_size;
    }
}

#[instrument(skip_all)]
pub fn packed_pcs_commit<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>>(
    pcs: &Pcs,
    polynomials: &[CommittedPol<'_, F>],
    dft: &EvalsDft<PF<EF>>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
) -> MultiCommitmentWitness<F, EF, Pcs> {
    let mut all_chunks = Vec::new();
    for (i, poly) in polynomials.iter().enumerate() {
        all_chunks.extend(split_in_chunks(i, poly));
    }
    all_chunks.sort_by_key(|c| Reverse(c.vars));

    let mut offset_in_packed = 0;
    let mut chunks_decomposition: BTreeMap<usize, Vec<CommittedChunk>> = BTreeMap::new();
    for chunk in &mut all_chunks {
        chunk.offset_in_packed = Some(offset_in_packed);
        offset_in_packed += 1 << chunk.vars;
        chunks_decomposition
            .entry(chunk.original_poly_index)
            .or_default()
            .push(chunk.clone());
    }

    let total_size = all_chunks
        .iter()
        .map(|c| 1 << c.vars)
        .sum::<usize>()
        .next_power_of_two();
    let packed_polynomial = F::zero_vec(total_size);
    all_chunks.par_iter().for_each(|chunk| {
        let start = chunk.offset_in_packed.unwrap();
        let end = start + (1 << chunk.vars);
        let original_poly = &polynomials[chunk.original_poly_index].polynomial;
        // original_start = (1 << (chunk.vars + 1)) + (1 << (chunk.vars + 2)) + ... (1 << (chunk.vars + index_in_original - 1))
        let original_start = (1 << (chunk.vars + 1)) * ((1 << chunk.index_in_original) - 1);
        let original_end = original_start + (1 << chunk.vars);
        unsafe {
            let slice = std::slice::from_raw_parts_mut(
                (packed_polynomial.as_ptr() as *mut F).add(start),
                end - start,
            );
            slice.copy_from_slice(&original_poly[original_start..original_end]);
        }
    });

    let inner_witness = pcs.commit(dft, prover_state, &packed_polynomial);
    MultiCommitmentWitness {
        chunks_decomposition,
        inner_witness,
        packed_polynomial,
    }
}

pub fn packed_pcs_global_statements<
    F: Field,
    EF: ExtensionField<F> + ExtensionField<PF<EF>>,
    Pcs: PCS<F, EF>,
>(
    witness: &MultiCommitmentWitness<F, EF, Pcs>,
    statements_per_polynomial: &[Vec<Evaluation<EF>>],
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
) -> Vec<Evaluation<EF>> {
    // TODO:
    // 1) parallelize
    // 2) cache the "eq" poly, and then use dot product
    // 3) for each statement we can avoid one of the sub-computation (so we should avoid the big one)

    let packed_vars = log2_strict_usize(witness.packed_polynomial.len());
    let mut packed_statements = Vec::new();
    for (poly_index, statements) in statements_per_polynomial.iter().enumerate() {
        let chunks = &witness.chunks_decomposition[&poly_index];
        assert!(!chunks.is_empty());
        for statement in statements {
            if chunks.len() == 1 {
                assert_eq!(chunks[0].vars, statement.point.0.len());
                let packed_point = MultilinearPoint(
                    [
                        to_big_endian_in_field(
                            chunks[0].offset_in_packed.unwrap(),
                            packed_vars - chunks[0].vars,
                        ),
                        statement.point.0.clone(),
                    ]
                    .concat(),
                );
                packed_statements.push(Evaluation {
                    point: packed_point,
                    value: statement.value,
                });
            } else {
                for (chunk_index, chunk) in chunks.iter().enumerate() {
                    let sub_point = MultilinearPoint(statement.point.0[1 + chunk_index..].to_vec());
                    let sub_value = (&witness.packed_polynomial[chunk.offset_in_packed.unwrap()
                        << chunk.vars
                        ..(chunk.offset_in_packed.unwrap() + 1) << chunk.vars])
                        .evaluate(&sub_point);
                    let packed_point = MultilinearPoint(
                        [
                            to_big_endian_in_field(
                                chunk.offset_in_packed.unwrap(),
                                packed_vars - chunk.vars,
                            ),
                            sub_point.0.clone(),
                        ]
                        .concat(),
                    );
                    packed_statements.push(Evaluation {
                        point: packed_point,
                        value: sub_value,
                    });
                    prover_state.add_extension_scalar(sub_value);

                    // TODO sanity assert_eq
                }
            }
        }
    }
    packed_statements
}

#[derive(Debug)]
pub struct ParsedMultiCommitment<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>> {
    pub tree: TreeOfVariables,
    pub inner_parsed_commitment: Pcs::ParsedCommitment,
}

pub fn packed_pcs_parse_commitment<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>>(
    pcs: &Pcs,
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    vars_per_polynomial: Vec<usize>,
) -> Result<ParsedMultiCommitment<F, EF, Pcs>, ProofError> {
    let tree = TreeOfVariables::compute_optimal(vars_per_polynomial);
    let inner_parsed_commitment = pcs.parse_commitment(verifier_state, tree.total_vars())?;
    Ok(ParsedMultiCommitment {
        tree,
        inner_parsed_commitment,
    })
}
#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use p3_field::extension::BinomialExtensionField;
    use p3_koala_bear::KoalaBear;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use utils::{
        build_merkle_compress, build_merkle_hash, build_prover_state, build_verifier_state,
    };
    use whir_p3::{
        poly::evals::EvaluationsList,
        whir::config::{FoldingFactor, SecurityAssumption, WhirConfigBuilder},
    };

    use super::*;

    type F = KoalaBear;
    type EF = BinomialExtensionField<F, 4>;

    #[test]
    fn test_check_tree() {
        let pcs = WhirConfigBuilder {
            folding_factor: FoldingFactor::ConstantFromSecondRound(4, 4),
            soundness_type: SecurityAssumption::CapacityBound,
            merkle_hash: build_merkle_hash(),
            merkle_compress: build_merkle_compress(),
            pow_bits: 16,
            max_num_variables_to_send_coeffs: 6,
            rs_domain_initial_reduction_factor: 1,
            security_level: 90,
            starting_log_inv_rate: 1,
            base_field: PhantomData::<F>,
            extension_field: PhantomData::<EF>,
        };

        let mut rng = StdRng::seed_from_u64(0);
        let vars_per_polynomial = [4, 4, 5, 3, 7, 10, 8];
        let mut polynomials = Vec::new();
        let mut statements_per_polynomial = Vec::new();
        for &vars in &vars_per_polynomial {
            let poly = (0..1 << vars).map(|_| rng.random()).collect::<Vec<F>>();
            let n_points = rng.random_range(1..5);
            let mut statements = Vec::new();
            for _ in 0..n_points {
                let point = MultilinearPoint((0..vars).map(|_| rng.random()).collect::<Vec<EF>>());
                let value = poly.evaluate(&point);
                statements.push(Evaluation { point, value });
            }
            polynomials.push(poly);
            statements_per_polynomial.push(statements);
        }

        let mut prover_state = build_prover_state();
        let dft = EvalsDft::<F>::default();

        let polynomials_refs = polynomials.iter().map(|p| p.as_slice()).collect::<Vec<_>>();
        let witness = packed_pcs_commit(&pcs, &polynomials_refs, &dft, &mut prover_state);

        let packed_statements =
            packed_pcs_global_statements(&witness.tree, &statements_per_polynomial);
        pcs.open(
            &dft,
            &mut prover_state,
            &packed_statements,
            witness.inner_witness,
            &witness.packed_polynomial,
        );

        let mut verifier_state = build_verifier_state(&prover_state);

        let parsed_commitment =
            packed_pcs_parse_commitment(&pcs, &mut verifier_state, vars_per_polynomial.to_vec())
                .unwrap();
        let packed_statements =
            packed_pcs_global_statements(&parsed_commitment.tree, &statements_per_polynomial);
        pcs.verify(
            &mut verifier_state,
            &parsed_commitment.inner_parsed_commitment,
            &packed_statements,
        )
        .unwrap();
    }
}
