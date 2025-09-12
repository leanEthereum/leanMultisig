use std::{cmp::Reverse, collections::BTreeMap};

use p3_field::{ExtensionField, Field};
use p3_util::{log2_ceil_usize, log2_strict_usize};
use rayon::prelude::*;
use tracing::instrument;
use utils::{
    Evaluation, FSProver, FSVerifier, PF, multilinear_eval_constants_at_right,
    to_big_endian_in_field,
};
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::multilinear::MultilinearPoint,
};

use crate::PCS;

#[derive(Debug, Clone)]
struct CommittedChunk {
    original_poly_index: usize,
    original_n_vars: usize,
    n_vars: usize,
    offset_in_original: usize,
    offset_in_packed: Option<usize>,
}

impl CommittedChunk {
    fn bits_offset_in_original<EF: Field>(&self) -> Vec<EF> {
        to_big_endian_in_field(
            self.offset_in_original >> self.n_vars,
            self.original_n_vars - self.n_vars,
        )
    }
}

#[derive(Debug, Clone)]
pub struct MultiCommitmentWitness<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>> {
    pub inner_witness: Pcs::Witness,
    pub packed_polynomial: Vec<F>,
}

#[derive(Debug, Clone, Copy)]
pub struct ColDims<F: Field> {
    pub n_vars: usize,          // column.len() == 1 << n_vars
    pub relevant_length: usize, // column[relevant_length..] = [default_value, ..., default_value]
    pub default_value: F,
}

impl<F: Field> ColDims<F> {
    pub fn dense(n_vars: usize) -> Self {
        Self {
            n_vars,
            relevant_length: 1 << n_vars,
            default_value: F::ZERO,
        }
    }

    pub fn sparse(n_vars: usize, relevant_length: usize, default_value: F) -> Self {
        assert!(relevant_length <= 1 << n_vars);
        Self {
            n_vars,
            relevant_length,
            default_value,
        }
    }
}

fn split_in_chunks<F: Field>(
    poly_index: usize,
    dims: &ColDims<F>,
    log_smallest_decomposition_chunk: usize,
) -> Vec<CommittedChunk> {
    let mut remaining = dims.relevant_length;
    let mut offset_in_original = 0;
    let mut res = Vec::new();
    loop {
        let chunk_size =
            if remaining.next_power_of_two() - remaining <= 1 << log_smallest_decomposition_chunk {
                log2_ceil_usize(remaining)
            } else {
                remaining.ilog2() as usize
            };
        res.push(CommittedChunk {
            original_poly_index: poly_index,
            original_n_vars: dims.n_vars,
            n_vars: chunk_size,
            offset_in_original,
            offset_in_packed: None,
        });
        offset_in_original += 1 << chunk_size;
        if remaining <= 1 << chunk_size {
            return res;
        }
        remaining -= 1 << chunk_size;
    }
}

fn compute_chunks<F: Field, EF: ExtensionField<F>>(
    dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
) -> (BTreeMap<usize, Vec<CommittedChunk>>, usize) {
    let mut all_chunks = Vec::new();
    for (i, dim) in dims.iter().enumerate() {
        all_chunks.extend(split_in_chunks(i, dim, log_smallest_decomposition_chunk));
    }
    all_chunks.sort_by_key(|c| Reverse(c.n_vars));

    let mut offset_in_packed = 0;
    let mut chunks_decomposition: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for chunk in &mut all_chunks {
        chunk.offset_in_packed = Some(offset_in_packed);
        offset_in_packed += 1 << chunk.n_vars;
        chunks_decomposition
            .entry(chunk.original_poly_index)
            .or_default()
            .push(chunk.clone());
    }
    let packed_n_vars = log2_ceil_usize(all_chunks.iter().map(|c| 1 << c.n_vars).sum::<usize>());
    (chunks_decomposition, packed_n_vars)
}

#[instrument(skip_all)]
pub fn packed_pcs_commit<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>>(
    pcs: &Pcs,
    polynomials: Vec<&[F]>,
    dims: &[ColDims<F>],
    dft: &EvalsDft<PF<EF>>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    log_smallest_decomposition_chunk: usize,
) -> MultiCommitmentWitness<F, EF, Pcs> {
    assert_eq!(polynomials.len(), dims.len());
    for (poly, dim) in polynomials.iter().zip(dims.iter()) {
        assert_eq!(poly.len(), 1 << dim.n_vars);
    }
    let (chunks_decomposition, packed_n_vars) =
        compute_chunks::<F, EF>(dims, log_smallest_decomposition_chunk);

    let packed_polynomial = F::zero_vec(1 << packed_n_vars);
    chunks_decomposition
        .values()
        .flatten()
        .collect::<Vec<_>>()
        .par_iter()
        .for_each(|chunk| {
            let start = chunk.offset_in_packed.unwrap();
            let end = start + (1 << chunk.n_vars);
            let original_poly = &polynomials[chunk.original_poly_index];
            unsafe {
                let slice = std::slice::from_raw_parts_mut(
                    (packed_polynomial.as_ptr() as *mut F).add(start),
                    end - start,
                );
                slice.copy_from_slice(
                    &original_poly
                        [chunk.offset_in_original..chunk.offset_in_original + (1 << chunk.n_vars)],
                );
            }
        });

    let inner_witness = pcs.commit(dft, prover_state, &packed_polynomial);
    MultiCommitmentWitness {
        inner_witness,
        packed_polynomial,
    }
}

pub fn packed_pcs_global_statements_for_prover<
    F: Field,
    EF: ExtensionField<F> + ExtensionField<PF<EF>>,
    Pcs: PCS<F, EF>,
>(
    witness: &MultiCommitmentWitness<F, EF, Pcs>,
    dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
    statements_per_polynomial: &[Vec<Evaluation<EF>>],
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
) -> Vec<Evaluation<EF>> {
    // TODO:
    // 1) parallelize
    // 2) cache the "eq" poly, and then use dot product
    // 3) for each statement we can avoid one of the sub-computation (so we should avoid the big one)
    // 4) current packing is not optimal in the end: can lead to [16][4][2][2] (instead of [16][8])
    // 5) opti in case of sparse point (containing boolean values) in statements

    let (chunks_decomposition, _) = compute_chunks::<F, EF>(dims, log_smallest_decomposition_chunk);

    let packed_vars = log2_strict_usize(witness.packed_polynomial.len());

    let statements_flattened = statements_per_polynomial
        .iter()
        .enumerate()
        .map(|(poly_index, poly_statements)| {
            poly_statements
                .iter()
                .map(move |statement| (poly_index, statement))
        })
        .flatten()
        .collect::<Vec<_>>();

    let sub_packed_statements_and_evals_to_send = statements_flattened
        .par_iter()
        .map(|(poly_index, statement)| {
            let chunks = &chunks_decomposition[&poly_index];
            assert!(!chunks.is_empty());
            let mut sub_packed_statements = Vec::new();
            let mut evals_to_send = Vec::new();
            if chunks.len() == 1 {
                assert_eq!(chunks[0].n_vars, statement.point.0.len());
                assert!(chunks[0].offset_in_packed.unwrap() % (1 << chunks[0].n_vars) == 0);
                let packed_point = MultilinearPoint(
                    [
                        to_big_endian_in_field(
                            chunks[0].offset_in_packed.unwrap() >> chunks[0].n_vars,
                            packed_vars - chunks[0].n_vars,
                        ),
                        statement.point.0.clone(),
                    ]
                    .concat(),
                );
                sub_packed_statements.push(Evaluation {
                    point: packed_point,
                    value: statement.value,
                });
            } else {
                assert_eq!(statement.point.0.len(), chunks[0].n_vars + 1);
                for chunk in chunks {
                    let missing_vars = statement.point.0.len() - chunk.n_vars;
                    let sub_point = MultilinearPoint(statement.point.0[missing_vars..].to_vec());
                    let sub_value = (&witness.packed_polynomial[chunk.offset_in_packed.unwrap()
                        ..chunk.offset_in_packed.unwrap() + (1 << chunk.n_vars)])
                        .evaluate(&sub_point);
                    let packed_point = MultilinearPoint(
                        [
                            to_big_endian_in_field(
                                chunk.offset_in_packed.unwrap() >> chunk.n_vars,
                                packed_vars - chunk.n_vars,
                            ),
                            sub_point.0.clone(),
                        ]
                        .concat(),
                    );
                    sub_packed_statements.push(Evaluation {
                        point: packed_point,
                        value: sub_value,
                    });
                    evals_to_send.push(sub_value);
                }
            }
            (sub_packed_statements, evals_to_send)
        })
        .collect::<Vec<_>>();

    let mut packed_statements = Vec::new();
    for (sub_packed_statements, evals_to_send) in sub_packed_statements_and_evals_to_send {
        packed_statements.extend(sub_packed_statements);
        prover_state.add_extension_scalars(&evals_to_send);
    }
    packed_statements
}

pub fn packed_pcs_parse_commitment<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>>(
    pcs: &Pcs,
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    commited_dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
) -> Result<Pcs::ParsedCommitment, ProofError> {
    let (_, packed_n_vars) =
        compute_chunks::<F, EF>(&commited_dims, log_smallest_decomposition_chunk);
    pcs.parse_commitment(verifier_state, packed_n_vars)
}

pub fn packed_pcs_global_statements_for_verifier<
    F: Field,
    EF: ExtensionField<F> + ExtensionField<PF<EF>>,
>(
    dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
    statements_per_polynomial: &[Vec<Evaluation<EF>>],
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
) -> Result<Vec<Evaluation<EF>>, ProofError> {
    assert_eq!(dims.len(), statements_per_polynomial.len());
    let (chunks_decomposition, packed_n_vars) =
        compute_chunks::<F, EF>(dims, log_smallest_decomposition_chunk);
    let mut packed_statements = Vec::new();
    for (poly_index, statements) in statements_per_polynomial.iter().enumerate() {
        let chunks = &chunks_decomposition[&poly_index];
        assert!(!chunks.is_empty());
        for statement in statements {
            if chunks.len() == 1 {
                assert_eq!(chunks[0].n_vars, statement.point.0.len());
                assert!(chunks[0].offset_in_packed.unwrap() % (1 << chunks[0].n_vars) == 0);
                let packed_point = MultilinearPoint(
                    [
                        to_big_endian_in_field(
                            chunks[0].offset_in_packed.unwrap() >> chunks[0].n_vars,
                            packed_n_vars - chunks[0].n_vars,
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
                assert_eq!(statement.point.0.len(), chunks[0].n_vars + 1);
                let sub_values = verifier_state.next_extension_scalars_vec(chunks.len())?; // TODO we could skip the last one, and deduce its value
                for (chunk, sub_value) in chunks.iter().zip(sub_values) {
                    let missing_vars = statement.point.0.len() - chunk.n_vars;
                    let sub_point = MultilinearPoint(statement.point.0[missing_vars..].to_vec());
                    let packed_point = MultilinearPoint(
                        [
                            to_big_endian_in_field(
                                chunk.offset_in_packed.unwrap() >> chunk.n_vars,
                                packed_n_vars - chunk.n_vars,
                            ),
                            sub_point.0.clone(),
                        ]
                        .concat(),
                    );
                    packed_statements.push(Evaluation {
                        point: packed_point,
                        value: sub_value,
                    });
                }
                // consistency check
                {
                    let mut retrieved_eval = EF::ZERO;
                    let mut chunk_offset_sums = 0;
                    assert_eq!(statement.point.len(), chunks[0].n_vars + 1);
                    for (i, chunk) in chunks.iter().enumerate() {
                        let missing_vars = statement.point.0.len() - chunk.n_vars;
                        retrieved_eval +=
                            packed_statements[packed_statements.len() - chunks.len() + i].value
                                * MultilinearPoint(statement.point.0[..missing_vars].to_vec())
                                    .eq_poly_outside(&MultilinearPoint(
                                        chunk.bits_offset_in_original(),
                                    ));
                        chunk_offset_sums += 1 << chunk.n_vars;
                    }
                    retrieved_eval +=
                        multilinear_eval_constants_at_right(chunk_offset_sums, &statement.point)
                            * dims[poly_index].default_value;

                    if retrieved_eval != statement.value {
                        return Err(ProofError::InvalidProof);
                    }
                }
            }
        }
    }
    Ok(packed_statements)
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use p3_field::{PrimeCharacteristicRing, extension::BinomialExtensionField};
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
    type EF = BinomialExtensionField<KoalaBear, 4>;

    #[test]
    fn test_packed_pcs() {
        let pcs = WhirConfigBuilder {
            folding_factor: FoldingFactor::ConstantFromSecondRound(4, 4),
            soundness_type: SecurityAssumption::CapacityBound,
            merkle_hash: build_merkle_hash(),
            merkle_compress: build_merkle_compress(),
            pow_bits: 13,
            max_num_variables_to_send_coeffs: 6,
            rs_domain_initial_reduction_factor: 1,
            security_level: 75,
            starting_log_inv_rate: 1,
            base_field: PhantomData::<F>,
            extension_field: PhantomData::<EF>,
        };

        let mut rng = StdRng::seed_from_u64(0);
        let log_smallest_decomposition_chunk = 3;
        let pol_lengths_and_default_value: [(usize, F); _] = [
            (16, F::from_usize(8)),
            (854, F::from_usize(0)),
            (854, F::from_usize(1)),
            (16, F::from_usize(0)),
            (17, F::from_usize(0)),
            (95, F::from_usize(3)),
            (256, F::from_usize(8)),
            (1088, F::from_usize(9)),
            (512, F::from_usize(0)),
            (754, F::from_usize(4)),
            (1023, F::from_usize(7)),
            (2025, F::from_usize(11)),
        ];
        let mut polynomials = Vec::new();
        let mut dims = Vec::new();
        let mut statements_per_polynomial = Vec::new();
        for &(pol_length, default_value) in &pol_lengths_and_default_value {
            let mut poly = (0..pol_length).map(|_| rng.random()).collect::<Vec<F>>();
            poly.resize(pol_length.next_power_of_two(), default_value);
            let n_vars = log2_strict_usize(poly.len());
            let n_points = rng.random_range(1..5);
            let mut statements = Vec::new();
            for _ in 0..n_points {
                let point =
                    MultilinearPoint((0..n_vars).map(|_| rng.random()).collect::<Vec<EF>>());
                let value = poly.evaluate(&point);
                statements.push(Evaluation { point, value });
            }
            polynomials.push(poly);
            dims.push(ColDims {
                n_vars,
                relevant_length: pol_length,
                default_value,
            });
            statements_per_polynomial.push(statements);
        }

        let mut prover_state = build_prover_state();
        let dft = EvalsDft::<F>::default();

        let witness = packed_pcs_commit(
            &pcs,
            polynomials.iter().map(|p| p.as_slice()).collect(),
            &dims,
            &dft,
            &mut prover_state,
            log_smallest_decomposition_chunk,
        );

        let packed_statements = packed_pcs_global_statements_for_prover(
            &witness,
            &dims,
            log_smallest_decomposition_chunk,
            &statements_per_polynomial,
            &mut prover_state,
        );
        pcs.open(
            &dft,
            &mut prover_state,
            &packed_statements,
            witness.inner_witness,
            &witness.packed_polynomial,
        );

        let mut verifier_state = build_verifier_state(&prover_state);

        let parsed_commitment = packed_pcs_parse_commitment(
            &pcs,
            &mut verifier_state,
            &dims,
            log_smallest_decomposition_chunk,
        )
        .unwrap();
        let packed_statements = packed_pcs_global_statements_for_verifier(
            &dims,
            log_smallest_decomposition_chunk,
            &statements_per_polynomial,
            &mut verifier_state,
        )
        .unwrap();
        pcs.verify(&mut verifier_state, &parsed_commitment, &packed_statements)
            .unwrap();
    }
}
