use std::{cmp::Reverse, collections::BTreeMap};

use p3_field::{ExtensionField, Field};
use p3_util::{log2_ceil_usize, log2_strict_usize};
use rayon::prelude::*;
use tracing::instrument;
use utils::{
    Evaluation, FSProver, FSVerifier, PF, from_end, multilinear_eval_constants_at_right,
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
struct Chunk {
    original_poly_index: usize,
    original_n_vars: usize,
    n_vars: usize,
    offset_in_original: usize,
    public_data: bool,
    offset_in_packed: Option<usize>,
}

impl Chunk {
    fn bits_offset_in_original<EF: Field>(&self) -> Vec<EF> {
        to_big_endian_in_field(
            self.offset_in_original >> self.n_vars,
            self.original_n_vars - self.n_vars,
        )
    }
}

/*
General layout: [public data][committed data][repeated value] (the thing has length 2^n_vars, public data is a power of two)
*/
#[derive(Debug, Clone, Copy)]
pub struct ColDims<F: Field> {
    pub n_vars: usize,
    pub log_public: Option<usize>,
    pub n_committed: usize,
    pub default_value: F,
}

impl<F: Field> ColDims<F> {
    pub fn dense(n_vars: usize) -> Self {
        Self {
            n_vars,
            log_public: None,
            n_committed: 1 << n_vars,
            default_value: F::ZERO,
        }
    }

    pub fn sparse(
        n_vars: usize,
        log_public: Option<usize>,
        n_committed: usize,
        default_value: F,
    ) -> Self {
        let n_public = log_public.map_or(0, |l| 1 << l);
        assert!(n_public + n_committed <= 1 << n_vars);
        Self {
            n_vars,
            log_public,
            n_committed,
            default_value,
        }
    }
}

fn split_in_chunks<F: Field>(
    poly_index: usize,
    dims: &ColDims<F>,
    log_smallest_decomposition_chunk: usize,
) -> Vec<Chunk> {
    let mut offset_in_original = 0;
    let mut res = Vec::new();
    if let Some(log_public) = dims.log_public {
        assert!(log_public >= log_smallest_decomposition_chunk);
        res.push(Chunk {
            original_poly_index: poly_index,
            original_n_vars: dims.n_vars,
            n_vars: log_public,
            offset_in_original,
            public_data: true,
            offset_in_packed: None,
        });
        offset_in_original += 1 << log_public;
    }
    let mut remaining = dims.n_committed;

    loop {
        let mut chunk_size =
            if remaining.next_power_of_two() - remaining <= 1 << log_smallest_decomposition_chunk {
                log2_ceil_usize(remaining)
            } else {
                remaining.ilog2() as usize
            };
        if let Some(log_public) = dims.log_public {
            chunk_size = chunk_size.min(log_public);
        }

        res.push(Chunk {
            original_poly_index: poly_index,
            original_n_vars: dims.n_vars,
            n_vars: chunk_size,
            offset_in_original,
            public_data: false,
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
) -> (BTreeMap<usize, Vec<Chunk>>, usize) {
    let mut all_chunks = Vec::new();
    for (i, dim) in dims.iter().enumerate() {
        all_chunks.extend(split_in_chunks(i, dim, log_smallest_decomposition_chunk));
    }
    all_chunks.sort_by_key(|c| (Reverse(c.public_data), Reverse(c.n_vars)));

    let mut offset_in_packed = 0;
    let mut chunks_decomposition: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for chunk in &mut all_chunks {
        if !chunk.public_data {
            chunk.offset_in_packed = Some(offset_in_packed);
            offset_in_packed += 1 << chunk.n_vars;
        }
        chunks_decomposition
            .entry(chunk.original_poly_index)
            .or_default()
            .push(chunk.clone());
    }
    let packed_n_vars = log2_ceil_usize(
        all_chunks
            .iter()
            .filter(|c| !c.public_data)
            .map(|c| 1 << c.n_vars)
            .sum::<usize>(),
    );
    (chunks_decomposition, packed_n_vars)
}

pub fn num_packed_vars_for_dims<F: Field, EF: ExtensionField<F>>(
    dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
) -> usize {
    let (_, packed_n_vars) = compute_chunks::<F, EF>(dims, log_smallest_decomposition_chunk);
    packed_n_vars
}

#[derive(Debug, Clone)]
pub struct MultiCommitmentWitness<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>> {
    pub inner_witness: Pcs::Witness,
    pub packed_polynomial: Vec<F>,
}

#[instrument(skip_all)]
pub fn packed_pcs_commit<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>>(
    pcs: &Pcs,
    polynomials: &[&[F]],
    dims: &[ColDims<F>],
    dft: &EvalsDft<PF<EF>>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    log_smallest_decomposition_chunk: usize,
) -> MultiCommitmentWitness<F, EF, Pcs> {
    assert_eq!(polynomials.len(), dims.len());
    for (i, (poly, dim)) in polynomials.iter().zip(dims.iter()).enumerate() {
        assert_eq!(
            poly.len(),
            1 << dim.n_vars,
            "poly {} has {} vars, but dim should be {}",
            i,
            log2_strict_usize(poly.len()),
            dim.n_vars
        );
    }
    let (chunks_decomposition, packed_n_vars) =
        compute_chunks::<F, EF>(dims, log_smallest_decomposition_chunk);

    let packed_polynomial = F::zero_vec(1 << packed_n_vars); // TODO avoid this huge cloning of all witness data
    chunks_decomposition
        .values()
        .flatten()
        .collect::<Vec<_>>()
        .par_iter()
        .filter(|chunk| !chunk.public_data)
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
>(
    polynomials: &[&[F]],
    dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
    statements_per_polynomial: &[Vec<Evaluation<EF>>],
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
) -> Vec<Evaluation<EF>> {
    // TODO:
    // 2) cache the "eq" poly, and then use dot product
    // 4) current packing is not optimal in the end: can lead to [16][4][2][2] (instead of [16][8])
    // 5) opti in case of sparse point (containing boolean values) in statements

    let (chunks_decomposition, packed_vars) =
        compute_chunks::<F, EF>(dims, log_smallest_decomposition_chunk);

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
            let dim = &dims[*poly_index];
            let pol = polynomials[*poly_index];

            let chunks = &chunks_decomposition[&poly_index];
            assert!(!chunks.is_empty());
            let mut sub_packed_statements = Vec::new();
            let mut evals_to_send = Vec::new();
            if chunks.len() == 1 {
                assert!(!chunks[0].public_data, "TODO");
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
                // skip the first one, we will deduce it (if it's not public)
                for chunk in &chunks[1..] {
                    let missing_vars = statement.point.0.len() - chunk.n_vars;
                    let sub_point = MultilinearPoint(statement.point.0[missing_vars..].to_vec());
                    let sub_value = (&pol
                        [chunk.offset_in_original..chunk.offset_in_original + (1 << chunk.n_vars)])
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
                // deduce the first sub_value, if it's not public
                if dim.log_public.is_none() {
                    let mut retrieved_eval = EF::ZERO;
                    let mut chunk_offset_sums = 1 << chunks[0].n_vars;
                    assert_eq!(statement.point.len(), chunks[0].n_vars + 1);
                    for (chunk, &sub_value) in chunks[1..].iter().zip(&evals_to_send) {
                        let missing_vars = statement.point.0.len() - chunk.n_vars;
                        retrieved_eval += sub_value
                            * MultilinearPoint(statement.point.0[..missing_vars].to_vec())
                                .eq_poly_outside(&MultilinearPoint(
                                    chunk.bits_offset_in_original(),
                                ));
                        chunk_offset_sums += 1 << chunk.n_vars;
                    }
                    retrieved_eval +=
                        multilinear_eval_constants_at_right(chunk_offset_sums, &statement.point)
                            * dim.default_value;

                    let initial_missing_vars = statement.point.0.len() - chunks[0].n_vars;
                    let initial_sub_value = (statement.value - retrieved_eval)
                        / MultilinearPoint(statement.point.0[..initial_missing_vars].to_vec())
                            .eq_poly_outside(&MultilinearPoint(
                                chunks[0].bits_offset_in_original(),
                            ));
                    let initial_sub_point =
                        MultilinearPoint(statement.point.0[initial_missing_vars..].to_vec());

                    let initial_packed_point = MultilinearPoint(
                        [
                            to_big_endian_in_field(
                                chunks[0].offset_in_packed.unwrap() >> chunks[0].n_vars,
                                packed_vars - chunks[0].n_vars,
                            ),
                            initial_sub_point.0.clone(),
                        ]
                        .concat(),
                    );
                    sub_packed_statements.insert(
                        0,
                        Evaluation {
                            point: initial_packed_point,
                            value: initial_sub_value,
                        },
                    );
                    evals_to_send.insert(0, initial_sub_value);
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
    dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
) -> Result<Pcs::ParsedCommitment, ProofError> {
    let (_, packed_n_vars) = compute_chunks::<F, EF>(&dims, log_smallest_decomposition_chunk);
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
    public_data: &BTreeMap<usize, Vec<F>>, // poly_index -> public data slice (power of 2)
) -> Result<Vec<Evaluation<EF>>, ProofError> {
    assert_eq!(dims.len(), statements_per_polynomial.len());
    let (chunks_decomposition, packed_n_vars) =
        compute_chunks::<F, EF>(dims, log_smallest_decomposition_chunk);
    let mut packed_statements = Vec::new();
    for (poly_index, statements) in statements_per_polynomial.iter().enumerate() {
        let dim = &dims[poly_index];
        let has_public_data = dim.log_public.is_some();
        let chunks = &chunks_decomposition[&poly_index];
        assert!(!chunks.is_empty());
        for statement in statements {
            if chunks.len() == 1 {
                assert!(!chunks[0].public_data, "TODO");
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
                let mut sub_values = vec![];
                let n_received_values = if has_public_data {
                    sub_values.push(public_data[&poly_index].evaluate(&MultilinearPoint(
                        from_end(&statement.point, chunks[0].n_vars).to_vec(),
                    )));
                    chunks.len() - 1
                } else {
                    chunks.len()
                };
                sub_values.extend(verifier_state.next_extension_scalars_vec(n_received_values)?); // TODO we could send less data (1 EF less)

                for (chunk, &sub_value) in chunks.iter().zip(&sub_values) {
                    if chunk.public_data {
                        continue;
                    }
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
                    for (i, chunk) in chunks.iter().enumerate() {
                        let missing_vars = statement.point.0.len() - chunk.n_vars;
                        retrieved_eval += sub_values[i]
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
    use p3_util::log2_strict_usize;
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
        let committed_length_lengths_and_default_value_and_log_public_data: [(
            usize,
            F,
            Option<usize>,
        ); _] = [
            (16, F::from_usize(8), Some(4)),
            (854, F::from_usize(0), Some(7)),
            (854, F::from_usize(1), Some(5)),
            (16, F::from_usize(0), Some(3)),
            (17, F::from_usize(0), Some(4)),
            (95, F::from_usize(3), Some(4)),
            (17, F::from_usize(0), None),
            (95, F::from_usize(3), None),
            (256, F::from_usize(8), None),
            (1088, F::from_usize(9), None),
            (512, F::from_usize(0), None),
            (256, F::from_usize(8), Some(3)),
            (1088, F::from_usize(9), Some(4)),
            (512, F::from_usize(0), Some(5)),
            (754, F::from_usize(4), Some(4)),
            (1023, F::from_usize(7), Some(4)),
            (2025, F::from_usize(11), Some(8)),
            (16, F::from_usize(8), None),
            (854, F::from_usize(0), None),
            (854, F::from_usize(1), None),
            (16, F::from_usize(0), None),
            (754, F::from_usize(4), None),
            (1023, F::from_usize(7), None),
            (2025, F::from_usize(11), None),
        ];
        let mut public_data = BTreeMap::new();
        let mut polynomials = Vec::new();
        let mut dims = Vec::new();
        let mut statements_per_polynomial = Vec::new();
        for (pol_index, &(committed_length, default_value, log_public_data)) in
            committed_length_lengths_and_default_value_and_log_public_data
                .iter()
                .enumerate()
        {
            let mut poly = (0..committed_length + log_public_data.map_or(0, |l| 1 << l))
                .map(|_| rng.random())
                .collect::<Vec<F>>();
            poly.resize(poly.len().next_power_of_two(), default_value);
            if let Some(log_public) = log_public_data {
                public_data.insert(pol_index, poly[..1 << log_public].to_vec());
            }
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
                log_public: log_public_data,
                n_committed: committed_length,
                default_value,
            });
            statements_per_polynomial.push(statements);
        }

        let mut prover_state = build_prover_state();
        let dft = EvalsDft::<F>::default();

        let polynomials_ref = polynomials.iter().map(|p| p.as_slice()).collect::<Vec<_>>();
        let witness = packed_pcs_commit(
            &pcs,
            &polynomials_ref,
            &dims,
            &dft,
            &mut prover_state,
            log_smallest_decomposition_chunk,
        );

        let packed_statements = packed_pcs_global_statements_for_prover(
            &polynomials_ref,
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
            &public_data,
        )
        .unwrap();
        pcs.verify(&mut verifier_state, &parsed_commitment, &packed_statements)
            .unwrap();
    }
}
