use std::{cmp::Reverse, collections::BTreeMap};

use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_util::{log2_ceil_usize, log2_strict_usize};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::instrument;
use utils::{
    FSProver, FSVerifier, MY_DIGEST_ELEMS, MerkleCompress, MerkleHasher, PF, WhirParsedCommitment,
    WhirWitness, from_end, multilinear_eval_constants_at_right, to_big_endian_bits,
    to_big_endian_in_field,
};
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::Evaluation;
use whir_p3::whir::config::{WhirConfig, WhirConfigBuilder};
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::multilinear::MultilinearPoint,
};

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

impl Chunk {
    fn global_point_for_statement<F: Field>(
        &self,
        point: &[F],
        packed_n_vars: usize,
    ) -> MultilinearPoint<F> {
        MultilinearPoint(
            [
                to_big_endian_in_field(
                    self.offset_in_packed.unwrap() >> self.n_vars,
                    packed_n_vars - self.n_vars,
                ),
                point.to_vec(),
            ]
            .concat(),
        )
    }
}

/*
General layout: [public data][committed data][repeated value] (the thing has length 2^n_vars, public data is a power of two)
*/
#[derive(Debug, Clone, Copy)]
pub struct ColDims<F: Field> {
    pub n_vars: usize,
    pub log_public_data_size: Option<usize>,
    pub committed_size: usize,
    pub default_value: F,
}

impl<F: Field> ColDims<F> {
    pub fn full(n_vars: usize) -> Self {
        Self {
            n_vars,
            log_public_data_size: None,
            committed_size: 1 << n_vars,
            default_value: F::ZERO,
        }
    }

    pub fn padded(committed_size: usize, default_value: F) -> Self {
        Self::padded_with_public_data(None, committed_size, default_value)
    }

    pub fn padded_with_public_data(
        log_public_data_size: Option<usize>,
        committed_size: usize,
        default_value: F,
    ) -> Self {
        let public_data_size = log_public_data_size.map_or(0, |l| 1 << l);
        let n_vars = log2_ceil_usize(public_data_size + committed_size);
        Self {
            n_vars,
            log_public_data_size,
            committed_size,
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
    if let Some(log_public) = dims.log_public_data_size {
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
    let mut remaining = dims.committed_size;

    loop {
        let mut chunk_size =
            if remaining.next_power_of_two() - remaining <= 1 << log_smallest_decomposition_chunk {
                log2_ceil_usize(remaining)
            } else {
                remaining.ilog2() as usize
            };
        if let Some(log_public) = dims.log_public_data_size {
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

fn compute_chunks<F: Field>(
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

pub fn num_packed_vars_for_dims<F: Field>(
    dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
) -> usize {
    let (_, packed_n_vars) = compute_chunks::<F>(dims, log_smallest_decomposition_chunk);
    packed_n_vars
}

#[derive(Debug)]
pub struct MultiCommitmentWitness<F: Field, EF: ExtensionField<F>> {
    pub inner_witness: WhirWitness<F, EF>,
    pub packed_polynomial: Vec<F>,
}

#[instrument(skip_all)]
pub fn packed_pcs_commit<F, EF, H, C>(
    whir_config_builder: &WhirConfigBuilder<H, C, MY_DIGEST_ELEMS>,
    polynomials: &[&[F]],
    dims: &[ColDims<F>],
    dft: &EvalsDft<PF<EF>>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    log_smallest_decomposition_chunk: usize,
) -> MultiCommitmentWitness<F, EF>
where
    F: Field + TwoAdicField + ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + ExtensionField<PF<EF>>,
    H: MerkleHasher<EF>,
    C: MerkleCompress<EF>,
    [PF<EF>; MY_DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
{
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
        compute_chunks::<F>(dims, log_smallest_decomposition_chunk);

    {
        // logging
        let total_commited_data: usize = dims.iter().map(|d| d.committed_size).sum();
        let packed_commited_data: usize = chunks_decomposition
            .values()
            .flatten()
            .filter(|c| !c.public_data)
            .map(|c| 1 << c.n_vars)
            .sum();

        tracing::info!(
            "Total committed data (full granularity): {} = 2^{:.3} | packed to 2^{:.3} -> 2^{}",
            total_commited_data,
            (total_commited_data as f64).log2(),
            (packed_commited_data as f64).log2(),
            packed_n_vars
        );
    }

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

    let inner_witness = WhirConfig::new(whir_config_builder.clone(), packed_n_vars).commit(
        dft,
        prover_state,
        &packed_polynomial,
    );
    MultiCommitmentWitness {
        inner_witness,
        packed_polynomial,
    }
}

#[instrument(skip_all)]
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
    // - cache the "eq" poly, and then use dot product
    // - current packing is not optimal in the end: can lead to [16][4][2][2] (instead of [16][8])

    let (chunks_decomposition, packed_vars) =
        compute_chunks::<F>(dims, log_smallest_decomposition_chunk);

    let statements_flattened = statements_per_polynomial
        .iter()
        .enumerate()
        .flat_map(|(poly_index, poly_statements)| {
            poly_statements
                .iter()
                .map(move |statement| (poly_index, statement))
        })
        .collect::<Vec<_>>();

    let sub_packed_statements_and_evals_to_send = statements_flattened
        .par_iter()
        .map(|(poly_index, statement)| {
            let dim = &dims[*poly_index];
            let pol = polynomials[*poly_index];

            let chunks = chunks_decomposition
                .get(poly_index)
                .expect("missing chunk definition for polynomial");
            assert!(!chunks.is_empty());
            let mut sub_packed_statements = Vec::new();
            let mut evals_to_send = Vec::new();
            if chunks.len() == 1 {
                assert!(!chunks[0].public_data, "TODO");
                assert_eq!(
                    chunks[0].n_vars,
                    statement.point.0.len(),
                    "poly: {poly_index}"
                );
                assert!(chunks[0].offset_in_packed.unwrap() % (1 << chunks[0].n_vars) == 0);

                sub_packed_statements.push(Evaluation::new(
                    chunks[0].global_point_for_statement(&statement.point, packed_vars),
                    statement.value,
                ));
            } else {
                let initial_booleans = statement
                    .point
                    .iter()
                    .take_while(|&&x| x == EF::ZERO || x == EF::ONE)
                    .map(|&x| x == EF::ONE)
                    .collect::<Vec<_>>();
                let mut all_chunk_evals = Vec::new();

                // skip the first one, we will deduce it (if it's not public)
                // TODO do we really need to parallelize this?
                chunks[1..]
                    .par_iter()
                    .map(|chunk| {
                        let missing_vars = statement.point.0.len() - chunk.n_vars;

                        let offset_in_original_booleans = to_big_endian_bits(
                            chunk.offset_in_original >> chunk.n_vars,
                            missing_vars,
                        );

                        if !initial_booleans.is_empty()
                            && initial_booleans.len() < offset_in_original_booleans.len()
                            && initial_booleans
                                == offset_in_original_booleans[..initial_booleans.len()]
                        {
                            tracing::warn!("TODO: sparse statement accroos mutiple chunks");
                        }

                        if initial_booleans.len() >= offset_in_original_booleans.len() {
                            if initial_booleans[..missing_vars] != offset_in_original_booleans {
                                // this chunk is not concerned by this sparse evaluation
                                return (None, EF::ZERO);
                            } else {
                                // the evaluation only depends on this chunk, no need to recompute and  = statement.value
                                return (None, statement.value);
                            }
                        }

                        let sub_point =
                            MultilinearPoint(statement.point.0[missing_vars..].to_vec());
                        let sub_value = (&pol[chunk.offset_in_original
                            ..chunk.offset_in_original + (1 << chunk.n_vars)])
                            .evaluate(&sub_point);
                        (
                            Some(Evaluation::new(
                                chunk.global_point_for_statement(&sub_point, packed_vars),
                                sub_value,
                            )),
                            sub_value,
                        )
                    })
                    .collect::<Vec<_>>()
                    .into_iter()
                    .for_each(|(statement, sub_value)| {
                        if let Some(statement) = statement {
                            evals_to_send.push(statement.value);
                            sub_packed_statements.push(statement);
                        }
                        all_chunk_evals.push(sub_value);
                    });

                // deduce the first sub_value, if it's not public
                if dim.log_public_data_size.is_none() {
                    let retrieved_eval = compute_multilinear_value_from_chunks(
                        &chunks[1..],
                        &all_chunk_evals,
                        &statement.point,
                        1 << chunks[0].n_vars,
                        dim.default_value,
                    );

                    let initial_missing_vars = statement.point.0.len() - chunks[0].n_vars;
                    let initial_sub_value = (statement.value - retrieved_eval)
                        / MultilinearPoint(statement.point.0[..initial_missing_vars].to_vec())
                            .eq_poly_outside(&MultilinearPoint(
                                chunks[0].bits_offset_in_original(),
                            ));
                    let initial_sub_point =
                        MultilinearPoint(statement.point.0[initial_missing_vars..].to_vec());

                    let initial_packed_point =
                        chunks[0].global_point_for_statement(&initial_sub_point, packed_vars);
                    sub_packed_statements
                        .insert(0, Evaluation::new(initial_packed_point, initial_sub_value));
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

pub fn packed_pcs_parse_commitment<
    F: Field + TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + ExtensionField<PF<EF>>,
    H: MerkleHasher<EF>,
    C: MerkleCompress<EF>,
>(
    whir_config_builder: &WhirConfigBuilder<H, C, MY_DIGEST_ELEMS>,
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    dims: &[ColDims<F>],
    log_smallest_decomposition_chunk: usize,
) -> Result<WhirParsedCommitment<F, EF>, ProofError> {
    let (_, packed_n_vars) = compute_chunks::<F>(dims, log_smallest_decomposition_chunk);
    WhirConfig::new(whir_config_builder.clone(), packed_n_vars).parse_commitment(verifier_state)
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
        compute_chunks::<F>(dims, log_smallest_decomposition_chunk);
    let mut packed_statements = Vec::new();
    for (poly_index, statements) in statements_per_polynomial.iter().enumerate() {
        let dim = &dims[poly_index];
        let has_public_data = dim.log_public_data_size.is_some();
        let chunks = chunks_decomposition
            .get(&poly_index)
            .expect("missing chunk definition for polynomial");
        assert!(!chunks.is_empty());
        for statement in statements {
            if chunks.len() == 1 {
                assert!(!chunks[0].public_data, "TODO");
                assert_eq!(chunks[0].n_vars, statement.point.0.len());
                assert!(chunks[0].offset_in_packed.unwrap() % (1 << chunks[0].n_vars) == 0);
                packed_statements.push(Evaluation::new(
                    chunks[0].global_point_for_statement(&statement.point, packed_n_vars),
                    statement.value,
                ));
            } else {
                let initial_booleans = statement
                    .point
                    .iter()
                    .take_while(|&&x| x == EF::ZERO || x == EF::ONE)
                    .map(|&x| x == EF::ONE)
                    .collect::<Vec<_>>();
                let mut sub_values = vec![];
                if has_public_data {
                    sub_values.push(public_data[&poly_index].evaluate(&MultilinearPoint(
                        from_end(&statement.point, chunks[0].n_vars).to_vec(),
                    )));
                }
                for chunk in chunks {
                    if chunk.public_data {
                        continue;
                    }
                    let missing_vars = statement.point.0.len() - chunk.n_vars;
                    let offset_in_original_booleans =
                        to_big_endian_bits(chunk.offset_in_original >> chunk.n_vars, missing_vars);

                    if initial_booleans.len() >= offset_in_original_booleans.len() {
                        if initial_booleans[..missing_vars] != offset_in_original_booleans {
                            // this chunk is not concerned by this sparse evaluation
                            sub_values.push(EF::ZERO);
                        } else {
                            // the evaluation only depends on this chunk, no need to recompute and  = statement.value
                            sub_values.push(statement.value);
                        }
                    } else {
                        let sub_value = verifier_state.next_extension_scalar()?;
                        sub_values.push(sub_value);
                        let sub_point =
                            MultilinearPoint(statement.point.0[missing_vars..].to_vec());
                        packed_statements.push(Evaluation::new(
                            chunk.global_point_for_statement(&sub_point, packed_n_vars),
                            sub_value,
                        ));
                    }
                }
                // consistency check
                if statement.value
                    != compute_multilinear_value_from_chunks(
                        chunks,
                        &sub_values,
                        &statement.point,
                        0,
                        dim.default_value,
                    )
                {
                    return Err(ProofError::InvalidProof);
                }
            }
        }
    }
    Ok(packed_statements)
}

fn compute_multilinear_value_from_chunks<F: Field, EF: ExtensionField<F>>(
    chunks: &[Chunk],
    evals_per_chunk: &[EF],
    point: &[EF],
    size_of_first_chunk_mising: usize,
    default_value: F,
) -> EF {
    assert_eq!(chunks.len(), evals_per_chunk.len());
    let mut eval = EF::ZERO;

    let mut chunk_offset_sums = size_of_first_chunk_mising;
    for (chunk, &sub_value) in chunks.iter().zip(evals_per_chunk) {
        let missing_vars = point.len() - chunk.n_vars;
        eval += sub_value
            * MultilinearPoint(point[..missing_vars].to_vec())
                .eq_poly_outside(&MultilinearPoint(chunk.bits_offset_in_original()));
        chunk_offset_sums += 1 << chunk.n_vars;
    }
    eval += multilinear_eval_constants_at_right(chunk_offset_sums, point) * default_value;
    eval
}

#[cfg(test)]
mod tests {
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
        let whir_config_builder = WhirConfigBuilder {
            folding_factor: FoldingFactor::new(4, 4),
            soundness_type: SecurityAssumption::CapacityBound,
            merkle_hash: build_merkle_hash(),
            merkle_compress: build_merkle_compress(),
            pow_bits: 13,
            max_num_variables_to_send_coeffs: 6,
            rs_domain_initial_reduction_factor: 1,
            security_level: 75,
            starting_log_inv_rate: 1,
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
                log_public_data_size: log_public_data,
                committed_size: committed_length,
                default_value,
            });
            statements_per_polynomial.push(statements);
        }

        let mut prover_state = build_prover_state();
        let dft = EvalsDft::<F>::default();

        let polynomials_ref = polynomials.iter().map(|p| p.as_slice()).collect::<Vec<_>>();
        let witness = packed_pcs_commit(
            &whir_config_builder,
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
        let num_variables = log2_strict_usize(witness.packed_polynomial.len());
        WhirConfig::new(whir_config_builder.clone(), num_variables).prove(
            &dft,
            &mut prover_state,
            packed_statements,
            witness.inner_witness,
            &witness.packed_polynomial,
        );

        let mut verifier_state = build_verifier_state(&prover_state);

        let parsed_commitment = packed_pcs_parse_commitment(
            &whir_config_builder,
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
        WhirConfig::new(whir_config_builder, num_variables)
            .verify(&mut verifier_state, &parsed_commitment, packed_statements)
            .unwrap();
    }
}
