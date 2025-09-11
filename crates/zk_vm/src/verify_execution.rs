use crate::common::*;
use crate::*;
use ::air::table::AirTable;
use ::air::verify_many_air_2;
use lookup::verify_gkr_product;
use lookup::verify_logup_star;
use p3_air::BaseAir;
use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use pcs::num_packed_vars_for_vars;
use pcs::packed_pcs_global_statements;
use pcs::{BatchPCS, NumVariables as _, packed_pcs_parse_commitment};
use sumcheck::SumcheckComputation;
use utils::dot_product_with_base;
use utils::to_big_endian_bits;
use utils::{Evaluation, PF, build_challenger, padd_with_zero_to_next_power_of_two};
use utils::{ToUsize, build_poseidon_16_air, build_poseidon_24_air};
use vm::*;
use whir_p3::fiat_shamir::{errors::ProofError, verifier::VerifierState};
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::MultilinearPoint;
use zk_vm_air::*;

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof_data: Vec<PF<EF>>,
    pcs: &impl BatchPCS<PF<EF>, EF, EF>,
) -> Result<(), ProofError> {
    let mut verifier_state = VerifierState::new(proof_data, build_challenger());

    let exec_table = AirTable::<EF, _, _>::new(VMAir, VMAir);
    let p16_air = build_poseidon_16_air();
    let p24_air = build_poseidon_24_air();
    let p16_air_packed = build_poseidon_16_air_packed();
    let p24_air_packed = build_poseidon_24_air_packed();
    let p16_table = AirTable::<EF, _, _>::new(p16_air.clone(), p16_air_packed);
    let p24_table = AirTable::<EF, _, _>::new(p24_air.clone(), p24_air_packed);
    let dot_product_table = AirTable::<EF, _, _>::new(DotProductAir, DotProductAir);

    let [
        log_n_cycles,
        n_poseidons_16,
        n_poseidons_24,
        n_dot_products,
        table_dot_products_log_n_rows,
        dot_product_padding_len,
        private_memory_len,
        n_vm_multilinear_evals,
    ] = verifier_state
        .next_base_scalars_const::<8>()?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    if log_n_cycles > 32
        || n_poseidons_16 > 1 << 32
        || n_poseidons_24 > 1 << 32
        || n_dot_products > 1 << 32
        || table_dot_products_log_n_rows > 32
        || private_memory_len > 1 << 32
        || dot_product_padding_len > 1 << table_dot_products_log_n_rows
        || n_vm_multilinear_evals > 1 << 10
    {
        // To avoid "DOS" attack
        return Err(ProofError::InvalidProof);
    }
    let n_cycles = 1 << log_n_cycles;

    let public_memory = build_public_memory(public_input);
    let public_memory_len = public_memory.len();
    if private_memory_len % public_memory_len != 0 {
        return Err(ProofError::InvalidProof);
    }
    let n_private_memory_chunks = private_memory_len / public_memory_len;
    let log_public_memory = log2_strict_usize(public_memory_len);
    let log_memory = log2_ceil_usize(public_memory_len + private_memory_len);
    let log_n_p16 = log2_ceil_usize(n_poseidons_16);
    let log_n_p24 = log2_ceil_usize(n_poseidons_24);

    let vars_p16_indexes = log_n_p16 + 2;
    let vars_p24_indexes = log_n_p24 + 2;

    let vars_p16_table = log_n_p16 + log2_ceil_usize(p16_air.width() - 16 * 2);
    let vars_p24_table = log_n_p24 + log2_ceil_usize(p24_air.width() - 24 * 2);

    let vars_private_memory = vec![log_public_memory; n_private_memory_chunks];

    struct RowMultilinearEval {
        addr_coeffs: F,
        addr_point: F,
        addr_res: F,
        n_vars: F,
        point: Vec<EF>,
        res: EF,
    }

    let mut vm_multilinear_evals = Vec::new();
    for _ in 0..n_vm_multilinear_evals {
        let [addr_coeffs, addr_point, addr_res, n_vars] =
            verifier_state.next_base_scalars_const::<4>()?;
        let point = verifier_state.next_extension_scalars_vec(n_vars.to_usize())?;
        let res = verifier_state.next_extension_scalar()?;
        vm_multilinear_evals.push(RowMultilinearEval {
            addr_coeffs,
            addr_point,
            addr_res,
            n_vars,
            point,
            res,
        });
    }

    let mut private_memory_statements = vec![vec![]; n_private_memory_chunks];
    for row_multilinear_eval in &vm_multilinear_evals {
        let addr_point = row_multilinear_eval.addr_point.to_usize();
        let addr_coeffs = row_multilinear_eval.addr_coeffs.to_usize();
        let addr_res = row_multilinear_eval.addr_res.to_usize();
        let n_vars = row_multilinear_eval.n_vars.to_usize();

        // TODO only 1 statement for the evaluation point (instead of `n_vars` ones)
        // TODO we can group together most of the equality constraints (by chuncks alligned on powers of 2)
        for (ef_addr, ef_value) in row_multilinear_eval
            .point
            .iter()
            .enumerate()
            .map(|(i, p)| (addr_point + i * DIMENSION, *p))
            .chain(std::iter::once((addr_res, row_multilinear_eval.res)))
        {
            for (f_address, f_value) in
                <EF as BasedVectorSpace<PF<EF>>>::as_basis_coefficients_slice(&ef_value)
                    .iter()
                    .enumerate()
                    .map(|(a, v)| (ef_addr + a, *v))
            {
                let memory_chunk_index =
                    f_address >> (log_memory - log2_ceil_usize(n_private_memory_chunks + 1));
                let addr_bits = &to_big_endian_bits(
                    f_address,
                    log_memory - log2_ceil_usize(n_private_memory_chunks + 1),
                );
                let memory_sparse_point = addr_bits
                    .iter()
                    .map(|&x| EF::from_bool(x))
                    .collect::<Vec<_>>();
                let statement = Evaluation {
                    point: MultilinearPoint(memory_sparse_point),
                    value: EF::from(f_value), // TODO avoid embedding
                };
                if memory_chunk_index == 0 {
                    if public_memory.evaluate(&statement.point) != statement.value {
                        return Err(ProofError::InvalidProof);
                    }
                } else {
                    private_memory_statements[memory_chunk_index - 1].push(statement);
                }
            }
        }

        {
            if n_vars > log_memory {
                return Err(ProofError::InvalidProof);
            }
            if addr_coeffs >= 1 << (log_memory - n_vars) {
                return Err(ProofError::InvalidProof);
            }
            if n_vars >= log_public_memory {
                todo!("vm multilinear eval accross multiple memory chunks")
            }
            let memory_chunk_index =
                addr_coeffs >> (log_memory - n_vars - log2_ceil_usize(n_private_memory_chunks + 1));
            let addr_bits = &to_big_endian_bits(
                addr_coeffs,
                log_memory - n_vars - log2_ceil_usize(n_private_memory_chunks + 1),
            );
            let mut memory_sparse_point = addr_bits
                .iter()
                .map(|&x| EF::from_bool(x))
                .collect::<Vec<_>>();
            memory_sparse_point.extend(row_multilinear_eval.point.clone());
            let statement = Evaluation {
                point: MultilinearPoint(memory_sparse_point),
                value: row_multilinear_eval.res,
            };
            if memory_chunk_index == 0 {
                if public_memory.evaluate(&statement.point) != statement.value {
                    return Err(ProofError::InvalidProof);
                }
            } else {
                private_memory_statements[memory_chunk_index - 1].push(statement);
            }
        }
    }

    let vars_pcs_base = [
        vec![
            log_n_cycles, // pc
            log_n_cycles, // fp
            log_n_cycles, // index A
            log_n_cycles, // index B
            log_n_cycles, // index C
            vars_p16_indexes,
            vars_p24_indexes,
            vars_p16_table,
            vars_p24_table,
            table_dot_products_log_n_rows, // dot product: (start) flag
            table_dot_products_log_n_rows, // dot product: length
            table_dot_products_log_n_rows + 2, // dot product: indexes
        ],
        vec![table_dot_products_log_n_rows; DIMENSION], // dot product: computation
        vars_private_memory,
    ]
    .concat();

    let parsed_commitment_base =
        packed_pcs_parse_commitment(pcs.pcs_a(), &mut verifier_state, vars_pcs_base)?;

    let grand_product_challenge_global = verifier_state.sample();
    let grand_product_challenge_p16 = verifier_state.sample().powers().collect_n(5);
    let grand_product_challenge_p24 = verifier_state.sample().powers().collect_n(5);
    let grand_product_challenge_dot_product = verifier_state.sample().powers().collect_n(6);
    let grand_product_challenge_vm_multilinear_eval = verifier_state.sample().powers().collect_n(6);
    let (grand_product_exec_res, grand_product_exec_statement) =
        verify_gkr_product(&mut verifier_state, log_n_cycles)?;
    let (grand_product_p16_res, grand_product_p16_statement) =
        verify_gkr_product(&mut verifier_state, log2_ceil_usize(n_poseidons_16))?;
    let (grand_product_p24_res, grand_product_p24_statement) =
        verify_gkr_product(&mut verifier_state, log2_ceil_usize(n_poseidons_24))?;
    let (grand_product_dot_product_res, grand_product_dot_product_statement) =
        verify_gkr_product(&mut verifier_state, table_dot_products_log_n_rows)?;
    let vm_multilinear_eval_grand_product_res = vm_multilinear_evals
        .iter()
        .map(|vm_multilinear_eval| {
            grand_product_challenge_global
                + grand_product_challenge_vm_multilinear_eval[1]
                + grand_product_challenge_vm_multilinear_eval[2] * vm_multilinear_eval.addr_coeffs
                + grand_product_challenge_vm_multilinear_eval[3] * vm_multilinear_eval.addr_point
                + grand_product_challenge_vm_multilinear_eval[4] * vm_multilinear_eval.addr_res
                + grand_product_challenge_vm_multilinear_eval[5] * vm_multilinear_eval.n_vars
        })
        .product::<EF>();

    let corrected_prod_exec = grand_product_exec_res
        / grand_product_challenge_global.exp_u64(
            (n_cycles
                - n_poseidons_16
                - n_poseidons_24
                - n_dot_products
                - vm_multilinear_evals.len()) as u64,
        );
    let corrected_prod_p16 = grand_product_p16_res
        / (grand_product_challenge_global
            + grand_product_challenge_p16[1]
            + grand_product_challenge_p16[4] * F::from_usize(POSEIDON_16_NULL_HASH_PTR))
        .exp_u64((n_poseidons_16.next_power_of_two() - n_poseidons_16) as u64);

    let corrected_prod_p24 = grand_product_p24_res
        / (grand_product_challenge_global
            + grand_product_challenge_p24[1]
            + grand_product_challenge_p24[4] * F::from_usize(POSEIDON_24_NULL_HASH_PTR))
        .exp_u64((n_poseidons_24.next_power_of_two() - n_poseidons_24) as u64);

    let corrected_dot_product = grand_product_dot_product_res
        / ((grand_product_challenge_global
            + grand_product_challenge_dot_product[1]
            + grand_product_challenge_dot_product[5])
            .exp_u64(dot_product_padding_len as u64)
            * (grand_product_challenge_global + grand_product_challenge_dot_product[1]).exp_u64(
                ((1 << table_dot_products_log_n_rows) - dot_product_padding_len - n_dot_products)
                    as u64,
            ));

    if corrected_prod_exec
        != corrected_prod_p16
            * corrected_prod_p24
            * corrected_dot_product
            * vm_multilinear_eval_grand_product_res
    {
        return Err(ProofError::InvalidProof);
    }

    let [
        p16_grand_product_evals_on_indexes_a,
        p16_grand_product_evals_on_indexes_b,
        p16_grand_product_evals_on_indexes_res,
    ] = verifier_state.next_extension_scalars_const()?;
    if grand_product_challenge_global
        + grand_product_challenge_p16[1]
        + grand_product_challenge_p16[2] * p16_grand_product_evals_on_indexes_a
        + grand_product_challenge_p16[3] * p16_grand_product_evals_on_indexes_b
        + grand_product_challenge_p16[4] * p16_grand_product_evals_on_indexes_res
        != grand_product_p16_statement.value
    {
        return Err(ProofError::InvalidProof);
    }
    let p16_mixing_scalars_grand_product = MultilinearPoint(verifier_state.sample_vec(2));
    let p16_final_statement_grand_product = Evaluation {
        point: MultilinearPoint(
            [
                p16_mixing_scalars_grand_product.0.clone(),
                grand_product_p16_statement.point.0,
            ]
            .concat(),
        ),
        value: [
            p16_grand_product_evals_on_indexes_a,
            p16_grand_product_evals_on_indexes_b,
            p16_grand_product_evals_on_indexes_res,
            EF::ZERO,
        ]
        .evaluate(&p16_mixing_scalars_grand_product),
    };

    let [
        p24_grand_product_evals_on_indexes_a,
        p24_grand_product_evals_on_indexes_b,
        p24_grand_product_evals_on_indexes_res,
    ] = verifier_state.next_extension_scalars_const()?;
    if grand_product_challenge_global
        + grand_product_challenge_p24[1]
        + grand_product_challenge_p24[2] * p24_grand_product_evals_on_indexes_a
        + grand_product_challenge_p24[3] * p24_grand_product_evals_on_indexes_b
        + grand_product_challenge_p24[4] * p24_grand_product_evals_on_indexes_res
        != grand_product_p24_statement.value
    {
        return Err(ProofError::InvalidProof);
    }
    let p24_mixing_scalars_grand_product = MultilinearPoint(verifier_state.sample_vec(2));
    let p24_final_statement_grand_product = Evaluation {
        point: MultilinearPoint(
            [
                p24_mixing_scalars_grand_product.0.clone(),
                grand_product_p24_statement.point.0,
            ]
            .concat(),
        ),
        value: [
            p24_grand_product_evals_on_indexes_a,
            p24_grand_product_evals_on_indexes_b,
            p24_grand_product_evals_on_indexes_res,
            EF::ZERO,
        ]
        .evaluate(&p24_mixing_scalars_grand_product),
    };

    // Grand product statements
    let (grand_product_final_dot_product_eval, grand_product_dot_product_sumcheck_claim) =
        sumcheck::verify(&mut verifier_state, table_dot_products_log_n_rows, 3)?;
    if grand_product_final_dot_product_eval != grand_product_dot_product_statement.value {
        return Err(ProofError::InvalidProof);
    }
    let grand_product_dot_product_sumcheck_inner_evals =
        verifier_state.next_extension_scalars_vec(5)?;

    if grand_product_dot_product_sumcheck_claim.value
        != grand_product_dot_product_sumcheck_claim
            .point
            .eq_poly_outside(&grand_product_dot_product_statement.point)
            * {
                DotProductFootprint {
                    grand_product_challenge_global,
                    grand_product_challenge_dot_product: grand_product_challenge_dot_product
                        .clone()
                        .try_into()
                        .unwrap(),
                }
                .eval(&grand_product_dot_product_sumcheck_inner_evals, &[])
            }
    {
        return Err(ProofError::InvalidProof);
    }

    let grand_product_dot_product_flag_statement = Evaluation {
        point: grand_product_dot_product_sumcheck_claim.point.clone(),
        value: grand_product_dot_product_sumcheck_inner_evals[0],
    };
    let grand_product_dot_product_len_statement = Evaluation {
        point: grand_product_dot_product_sumcheck_claim.point.clone(),
        value: grand_product_dot_product_sumcheck_inner_evals[1],
    };
    let grand_product_dot_product_table_indexes_mixing_challenges =
        MultilinearPoint(verifier_state.sample_vec(2));
    let grand_product_dot_product_table_indexes_statement = Evaluation {
        point: MultilinearPoint(
            [
                grand_product_dot_product_table_indexes_mixing_challenges
                    .0
                    .clone(),
                grand_product_dot_product_sumcheck_claim.point.0,
            ]
            .concat(),
        ),
        value: [
            grand_product_dot_product_sumcheck_inner_evals[2],
            grand_product_dot_product_sumcheck_inner_evals[3],
            grand_product_dot_product_sumcheck_inner_evals[4],
            EF::ZERO,
        ]
        .evaluate(&grand_product_dot_product_table_indexes_mixing_challenges),
    };

    let (grand_product_final_exec_eval, grand_product_exec_sumcheck_claim) =
        sumcheck::verify(&mut verifier_state, log_n_cycles, 4)?;
    if grand_product_final_exec_eval != grand_product_exec_statement.value {
        return Err(ProofError::InvalidProof);
    }

    let grand_product_exec_sumcheck_inner_evals =
        verifier_state.next_extension_scalars_vec(N_TOTAL_COLUMNS)?;

    let grand_product_exec_evals_on_each_column =
        &grand_product_exec_sumcheck_inner_evals[..N_INSTRUCTION_COLUMNS];

    if grand_product_exec_sumcheck_claim.value
        != grand_product_exec_sumcheck_claim
            .point
            .eq_poly_outside(&grand_product_exec_statement.point)
            * {
                PrecompileFootprint {
                    grand_product_challenge_global,
                    grand_product_challenge_p16: grand_product_challenge_p16.try_into().unwrap(),
                    grand_product_challenge_p24: grand_product_challenge_p24.try_into().unwrap(),
                    grand_product_challenge_dot_product: grand_product_challenge_dot_product
                        .try_into()
                        .unwrap(),
                    grand_product_challenge_vm_multilinear_eval:
                        grand_product_challenge_vm_multilinear_eval
                            .try_into()
                            .unwrap(),
                }
                .eval(&grand_product_exec_sumcheck_inner_evals, &[])
            }
    {
        return Err(ProofError::InvalidProof);
    }

    let grand_product_fp_statement = Evaluation {
        point: grand_product_exec_sumcheck_claim.point.clone(),
        value: grand_product_exec_sumcheck_inner_evals[COL_INDEX_FP],
    };

    let exec_evals_to_verify = exec_table.verify(
        &mut verifier_state,
        UNIVARIATE_SKIPS,
        log_n_cycles,
        &exec_column_groups(),
    )?;

    let dot_product_evals_to_verify = dot_product_table.verify(
        &mut verifier_state,
        1,
        table_dot_products_log_n_rows,
        &DOT_PRODUCT_AIR_COLUMN_GROUPS,
    )?;

    let [p16_evals_to_verify, p24_evals_to_verify] = verify_many_air_2(
        &mut verifier_state,
        &[&p16_table],
        &[&p24_table],
        UNIVARIATE_SKIPS,
        &[log_n_p16, log_n_p24],
        &[
            poseidon_16_column_groups(&p16_air),
            poseidon_24_column_groups(&p24_air),
        ],
    )?
    .try_into()
    .unwrap();
    let memory_folding_challenges = MultilinearPoint(p16_evals_to_verify[0].point[..3].to_vec());

    // Poseidons 16/24 memory addresses lookup
    let poseidon_lookup_batching_chalenges = MultilinearPoint(verifier_state.sample_vec(3));

    let non_used_precompiles_evals = verifier_state
        .next_extension_scalars_vec(N_INSTRUCTION_COLUMNS - N_INSTRUCTION_COLUMNS_IN_AIR)?;
    let bytecode_compression_challenges =
        MultilinearPoint(verifier_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    for i in 1..N_INSTRUCTION_COLUMNS_IN_AIR {
        assert_eq!(
            &exec_evals_to_verify[0].point,
            &exec_evals_to_verify[i].point
        );
    }
    let bytecode_lookup_point_1 = exec_evals_to_verify[0].point.clone();
    let bytecode_lookup_claim_1 = Evaluation {
        point: bytecode_lookup_point_1,
        value: padd_with_zero_to_next_power_of_two(
            &[
                (0..N_INSTRUCTION_COLUMNS_IN_AIR)
                    .map(|i| exec_evals_to_verify[i].value)
                    .collect::<Vec<_>>(),
                non_used_precompiles_evals,
            ]
            .concat(),
        )
        .evaluate(&bytecode_compression_challenges),
    };

    let bytecode_lookup_claim_2 = Evaluation {
        point: grand_product_exec_sumcheck_claim.point.clone(),
        value: padd_with_zero_to_next_power_of_two(grand_product_exec_evals_on_each_column)
            .evaluate(&bytecode_compression_challenges),
    };
    let alpha_bytecode_lookup = verifier_state.sample();

    let dot_product_evals_spread = verifier_state.next_extension_scalars_vec(DIMENSION)?;
    if dot_product_with_base(&dot_product_evals_spread) != dot_product_evals_to_verify[3].value {
        return Err(ProofError::InvalidProof);
    }
    let dot_product_values_batching_scalars = MultilinearPoint(verifier_state.sample_vec(3));
    let dot_product_values_batched_point = MultilinearPoint(
        [
            dot_product_values_batching_scalars.0.clone(),
            dot_product_evals_to_verify[3].point.0.clone(),
        ]
        .concat(),
    );
    let dot_product_values_batched_eval =
        padd_with_zero_to_next_power_of_two(&dot_product_evals_spread)
            .evaluate(&dot_product_values_batching_scalars);

    let unused_1 = verifier_state.next_extension_scalar()?;
    let grand_product_mem_values_mixing_challenges = MultilinearPoint(verifier_state.sample_vec(2));
    let base_memory_lookup_statement_1 = Evaluation {
        point: MultilinearPoint(
            [
                grand_product_mem_values_mixing_challenges.0.clone(),
                grand_product_exec_sumcheck_claim.point.0,
            ]
            .concat(),
        ),
        value: [
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_A],
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_B],
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_C],
            unused_1,
        ]
        .evaluate(&grand_product_mem_values_mixing_challenges),
    };

    let unused_2 = verifier_state.next_extension_scalar()?;
    let exec_air_mem_values_mixing_challenges = MultilinearPoint(verifier_state.sample_vec(2));
    let base_memory_lookup_statement_2 = Evaluation {
        point: MultilinearPoint(
            [
                exec_air_mem_values_mixing_challenges.0.clone(),
                exec_evals_to_verify[COL_INDEX_MEM_VALUE_A.index_in_air()]
                    .point
                    .0
                    .clone(),
            ]
            .concat(),
        ),
        value: [
            exec_evals_to_verify[COL_INDEX_MEM_VALUE_A.index_in_air()].value,
            exec_evals_to_verify[COL_INDEX_MEM_VALUE_B.index_in_air()].value,
            exec_evals_to_verify[COL_INDEX_MEM_VALUE_C.index_in_air()].value,
            unused_2,
        ]
        .evaluate(&exec_air_mem_values_mixing_challenges),
    };

    let [unused_3a, unused_3b, unused_3c] = verifier_state.next_extension_scalars_const()?;
    let dot_product_air_mem_values_mixing_challenges =
        MultilinearPoint(verifier_state.sample_vec(2));
    let base_memory_lookup_statement_3 = Evaluation {
        point: MultilinearPoint(
            [
                dot_product_air_mem_values_mixing_challenges.0.clone(),
                EF::zero_vec(log_n_cycles - dot_product_values_batched_point.len()),
                dot_product_values_batched_point.0.clone(),
            ]
            .concat(),
        ),
        value: [
            unused_3a,
            unused_3b,
            unused_3c,
            dot_product_values_batched_eval,
        ]
        .evaluate(&dot_product_air_mem_values_mixing_challenges),
    };
    let memory_poly_eq_point_alpha = verifier_state.sample();

    let log_bytecode_len = log2_ceil_usize(bytecode.instructions.len());
    let vars_pcs_extension = vec![log_memory, log_memory - 3, log_bytecode_len];
    let parsed_commitment_extension = packed_pcs_parse_commitment(
        &pcs.pcs_b(
            parsed_commitment_base
                .inner_parsed_commitment
                .num_variables(),
            num_packed_vars_for_vars(&vars_pcs_extension),
        ),
        &mut verifier_state,
        vars_pcs_extension,
    )
    .unwrap();

    let base_memory_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log_memory,
        log_n_cycles + 2,
        &[
            base_memory_lookup_statement_1,
            base_memory_lookup_statement_2,
            base_memory_lookup_statement_3,
        ],
        memory_poly_eq_point_alpha,
    )
    .unwrap();

    let mut poseidon_lookup_point = poseidon_lookup_batching_chalenges.0.clone();
    poseidon_lookup_point.extend_from_slice({
        if n_poseidons_16 > n_poseidons_24 {
            &p16_evals_to_verify[0].point[3..]
        } else {
            &p24_evals_to_verify[0].point[3..]
        }
    });
    let poseidon_lookup_value = poseidon_lookup_value(
        n_poseidons_16,
        n_poseidons_24,
        &p16_evals_to_verify,
        &p24_evals_to_verify,
        &poseidon_lookup_batching_chalenges,
    );
    let poseidon_lookup_challenge = Evaluation {
        point: MultilinearPoint(poseidon_lookup_point),
        value: poseidon_lookup_value,
    };
    let poseidon_lookup_log_length = 3 + log_n_p16.max(log_n_p24);
    let poseidon_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log_memory - 3, // "-3" because it's folded memory
        poseidon_lookup_log_length,
        &[poseidon_lookup_challenge],
        EF::ONE,
    )
    .unwrap();

    let bytecode_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log_bytecode_len,
        log_n_cycles,
        &[bytecode_lookup_claim_1, bytecode_lookup_claim_2],
        alpha_bytecode_lookup,
    )
    .unwrap();
    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);
    if folded_bytecode.evaluate(&bytecode_logup_star_statements.on_table.point)
        != bytecode_logup_star_statements.on_table.value
    {
        return Err(ProofError::InvalidProof);
    }

    let poseidon_lookup_memory_point = MultilinearPoint(
        [
            poseidon_logup_star_statements.on_table.point.0.clone(),
            memory_folding_challenges.0,
        ]
        .concat(),
    );

    let exec_lookup_chunk_point = MultilinearPoint(
        base_memory_logup_star_statements.on_table.point[log_memory - log_public_memory..].to_vec(),
    );
    let poseidon_lookup_chunk_point =
        MultilinearPoint(poseidon_lookup_memory_point[log_memory - log_public_memory..].to_vec());

    let mut chunk_evals_exec_lookup = vec![public_memory.evaluate(&exec_lookup_chunk_point)];
    let mut chunk_evals_poseidon_lookup =
        vec![public_memory.evaluate(&poseidon_lookup_chunk_point)];

    for i in 0..n_private_memory_chunks {
        let chunk_eval_exec_lookup = verifier_state.next_extension_scalar()?;
        let chunk_eval_poseidon_lookup = verifier_state.next_extension_scalar()?;
        chunk_evals_exec_lookup.push(chunk_eval_exec_lookup);
        chunk_evals_poseidon_lookup.push(chunk_eval_poseidon_lookup);
        private_memory_statements[i].extend(vec![
            Evaluation {
                point: exec_lookup_chunk_point.clone(),
                value: chunk_eval_exec_lookup,
            },
            Evaluation {
                point: poseidon_lookup_chunk_point.clone(),
                value: chunk_eval_poseidon_lookup,
            },
        ]);
    }

    if base_memory_logup_star_statements.on_table.value
        != padd_with_zero_to_next_power_of_two(&chunk_evals_exec_lookup).evaluate(
            &MultilinearPoint(
                base_memory_logup_star_statements.on_table.point[..log_memory - log_public_memory]
                    .to_vec(),
            ),
        )
    {
        return Err(ProofError::InvalidProof);
    }
    if poseidon_logup_star_statements.on_table.value
        != padd_with_zero_to_next_power_of_two(&chunk_evals_poseidon_lookup).evaluate(
            &MultilinearPoint(
                poseidon_logup_star_statements.on_table.point[..log_memory - log_public_memory]
                    .to_vec(),
            ),
        )
    {
        return Err(ProofError::InvalidProof);
    }

    // index opening for poseidon lookup
    let poseidon_index_evals = verifier_state.next_extension_scalars_vec(8)?;
    if poseidon_index_evals.evaluate(&MultilinearPoint(
        poseidon_logup_star_statements.on_indexes.point[..3].to_vec(),
    )) != poseidon_logup_star_statements.on_indexes.value
    {
        return Err(ProofError::InvalidProof);
    }

    let (mut p16_indexes_statements, mut p24_indexes_statements) =
        poseidon_lookup_index_statements(
            &poseidon_index_evals,
            n_poseidons_16,
            n_poseidons_24,
            &poseidon_logup_star_statements.on_indexes.point,
        )?;
    p16_indexes_statements.push(p16_final_statement_grand_product);
    p24_indexes_statements.push(p24_final_statement_grand_product);

    let (initial_pc_statement, final_pc_statement) =
        intitial_and_final_pc_conditions(bytecode, log_n_cycles);

    let dot_product_computation_column_evals =
        verifier_state.next_extension_scalars_const::<DIMENSION>()?;
    if dot_product_with_base(&dot_product_computation_column_evals)
        != dot_product_evals_to_verify[4].value
    {
        return Err(ProofError::InvalidProof);
    }
    let dot_product_computation_column_statements = (0..DIMENSION)
        .map(|i| {
            vec![Evaluation {
                point: dot_product_evals_to_verify[4].point.clone(),
                value: dot_product_computation_column_evals[i],
            }]
        })
        .collect::<Vec<_>>();

    let mem_lookup_eval_indexes_partial_point =
        MultilinearPoint(base_memory_logup_star_statements.on_indexes.point[2..].to_vec());
    let [
        mem_lookup_eval_indexes_a,
        mem_lookup_eval_indexes_b,
        mem_lookup_eval_indexes_c,
        mem_lookup_eval_spread_indexes_dot_product,
    ] = verifier_state.next_extension_scalars_const()?;

    let index_diff = log_n_cycles - (table_dot_products_log_n_rows + 5);

    assert_eq!(
        [
            mem_lookup_eval_indexes_a,
            mem_lookup_eval_indexes_b,
            mem_lookup_eval_indexes_c,
            mem_lookup_eval_spread_indexes_dot_product
                * mem_lookup_eval_indexes_partial_point[..index_diff]
                    .iter()
                    .map(|x| EF::ONE - *x)
                    .product::<EF>(),
        ]
        .evaluate(&MultilinearPoint(
            base_memory_logup_star_statements.on_indexes.point[..2].to_vec(),
        )),
        base_memory_logup_star_statements.on_indexes.value
    );

    let dot_product_logup_star_indexes_inner_point =
        MultilinearPoint(mem_lookup_eval_indexes_partial_point.0[3 + index_diff..].to_vec());
    let dot_product_logup_star_indexes_inner_value = verifier_state.next_extension_scalar()?;
    let dot_product_logup_star_indexes_inner_eval = Evaluation {
        point: dot_product_logup_star_indexes_inner_point,
        value: dot_product_logup_star_indexes_inner_value,
    };
    {
        let mut dot_product_indexes_inner_evals_incr = vec![EF::ZERO; 8];
        for i in 0..DIMENSION {
            dot_product_indexes_inner_evals_incr[i] = dot_product_logup_star_indexes_inner_value
                + EF::from_usize(i)
                    * [F::ONE, F::ONE, F::ONE, F::ZERO].evaluate(&MultilinearPoint(
                        mem_lookup_eval_indexes_partial_point.0[3 + index_diff..5 + index_diff]
                            .to_vec(),
                    ));
        }
        if dot_product_indexes_inner_evals_incr.evaluate(&MultilinearPoint(
            mem_lookup_eval_indexes_partial_point.0[index_diff..3 + index_diff].to_vec(),
        )) != mem_lookup_eval_spread_indexes_dot_product
        {
            return Err(ProofError::InvalidProof);
        }
    }

    let global_statements_base = packed_pcs_global_statements(
        &parsed_commitment_base.tree,
        &[
            vec![
                vec![
                    exec_evals_to_verify[COL_INDEX_PC.index_in_air()].clone(),
                    bytecode_logup_star_statements.on_indexes.clone(),
                    initial_pc_statement,
                    final_pc_statement,
                ], // pc
                vec![
                    exec_evals_to_verify[COL_INDEX_FP.index_in_air()].clone(),
                    grand_product_fp_statement,
                ], // fp
                vec![
                    exec_evals_to_verify[COL_INDEX_MEM_ADDRESS_A.index_in_air()].clone(),
                    Evaluation {
                        point: mem_lookup_eval_indexes_partial_point.clone(),
                        value: mem_lookup_eval_indexes_a,
                    },
                ], // exec memory address A
                vec![
                    exec_evals_to_verify[COL_INDEX_MEM_ADDRESS_B.index_in_air()].clone(),
                    Evaluation {
                        point: mem_lookup_eval_indexes_partial_point.clone(),
                        value: mem_lookup_eval_indexes_b,
                    },
                ], // exec memory address B
                vec![
                    exec_evals_to_verify[COL_INDEX_MEM_ADDRESS_C.index_in_air()].clone(),
                    Evaluation {
                        point: mem_lookup_eval_indexes_partial_point,
                        value: mem_lookup_eval_indexes_c,
                    },
                ], // exec memory address C
                p16_indexes_statements,
                p24_indexes_statements,
                vec![p16_evals_to_verify[2].clone()],
                vec![p24_evals_to_verify[3].clone()],
                vec![
                    dot_product_evals_to_verify[0].clone(),
                    grand_product_dot_product_flag_statement,
                ], // dot product: (start) flag
                vec![
                    dot_product_evals_to_verify[1].clone(),
                    grand_product_dot_product_len_statement,
                ], // dot product: length
                vec![
                    dot_product_evals_to_verify[2].clone(),
                    dot_product_logup_star_indexes_inner_eval,
                    grand_product_dot_product_table_indexes_statement,
                ], // dot product: indexes
            ],
            dot_product_computation_column_statements,
            private_memory_statements,
        ]
        .concat(),
    );

    let global_statements_extension = packed_pcs_global_statements(
        &parsed_commitment_extension.tree,
        &[
            base_memory_logup_star_statements.on_pushforward,
            poseidon_logup_star_statements.on_pushforward,
            bytecode_logup_star_statements.on_pushforward,
        ],
    );

    pcs.batch_verify(
        &mut verifier_state,
        &parsed_commitment_base.inner_parsed_commitment,
        &global_statements_base,
        &parsed_commitment_extension.inner_parsed_commitment,
        &global_statements_extension,
    )?;

    Ok(())
}
