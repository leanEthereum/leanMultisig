use std::collections::BTreeMap;

use crate::*;
use crate::{SnarkParams, common::*};
use air::verify_air;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use sub_protocols::verify_logup_star;
use sub_protocols::*;
use utils::ToUsize;
use whir_p3::{SparseStatement, SparseValue, WhirConfig};

#[derive(Debug, Clone)]
pub struct ProofVerificationDetails {
    pub log_memory: usize,
    pub table_log_n_vars: BTreeMap<Table, VarCount>,
    pub first_quotient_gkr_n_vars: usize,
}

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof: Vec<F>,
    params: &SnarkParams,
) -> Result<ProofVerificationDetails, ProofError> {
    let mut verifier_state = VerifierState::<EF, _>::new(proof, get_poseidon16().clone());
    verifier_state.duplexing();

    let dims = verifier_state
        .next_base_scalars_vec(1 + N_TABLES)?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>();
    let log_memory = dims[0];
    let table_n_vars: BTreeMap<Table, VarCount> = (0..N_TABLES).map(|i| (ALL_TABLES[i], dims[i + 1])).collect();
    for &n_vars in table_n_vars.values() {
        if !(MIN_LOG_N_ROWS_PER_TABLE..=MAX_LOG_N_ROWS_PER_TABLE).contains(&n_vars) {
            return Err(ProofError::InvalidProof);
        }
    }
    // check memory is bigger than any other table
    if log_memory < *table_n_vars.values().max().unwrap() {
        return Err(ProofError::InvalidProof);
    }

    let public_memory = build_public_memory(public_input);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    let parsed_commitment_base =
        packed_pcs_parse_commitment(&params.first_whir, &mut verifier_state, log_memory, &table_n_vars)?;

    let logup_c = verifier_state.sample();
    verifier_state.duplexing();
    let logup_alpha = verifier_state.sample();
    verifier_state.duplexing();

    let logup_statements = verify_generic_logup(
        &mut verifier_state,
        logup_c,
        logup_alpha,
        log_memory,
        &table_n_vars,
        UNIVARIATE_SKIPS,
    )?;

    let (mut air_points, mut air_evals) = (BTreeMap::new(), BTreeMap::new());
    for (table, log_n_rows) in &table_n_vars {
        let (this_air_point, this_air_evals) = verify_bus_and_air(
            &mut verifier_state,
            table,
            *log_n_rows,
            logup_c,
            logup_alpha,
            &logup_statements.bus_points[table],
            logup_statements.bus_numerators_values[table],
            logup_statements.bus_denominators_values[table],
        )?;
        air_points.insert(*table, this_air_point);
        air_evals.insert(*table, this_air_evals);
    }

    let bytecode_compression_challenges =
        MultilinearPoint(verifier_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let bytecode_lookup_claim = Evaluation::new(
        air_points[&Table::execution()].clone(),
        padd_with_zero_to_next_power_of_two(
            &air_evals[&Table::execution()][N_COMMITTED_EXEC_COLUMNS..][..N_INSTRUCTION_COLUMNS],
        )
        .evaluate(&bytecode_compression_challenges),
    );

    let bytecode_pushforward_parsed_commitment =
        WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len()))
            .parse_commitment::<EF>(&mut verifier_state)?;

    let bytecode_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log2_ceil_usize(bytecode.instructions.len()),
        table_n_vars[&Table::execution()],
        &[bytecode_lookup_claim],
        EF::ONE,
    )?;
    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);
    if folded_bytecode.evaluate(&bytecode_logup_star_statements.on_table.point)
        != bytecode_logup_star_statements.on_table.value
    {
        return Err(ProofError::InvalidProof);
    }

    let mut committed_statements: CommittedStatements = Default::default();
    for table in ALL_TABLES {
        let table_statements = vec![
            (
                air_points[&table].clone(),
                table.commited_air_values(&air_evals[&table]),
            ),
            (
                logup_statements.columns_points[&table].clone(),
                logup_statements.columns_values[&table].clone(),
            ),
        ];
        committed_statements.insert(table, table_statements);
    }

    committed_statements.get_mut(&Table::execution()).unwrap().push((
        bytecode_logup_star_statements.on_indexes.point.clone(),
        BTreeMap::from_iter([(COL_INDEX_PC, bytecode_logup_star_statements.on_indexes.value)]),
    ));

    let public_memory_random_point =
        MultilinearPoint(verifier_state.sample_vec(log2_strict_usize(public_memory.len())));
    verifier_state.duplexing();
    let public_memory_eval = public_memory.evaluate(&public_memory_random_point);

    let memory_acc_statements = vec![
        SparseStatement::new(
            parsed_commitment_base.num_variables,
            logup_statements.memory_acc_point,
            vec![
                SparseValue::new(0, logup_statements.value_memory),
                SparseValue::new(1, logup_statements.value_acc),
            ],
        ),
        SparseStatement::new(
            parsed_commitment_base.num_variables,
            public_memory_random_point,
            vec![SparseValue::new(0, public_memory_eval)],
        ),
    ];

    let global_statements_base = packed_pcs_global_statements(
        parsed_commitment_base.num_variables,
        log_memory,
        memory_acc_statements,
        &table_n_vars,
        &committed_statements,
    );

    WhirConfig::new(&params.first_whir, parsed_commitment_base.num_variables).verify(
        &mut verifier_state,
        &parsed_commitment_base,
        global_statements_base,
    )?;

    WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len())).verify(
        &mut verifier_state,
        &bytecode_pushforward_parsed_commitment,
        bytecode_logup_star_statements
            .on_pushforward
            .into_iter()
            .map(|smt| SparseStatement::dense(smt.point, smt.value))
            .collect::<Vec<_>>(),
    )?;

    Ok(ProofVerificationDetails {
        log_memory,
        table_log_n_vars: table_n_vars,
        first_quotient_gkr_n_vars: logup_statements.total_n_vars,
    })
}

#[allow(clippy::too_many_arguments)]
fn verify_bus_and_air(
    verifier_state: &mut impl FSVerifier<EF>,
    table: &Table,
    log_n_nrows: usize,
    logup_c: EF,
    logup_alpha: EF,
    bus_point: &MultilinearPoint<EF>,
    bus_numerator_value: EF,
    bus_denominator_value: EF,
) -> ProofResult<(MultilinearPoint<EF>, Vec<EF>)> {
    let bus_beta = verifier_state.sample();
    verifier_state.duplexing();

    let bus_final_value = bus_numerator_value
        * match table.bus().direction {
            BusDirection::Pull => EF::NEG_ONE,
            BusDirection::Push => EF::ONE,
        }
        + bus_beta * (bus_denominator_value - logup_c);

    let bus_virtual_statement = Evaluation::new(bus_point.clone(), bus_final_value);

    let extra_data = ExtraDataForBuses {
        logup_alpha_powers: logup_alpha.powers().collect_n(max_bus_width()),
        logup_alpha_powers_packed: EFPacking::<EF>::from(logup_alpha).powers().collect_n(max_bus_width()),
        bus_beta,
        bus_beta_packed: EFPacking::<EF>::from(bus_beta),
        alpha_powers: vec![], // filled later
    };

    let (air_point, mut evals_f, evals_ef) = {
        macro_rules! verify_air_for_table {
            ($t:expr) => {
                verify_air(
                    verifier_state,
                    $t,
                    extra_data,
                    UNIVARIATE_SKIPS,
                    log_n_nrows,
                    &table.air_padding_row_f(),
                    &table.air_padding_row_ef(),
                    Some(bus_virtual_statement),
                )?
            };
        }
        delegate_to_inner!(table => verify_air_for_table)
    };

    for value in evals_ef {
        let transposed = verifier_state.next_extension_scalars_vec(DIMENSION)?;
        if dot_product_with_base(&transposed) != value {
            return Err(ProofError::InvalidProof);
        }
        evals_f.extend(transposed);
    }

    Ok((air_point, evals_f))
}
