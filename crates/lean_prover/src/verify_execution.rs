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
    pub table_n_vars: BTreeMap<Table, VarCount>,
    pub first_quotient_gkr_n_vars: usize,
    pub total_whir_statements_base: usize,
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
    for (table, &n_vars) in &table_n_vars {
        if n_vars < MIN_LOG_N_ROWS_PER_TABLE {
            return Err(ProofError::InvalidProof);
        }
        if n_vars
            > MAX_LOG_N_ROWS_PER_TABLE
                .iter()
                .find(|(t, _)| t == table)
                .map(|(_, m)| *m)
                .unwrap()
        {
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

    let logup_statements = verify_generic_logup(&mut verifier_state, logup_c, logup_alpha, log_memory, &table_n_vars)?;
    let mut committed_statements: CommittedStatements = Default::default();
    for table in ALL_TABLES {
        committed_statements.insert(
            table,
            vec![(
                logup_statements.points[&table].clone(),
                logup_statements.columns_values[&table].clone(),
            )],
        );
    }

    let bus_beta = verifier_state.sample();
    verifier_state.duplexing();
    let air_alpha = verifier_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(max_air_constraints() + 1);

    for (table, log_n_rows) in &table_n_vars {
        let this_air_claims = verify_bus_and_air(
            &mut verifier_state,
            table,
            *log_n_rows,
            logup_c,
            logup_alpha,
            bus_beta,
            air_alpha_powers.clone(),
            &logup_statements.points[table],
            logup_statements.bus_numerators_values[table],
            logup_statements.bus_denominators_values[table],
        )?;
        committed_statements.get_mut(table).unwrap().extend(this_air_claims);
    }

    let bytecode_compression_challenges =
        MultilinearPoint(verifier_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let bytecode_air_entry = &mut committed_statements.get_mut(&Table::execution()).unwrap()[2];
    let bytecode_air_point = bytecode_air_entry.0.clone();
    let mut bytecode_air_values = vec![];
    for bytecode_col_index in N_COMMITTED_EXEC_COLUMNS..N_COMMITTED_EXEC_COLUMNS + N_INSTRUCTION_COLUMNS {
        bytecode_air_values.push(bytecode_air_entry.1.remove(&bytecode_col_index).unwrap());
    }

    let bytecode_lookup_claim = Evaluation::new(
        bytecode_air_point.clone(),
        padd_with_zero_to_next_power_of_two(&bytecode_air_values).evaluate(&bytecode_compression_challenges),
    );

    let bytecode_pushforward_parsed_commitment =
        WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len()))
            .parse_commitment::<EF>(&mut verifier_state)?;

    let bytecode_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log2_ceil_usize(bytecode.instructions.len()),
        table_n_vars[&Table::execution()],
        bytecode_lookup_claim,
    )?;
    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);
    if folded_bytecode.evaluate(&bytecode_logup_star_statements.on_table.point)
        != bytecode_logup_star_statements.on_table.value
    {
        return Err(ProofError::InvalidProof);
    }

    committed_statements.get_mut(&Table::execution()).unwrap().push((
        bytecode_logup_star_statements.on_indexes.point.clone(),
        BTreeMap::from_iter([(COL_PC, bytecode_logup_star_statements.on_indexes.value)]),
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
    let total_whir_statements_base = global_statements_base.iter().map(|s| s.values.len()).sum();
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
        table_n_vars,
        first_quotient_gkr_n_vars: logup_statements.total_n_vars,
        total_whir_statements_base,
    })
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn verify_bus_and_air(
    verifier_state: &mut impl FSVerifier<EF>,
    table: &Table,
    log_n_nrows: usize,
    logup_c: EF,
    logup_alpha: EF,
    bus_beta: EF,
    air_alpha_powers: Vec<EF>,
    bus_point: &MultilinearPoint<EF>,
    bus_numerator_value: EF,
    bus_denominator_value: EF,
) -> ProofResult<Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>)>> {
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
        alpha_powers: air_alpha_powers,
    };

    let air_claims = {
        macro_rules! verify_air_for_table {
            ($t:expr) => {
                verify_air(
                    verifier_state,
                    $t,
                    extra_data,
                    1,
                    log_n_nrows,
                    Some(bus_virtual_statement),
                )?
            };
        }
        delegate_to_inner!(table => verify_air_for_table)
    };

    let mut res = vec![];
    if let Some(down_point) = air_claims.down_point {
        assert_eq!(air_claims.evals_f_on_down_columns.len(), table.n_down_columns_f());
        let mut down_evals = BTreeMap::new();
        for (value_f, col_index) in air_claims
            .evals_f_on_down_columns
            .iter()
            .zip(table.down_column_indexes_f())
        {
            down_evals.insert(col_index, *value_f);
        }

        assert_eq!(air_claims.evals_ef_on_down_columns.len(), table.n_down_columns_ef());
        for (col_index, value) in table
            .down_column_indexes_ef()
            .into_iter()
            .zip(air_claims.evals_ef_on_down_columns)
        {
            let transposed = verifier_state.next_extension_scalars_vec(DIMENSION)?;
            if dot_product_with_base(&transposed) != value {
                return Err(ProofError::InvalidProof);
            }
            for (j, v) in transposed.iter().enumerate() {
                let virtual_index = table.n_columns_f_air() + col_index * DIMENSION + j;
                down_evals.insert(virtual_index, *v);
            }
        }
        res.push((down_point, down_evals));
    }

    assert_eq!(air_claims.evals_f.len(), table.n_columns_f_air());
    assert_eq!(air_claims.evals_ef.len(), table.n_columns_ef_air());
    let mut evals = air_claims
        .evals_f
        .iter()
        .copied()
        .enumerate()
        .collect::<BTreeMap<_, _>>();
    for (col_index, value) in air_claims.evals_ef.into_iter().enumerate() {
        let transposed = verifier_state.next_extension_scalars_vec(DIMENSION)?;
        if dot_product_with_base(&transposed) != value {
            return Err(ProofError::InvalidProof);
        }
        for (j, v) in transposed.into_iter().enumerate() {
            let virtual_index = table.n_columns_f_air() + col_index * DIMENSION + j;
            evals.insert(virtual_index, v);
        }
    }

    res.push((air_claims.point.clone(), evals));

    Ok(res)
}
