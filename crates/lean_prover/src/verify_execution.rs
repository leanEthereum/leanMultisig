use std::collections::BTreeMap;

use crate::*;
use air::verify_air;
use lean_vm::*;
use sub_protocols::*;
use utils::ToUsize;

#[derive(Debug, Clone)]
pub struct ProofVerificationDetails {
    pub bytecode_evaluation: Evaluation<EF>,
}

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof: RawProof<F>,
) -> Result<ProofVerificationDetails, ProofError> {
    let mut verifier_state = VerifierState::<EF, _>::new(proof, get_poseidon16().clone());

    let dims = verifier_state
        .next_base_scalars_vec(2 + N_TABLES)?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>();
    let log_inv_rate = dims[0];
    let log_memory = dims[1];
    let table_n_vars: BTreeMap<Table, VarCount> = (0..N_TABLES).map(|i| (ALL_TABLES[i], dims[i + 2])).collect();
    if !(MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(ProofError::InvalidProof);
    }
    let whir_config = default_whir_config(log_inv_rate);
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
    if log_memory < (*table_n_vars.values().max().unwrap()).max(bytecode.log_size()) {
        return Err(ProofError::InvalidProof);
    }

    let public_memory = build_public_memory(public_input);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    let parsed_commitment = stacked_pcs_parse_commitment(
        &whir_config,
        &mut verifier_state,
        log_memory,
        bytecode.log_size(),
        &table_n_vars,
    )?;

    let logup_c = verifier_state.sample();
    let logup_alphas = verifier_state.sample_vec(log2_ceil_usize(max_bus_width()));
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);

    let logup_statements = verify_generic_logup(
        &mut verifier_state,
        logup_c,
        &logup_alphas,
        &logup_alphas_eq_poly,
        log_memory,
        &bytecode.instructions_multilinear,
        &table_n_vars,
    )?;
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
    let air_alpha = verifier_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(max_air_constraints() + 1);

    let tables_sorted = sort_tables_by_height(&table_n_vars);
    for (table, log_n_rows) in &tables_sorted {
        let this_air_claims = verify_bus_and_air(
            &mut verifier_state,
            table,
            *log_n_rows,
            logup_c,
            &logup_alphas_eq_poly,
            bus_beta,
            air_alpha_powers.clone(),
            &logup_statements.points[table],
            logup_statements.bus_numerators_values[table],
            logup_statements.bus_denominators_values[table],
        )?;
        committed_statements.get_mut(table).unwrap().extend(this_air_claims);
    }

    let public_memory_random_point =
        MultilinearPoint(verifier_state.sample_vec(log2_strict_usize(public_memory.len())));
    let public_memory_eval = public_memory.evaluate(&public_memory_random_point);

    let previous_statements = vec![
        SparseStatement::new(
            parsed_commitment.num_variables,
            logup_statements.memory_and_acc_point,
            vec![
                SparseValue::new(0, logup_statements.value_memory),
                SparseValue::new(1, logup_statements.value_memory_acc),
            ],
        ),
        SparseStatement::new(
            parsed_commitment.num_variables,
            public_memory_random_point,
            vec![SparseValue::new(0, public_memory_eval)],
        ),
        SparseStatement::new(
            parsed_commitment.num_variables,
            logup_statements.bytecode_and_acc_point,
            vec![SparseValue::new(
                (2 << log_memory) >> bytecode.log_size(),
                logup_statements.value_bytecode_acc,
            )],
        ),
    ];

    let global_statements_base = stacked_pcs_global_statements(
        parsed_commitment.num_variables,
        log_memory,
        bytecode.log_size(),
        previous_statements,
        &table_n_vars,
        &committed_statements,
    );

    // sanity check (not necessary for soundness)
    let num_whir_statements = global_statements_base.iter().map(|s| s.values.len()).sum::<usize>();
    assert_eq!(num_whir_statements, total_whir_statements());

    WhirConfig::new(&whir_config, parsed_commitment.num_variables).verify(
        &mut verifier_state,
        &parsed_commitment,
        global_statements_base,
    )?;

    Ok(ProofVerificationDetails {
        bytecode_evaluation: logup_statements.bytecode_evaluation.unwrap(),
    })
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn verify_bus_and_air(
    verifier_state: &mut impl FSVerifier<EF>,
    table: &Table,
    log_n_nrows: usize,
    logup_c: EF,
    logup_alphas_eq_poly: &[EF],
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
        logup_alphas_eq_poly: logup_alphas_eq_poly.to_vec(),
        logup_alphas_eq_poly_packed: logup_alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect(),
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
                    log_n_nrows,
                    Some(bus_virtual_statement),
                )?
            };
        }
        delegate_to_inner!(table => verify_air_for_table)
    };

    let mut res = vec![];
    if let Some(down_point) = air_claims.down_point {
        assert_eq!(air_claims.evals_on_down_columns.len(), table.n_down_columns());
        let mut down_evals = BTreeMap::new();
        for (value_f, col_index) in air_claims.evals_on_down_columns.iter().zip(table.down_column_indexes()) {
            down_evals.insert(col_index, *value_f);
        }

        res.push((down_point, down_evals));
    }

    assert_eq!(air_claims.evals.len(), table.n_columns());
    let evals = air_claims.evals.iter().copied().enumerate().collect::<BTreeMap<_, _>>();

    res.push((air_claims.point.clone(), evals));

    Ok(res)
}
