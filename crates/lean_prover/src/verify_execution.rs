use std::collections::BTreeMap;

use crate::*;
use backend::{Proof, RawProof, VerifierState};
use lean_vm::*;
use sub_protocols::jagged_pcs::{
    JaggedClaim, ZkvmJaggedLayout, jagged_parse_commitment, jagged_verify, pad_point_high, table_padding_values,
};
use sub_protocols::*;
use utils::{ToUsize, from_end, get_poseidon16};

#[derive(Debug, Clone)]
pub struct ProofVerificationDetails {
    pub bytecode_evaluation: Evaluation<EF>,
}

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof: Proof<F>,
) -> Result<(ProofVerificationDetails, RawProof<F>), ProofError> {
    let mut verifier_state = VerifierState::<EF, _>::new(proof, get_poseidon16().clone())?;
    verifier_state.observe_scalars(public_input);
    verifier_state.observe_scalars(&poseidon16_compress_pair(&bytecode.hash, &SNARK_DOMAIN_SEP));
    // dims layout: [log_inv_rate, log_memory, public_input_len, padding_zero_vec_ptr,
    //               log_n_rows for each table (in BTreeMap order), non_padded_n_rows for each table].
    let dims = verifier_state
        .next_base_scalars_vec(4 + 2 * N_TABLES)?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>();
    let log_inv_rate = dims[0];
    let log_memory = dims[1];
    let public_input_len = dims[2];
    let padding_zero_vec_ptr = dims[3];
    if public_input_len != public_input.len() {
        return Err(ProofError::InvalidProof);
    }
    let null_hash_ptr = padding_zero_vec_ptr + 16;

    let table_n_vars: BTreeMap<Table, VarCount> = (0..N_TABLES).map(|i| (ALL_TABLES[i], dims[4 + i])).collect();
    let non_padded_per_table: BTreeMap<Table, usize> =
        (0..N_TABLES).map(|i| (ALL_TABLES[i], dims[4 + N_TABLES + i])).collect();

    check_rate(log_inv_rate)?;
    let whir_config = default_whir_config(log_inv_rate);
    for (table, &log_n_rows) in &table_n_vars {
        if log_n_rows < MIN_LOG_N_ROWS_PER_TABLE {
            return Err(ProofError::InvalidProof);
        }
        let log_limit = max_log_n_rows_per_table(table);
        if log_n_rows > log_limit {
            return Err(TooBigTableError {
                table_name: table.name(),
                log_n_rows,
                log_limit,
            }
            .into());
        }
        let h = non_padded_per_table[table];
        // h = 0 is valid for tables whose precompile isn't used in this run.
        if h > 0 && log2_ceil_usize(h + 1) > log_n_rows {
            return Err(ProofError::InvalidProof);
        }
        if h > 1 << log_n_rows {
            return Err(ProofError::InvalidProof);
        }
    }
    if log_memory < (*table_n_vars.values().max().unwrap()).max(bytecode.log_size()) {
        return Err(ProofError::InvalidProof);
    }
    if padding_zero_vec_ptr + 16 + 8 > 1 << log_memory {
        // Padding pointer must fit inside committed memory (with room for 16 zero
        // cells and the 8-cell `null_hash_of_zero` block placed after it).
        return Err(ProofError::InvalidProof);
    }

    let public_memory = padd_with_zero_to_next_power_of_two(public_input);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }
    if bytecode.log_size() < MIN_BYTECODE_LOG_SIZE {
        return Err(ProofError::InvalidProof);
    }

    // Build the jagged layout (matches the prover side bit-for-bit).
    let layout = ZkvmJaggedLayout::new(log_memory, bytecode.log_size(), &non_padded_per_table);
    let parsed = jagged_parse_commitment(&layout.config, &mut verifier_state, &whir_config)?;

    // Per-table padding values (must match what the prover used during commit).
    let padding_values_per_table: BTreeMap<Table, Vec<F>> = ALL_TABLES
        .iter()
        .map(|&table| (table, table_padding_values(table, padding_zero_vec_ptr, null_hash_ptr)))
        .collect();

    let logup_c = verifier_state.sample();
    let logup_alphas = verifier_state.sample_vec(log2_ceil_usize(max_bus_width_including_domainsep()));
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
    let gkr_point = &logup_statements.gkr_point;
    let mut committed_statements: CommittedStatements = Default::default();
    for table in ALL_TABLES {
        committed_statements.insert(table, Vec::new());
    }

    let bus_beta = verifier_state.sample();
    let air_alpha = verifier_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(max_air_constraints() + 1);
    let eta: EF = verifier_state.sample();

    let tables_sorted = sort_tables_by_height(&table_n_vars);

    struct TableVerifyData {
        table: Table,
        extra_data: ExtraDataForBuses<EF>,
        eta_power: EF,
    }
    let mut verify_data: Vec<TableVerifyData> = Vec::new();
    let mut initial_sum = EF::ZERO;
    let mut eta_power = EF::ONE;

    for (table, _) in &tables_sorted {
        let bus_numerator_value = logup_statements.bus_numerators_values[table];
        let bus_denominator_value = logup_statements.bus_denominators_values[table];
        let bus_final_value = bus_numerator_value
            * match table.bus().direction {
                BusDirection::Pull => EF::NEG_ONE,
                BusDirection::Push => EF::ONE,
            }
            + bus_beta * (bus_denominator_value - logup_c);

        let logup_cols = table.logup_claim_columns();
        let table_columns_values = &logup_statements.columns_values[table];
        let logup_extra_sum: EF = logup_cols
            .iter()
            .enumerate()
            .map(|(j, col)| air_alpha_powers[1 + j] * table_columns_values[col])
            .sum();
        let initial_table_sum = bus_final_value + logup_extra_sum;

        initial_sum += eta_power * initial_table_sum;

        verify_data.push(TableVerifyData {
            table: *table,
            eta_power,
            extra_data: ExtraDataForBuses::new(logup_alphas_eq_poly.clone(), bus_beta, air_alpha_powers.clone()),
        });

        eta_power *= eta;
    }

    let max_full_degree = tables_sorted.iter().map(|(t, _)| t.degree_air() + 1).max().unwrap();

    let n_max = tables_sorted[0].1;
    let Evaluation {
        point: sumcheck_air_point,
        value: claimed_air_final_value,
    } = sumcheck_verify(&mut verifier_state, n_max, max_full_degree, initial_sum, None)?;

    let mut my_air_final_value = EF::ZERO;
    for vd in &verify_data {
        let n_cols_total = vd.table.n_columns() + vd.table.n_down_columns();
        let col_evals = verifier_state.next_extension_scalars_vec(n_cols_total)?;

        macro_rules! eval_constraint {
            ($t:expr) => {{ <_ as SumcheckComputation<EF>>::eval_extension($t, &col_evals, &vd.extra_data) }};
        }
        let constraint_eval = delegate_to_inner!(&vd.table => eval_constraint);

        let bus_point = from_end(gkr_point, table_n_vars[&vd.table]);
        let natural_ordering_point = natural_ordering_point_for_session(&sumcheck_air_point.0, table_n_vars[&vd.table]);
        my_air_final_value += back_loaded_table_contribution(
            bus_point,
            &sumcheck_air_point.0,
            &natural_ordering_point,
            constraint_eval,
            vd.eta_power,
        );

        macro_rules! split {
            ($t:expr) => {{ columns_evals_up_and_down($t, &col_evals, &natural_ordering_point) }};
        }
        let claim = delegate_to_inner!(&vd.table => split);

        committed_statements.get_mut(&vd.table).unwrap().push(claim);
    }

    if my_air_final_value != claimed_air_final_value {
        return Err(ProofError::InvalidProof);
    }

    let public_memory_random_point =
        MultilinearPoint(verifier_state.sample_vec(log2_strict_usize(public_memory.len())));
    let public_memory_eval = public_memory.evaluate(&public_memory_random_point);

    let claims = build_jagged_claims(
        &layout,
        log_memory,
        &logup_statements,
        &public_memory_random_point,
        public_memory_eval,
        &committed_statements,
        &table_n_vars,
        &padding_values_per_table,
    );

    jagged_verify(&layout.config, &parsed, &claims, &mut verifier_state, &whir_config)?;

    Ok((
        ProofVerificationDetails {
            bytecode_evaluation: logup_statements.bytecode_evaluation.unwrap(),
        },
        verifier_state.into_raw_proof(),
    ))
}

#[allow(clippy::too_many_arguments)]
fn build_jagged_claims(
    layout: &ZkvmJaggedLayout,
    log_memory: usize,
    logup_statements: &GenericLogupStatements,
    public_memory_random_point: &MultilinearPoint<EF>,
    public_memory_eval: EF,
    committed_statements: &CommittedStatements,
    tables_log_heights: &BTreeMap<Table, VarCount>,
    padding_values_per_table: &BTreeMap<Table, Vec<F>>,
) -> Vec<JaggedClaim> {
    let mut claims = Vec::new();

    claims.push(JaggedClaim {
        sub_table_id: layout.memory_st,
        col_in_sub_table: 0,
        z_row: logup_statements.memory_and_acc_point.clone(),
        value: logup_statements.value_memory,
        is_next: false,
        padding_value: F::ZERO,
    });
    claims.push(JaggedClaim {
        sub_table_id: layout.memory_acc_st,
        col_in_sub_table: 0,
        z_row: logup_statements.memory_and_acc_point.clone(),
        value: logup_statements.value_memory_acc,
        is_next: false,
        padding_value: F::ZERO,
    });

    let pm_z_row = pad_point_high(public_memory_random_point, log_memory);
    claims.push(JaggedClaim {
        sub_table_id: layout.memory_st,
        col_in_sub_table: 0,
        z_row: pm_z_row,
        value: public_memory_eval,
        is_next: false,
        padding_value: F::ZERO,
    });

    claims.push(JaggedClaim {
        sub_table_id: layout.bytecode_acc_st,
        col_in_sub_table: 0,
        z_row: logup_statements.bytecode_and_acc_point.clone(),
        value: logup_statements.value_bytecode_acc,
        is_next: false,
        padding_value: F::ZERO,
    });

    let exec_log = tables_log_heights[&Table::execution()];
    let pc_loc = layout.locate(Table::execution(), COL_PC);
    let pc_pad = padding_values_per_table[&Table::execution()][COL_PC];
    claims.push(JaggedClaim {
        sub_table_id: pc_loc.sub_table_id,
        col_in_sub_table: pc_loc.col_in_sub_table,
        z_row: MultilinearPoint(vec![EF::ZERO; exec_log]),
        value: EF::from_usize(STARTING_PC),
        is_next: false,
        padding_value: pc_pad,
    });

    for &table in &ALL_TABLES {
        let pad = &padding_values_per_table[&table];
        for (point, eq_values, next_values) in &committed_statements[&table] {
            for (&col_index, &value) in eq_values {
                let loc = layout.locate(table, col_index);
                claims.push(JaggedClaim {
                    sub_table_id: loc.sub_table_id,
                    col_in_sub_table: loc.col_in_sub_table,
                    z_row: point.clone(),
                    value,
                    is_next: false,
                    padding_value: pad[col_index],
                });
            }
            for (&col_index, &value) in next_values {
                let loc = layout.locate(table, col_index);
                claims.push(JaggedClaim {
                    sub_table_id: loc.sub_table_id,
                    col_in_sub_table: loc.col_in_sub_table,
                    z_row: point.clone(),
                    value,
                    is_next: true,
                    padding_value: pad[col_index],
                });
            }
        }
    }

    claims
}

fn back_loaded_table_contribution<EF: ExtensionField<PF<EF>>>(
    bus_point: &[EF],
    sumcheck_air_point: &[EF],
    natural_ordering_point: &[EF],
    constraint_eval: EF,
    eta_power: EF,
) -> EF {
    let n_t = bus_point.len();
    let n_max = sumcheck_air_point.len();
    let suffix_start = n_max - n_t;
    assert_eq!(natural_ordering_point.len(), n_t);
    let eq_val =
        MultilinearPoint(bus_point.to_vec()).eq_poly_outside(&MultilinearPoint(natural_ordering_point.to_vec()));
    let k_t: EF = sumcheck_air_point[..suffix_start].iter().copied().product();
    eta_power * k_t * eq_val * constraint_eval
}
