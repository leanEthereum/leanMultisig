use std::collections::BTreeMap;

use crate::*;
use lean_vm::*;

use serde::{Deserialize, Serialize};
use sub_protocols::jagged_pcs::{
    JaggedClaim, ZkvmJaggedLayout, jagged_commit, jagged_open, pad_point_high, table_padding_values,
};
use sub_protocols::*;
use tracing::info_span;
use utils::ansi::Colorize;
use utils::{build_prover_state, from_end};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionProof {
    pub proof: Proof<F>,
    // benchmark / debug purpose
    #[serde(skip, default)]
    pub metadata: Option<ExecutionMetadata>,
}

pub fn prove_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    check_rate(whir_config.starting_log_inv_rate)
        .map_err(|err| panic!("{err}"))
        .unwrap();
    let ExecutionTrace {
        traces,
        public_memory_size,
        mut memory, // padded with zeros to next power of two
        metadata,
        padding_zero_vec_ptr,
    } = info_span!("Witness generation").in_scope(|| -> Result<_, ProverError> {
        let execution_result = info_span!("Executing bytecode")
            .in_scope(|| try_execute_bytecode(bytecode, public_input, witness, vm_profiler))?;
        Ok(info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result)))
    })?;

    // Memory must be at least MIN_LOG_MEMORY_SIZE and at least bytecode size.
    let min_memory_size = (1 << MIN_LOG_MEMORY_SIZE).max(1 << bytecode.log_size());
    if memory.len() < min_memory_size {
        memory.resize(min_memory_size, F::ZERO);
    }
    let null_hash_ptr = padding_zero_vec_ptr + 16;
    let log_memory = log2_strict_usize(memory.len());
    let log_bytecode = bytecode.log_size();

    let mut prover_state = build_prover_state();
    prover_state.observe_scalars(public_input);
    prover_state.observe_scalars(&poseidon16_compress_pair(&bytecode.hash, &SNARK_DOMAIN_SEP));
    prover_state.add_base_scalars(
        &[
            vec![
                whir_config.starting_log_inv_rate,
                log_memory,
                public_input.len(),
                padding_zero_vec_ptr,
            ],
            traces.values().map(|t| t.log_n_rows).collect::<Vec<_>>(),
            traces.values().map(|t| t.non_padded_n_rows).collect::<Vec<_>>(),
        ]
        .concat()
        .into_iter()
        .map(F::from_usize)
        .collect::<Vec<_>>(),
    );
    for (table, table_trace) in &traces {
        let log_n_rows = table_trace.log_n_rows;
        assert!(log_n_rows >= MIN_LOG_N_ROWS_PER_TABLE, "missing padding");
        let log_limit = max_log_n_rows_per_table(table);
        if log_n_rows > log_limit {
            return Err(TooBigTableError {
                table_name: table.name(),
                log_n_rows,
                log_limit,
            }
            .into());
        }
    }

    let mut table_log = String::new();
    for (table, trace) in &traces {
        table_log.push_str(&format!(
            "{}: 2^{} * (1 + {:.2}) rows | ",
            table.name(),
            trace.log_n_rows - 1,
            (trace.non_padded_n_rows as f64) / (1 << (trace.log_n_rows - 1)) as f64 - 1.0
        ));
    }
    table_log = table_log.trim_end_matches(" | ").to_string();
    tracing::info!("Trace tables sizes: {}", table_log.magenta());

    // TODO parrallelize
    let mut memory_acc = F::zero_vec(memory.len());
    info_span!("Building memory access count").in_scope(|| {
        for (table, trace) in &traces {
            for lookup in table.lookups() {
                for i in &trace.columns[lookup.index] {
                    for j in 0..lookup.values.len() {
                        memory_acc[i.to_usize() + j] += F::ONE;
                    }
                }
            }
        }
    });

    // // TODO parrallelize
    let mut bytecode_acc = F::zero_vec(bytecode.padded_size());
    info_span!("Building bytecode access count").in_scope(|| {
        for pc in traces[&Table::execution()].columns[COL_PC].iter() {
            bytecode_acc[pc.to_usize()] += F::ONE;
        }
    });

    // Build the jagged layout from non-padded heights.
    let non_padded_per_table: BTreeMap<Table, usize> = traces
        .iter()
        .map(|(table, trace)| (*table, trace.non_padded_n_rows))
        .collect();
    let layout = ZkvmJaggedLayout::new(log_memory, log_bytecode, &non_padded_per_table);

    // Pre-compute per-table padding values (one per AIR column).
    let padding_values_per_table: BTreeMap<Table, Vec<F>> = ALL_TABLES
        .iter()
        .map(|&table| (table, table_padding_values(table, padding_zero_vec_ptr, null_hash_ptr)))
        .collect();

    // Assemble the column-data slice that `jagged_commit` consumes.
    let columns_for_commit: Vec<Vec<&[F]>> =
        build_columns_for_commit(&layout, &memory, &memory_acc, &bytecode_acc, &traces);

    // 1st Commitment (jagged).
    let jagged_witness = jagged_commit(&layout.config, &columns_for_commit, &mut prover_state, whir_config);

    // logup (GKR)
    let logup_c = prover_state.sample();
    let logup_alphas = prover_state.sample_vec(log2_ceil_usize(max_bus_width_including_domainsep()));
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);

    let logup_statements = prove_generic_logup(
        &mut prover_state,
        logup_c,
        &logup_alphas_eq_poly,
        &memory,
        &memory_acc,
        &bytecode.instructions_multilinear,
        &bytecode_acc,
        &traces,
    );
    let gkr_point = &logup_statements.gkr_point;
    // The per-table column evaluations at gkr_suffix are no longer their own WHIR
    // statements — they are absorbed into the AIR sumcheck as virtual constraints.
    let mut committed_statements: CommittedStatements = Default::default();
    for table in ALL_TABLES {
        committed_statements.insert(table, Vec::new());
    }

    let bus_beta = prover_state.sample();
    let air_alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(max_air_constraints() + 1);
    let air_eta: EF = prover_state.sample();

    let tables_log_heights: BTreeMap<Table, VarCount> =
        traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_sorted = sort_tables_by_height(&tables_log_heights);

    let column_refs: Vec<Vec<&[F]>> = tables_sorted
        .iter()
        .map(|(table, _)| {
            traces[table].columns[..table.n_columns()]
                .iter()
                .map(Vec::as_slice)
                .collect()
        })
        .collect();
    let _span = info_span!("Computing shifted columns for AIR sumcheck").entered();
    let shifted_rows: Vec<Vec<Vec<F>>> = tables_sorted
        .par_iter()
        .zip(&column_refs)
        .map(|((table, _), cols)| compute_shifted_columns(&table.down_column_indexes(), cols))
        .collect();
    std::mem::drop(_span);
    let mut sessions = Vec::with_capacity(tables_sorted.len());
    for (idx, (table, log_n_rows)) in tables_sorted.iter().enumerate() {
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

        let eq_suffix = from_end(gkr_point, *log_n_rows).to_vec();

        let extra_data = ExtraDataForBuses::new(logup_alphas_eq_poly.clone(), bus_beta, air_alpha_powers.clone());

        let mut up_down: Vec<&[PF<EF>]> = column_refs[idx].to_vec();
        up_down.extend(shifted_rows[idx].iter().map(Vec::as_slice));
        let packed = MleGroupRef::<EF>::Base(up_down).pack();

        let non_padded = traces[table].non_padded_n_rows;

        macro_rules! make_session {
            ($t:expr) => {{
                let session =
                    AirSumcheckSession::new(packed, eq_suffix, initial_table_sum, *$t, extra_data, non_padded);
                Box::new(session) as Box<dyn OuterSumcheckSession<EF> + '_>
            }};
        }
        sessions.push(delegate_to_inner!(table => make_session));
    }

    let sumcheck_air_point = info_span!("batched AIR sumcheck")
        .in_scope(|| prove_batched_air_sumcheck(&mut prover_state, &mut sessions, air_eta));

    for (idx, (table, _)) in tables_sorted.iter().enumerate() {
        let col_evals = sessions[idx].final_column_evals();
        prover_state.add_extension_scalars(&col_evals);

        let natural_ordering_point =
            natural_ordering_point_for_session(&sumcheck_air_point.0, traces[table].log_n_rows);
        macro_rules! split {
            ($t:expr) => {{ columns_evals_up_and_down($t, &col_evals, &natural_ordering_point) }};
        }
        let claim = delegate_to_inner!(table => split);
        committed_statements.get_mut(table).unwrap().push(claim);
    }

    let public_memory_random_point = MultilinearPoint(prover_state.sample_vec(log2_strict_usize(public_memory_size)));
    let public_memory_eval = (&memory[..public_memory_size]).evaluate(&public_memory_random_point);

    // Translate every claim about the committed polynomial into a JaggedClaim.
    let claims = build_jagged_claims(
        &layout,
        log_memory,
        log_bytecode,
        &logup_statements,
        &public_memory_random_point,
        public_memory_eval,
        &committed_statements,
        &tables_log_heights,
        &padding_values_per_table,
    );

    jagged_open(jagged_witness, &claims, &mut prover_state, whir_config);

    tracing::info!("total pow_grinding time: {} ms", pow_grinding_time().as_millis());
    reset_pow_grinding_time();

    Ok(ExecutionProof {
        proof: prover_state.into_proof(),
        metadata: Some(metadata),
    })
}

/// Build the per-sub-table column-data slice required by [`jagged_commit`].
fn build_columns_for_commit<'a>(
    layout: &ZkvmJaggedLayout,
    memory: &'a [F],
    memory_acc: &'a [F],
    bytecode_acc: &'a [F],
    traces: &'a BTreeMap<Table, TableTrace>,
) -> Vec<Vec<&'a [F]>> {
    let mut columns: Vec<Vec<&'a [F]>> = Vec::with_capacity(layout.config.n_sub_tables());
    columns.push(vec![memory]);
    columns.push(vec![memory_acc]);
    columns.push(vec![bytecode_acc]);
    for &table in &ALL_TABLES {
        let n_cols = table.n_columns();
        let h = traces[&table].non_padded_n_rows;
        let widths = sub_protocols::jagged_pcs::decompose_table_widths(n_cols);
        let mut col_offset = 0;
        for w in widths {
            let cols: Vec<&[F]> = (col_offset..col_offset + w)
                .map(|c| &traces[&table].columns[c][..h])
                .collect();
            columns.push(cols);
            col_offset += w;
        }
    }
    columns
}

#[allow(clippy::too_many_arguments)]
fn build_jagged_claims(
    layout: &ZkvmJaggedLayout,
    log_memory: usize,
    log_bytecode: usize,
    logup_statements: &GenericLogupStatements,
    public_memory_random_point: &MultilinearPoint<EF>,
    public_memory_eval: EF,
    committed_statements: &CommittedStatements,
    tables_log_heights: &BTreeMap<Table, VarCount>,
    padding_values_per_table: &BTreeMap<Table, Vec<F>>,
) -> Vec<JaggedClaim> {
    let mut claims = Vec::new();

    // Memory + memory_acc at the shared logup point.
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

    // Public memory: claim about memory's MLE at a point of length
    // log2(public_memory_size). Lift to length log_memory by prepending zeros
    // (the public input lives in the first 2^len cells of memory).
    let pm_z_row = pad_point_high(public_memory_random_point, log_memory);
    claims.push(JaggedClaim {
        sub_table_id: layout.memory_st,
        col_in_sub_table: 0,
        z_row: pm_z_row,
        value: public_memory_eval,
        is_next: false,
        padding_value: F::ZERO,
    });

    // Bytecode_acc.
    claims.push(JaggedClaim {
        sub_table_id: layout.bytecode_acc_st,
        col_in_sub_table: 0,
        z_row: logup_statements.bytecode_and_acc_point.clone(),
        value: logup_statements.value_bytecode_acc,
        is_next: false,
        padding_value: F::ZERO,
    });

    // PC start: PC[0] = STARTING_PC. With z_row = (0, ..., 0) of length
    // log_n_rows[execution], this is a claim about the data-only column at
    // row 0 (since the indicator factor is 0 at this point, padding doesn't
    // contribute regardless of padding_value).
    let _ = log_bytecode;
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
    // PC end (PC[2^log - 1] = ENDING_PC) is automatically enforced by the
    // padding_value = ENDING_PC (the structural padding-row value); no extra
    // claim required.

    // Per-table per-column AIR sumcheck claims.
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
