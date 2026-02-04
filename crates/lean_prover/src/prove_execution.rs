use std::collections::BTreeMap;

use crate::common::*;
use crate::*;
use air::prove_air;
use lean_vm::*;

use p3_util::log2_ceil_usize;
use sub_protocols::*;
use tracing::info_span;
use utils::{build_prover_state, padd_with_zero_to_next_power_of_two};
use xmss::Poseidon16History;

#[derive(Debug)]
pub struct ExecutionProof {
    pub proof: Vec<F>,
    pub proof_size_fe: usize,
    pub exec_summary: String,
    pub first_whir_n_vars: usize,
}

pub fn prove_execution(
    bytecode: &Bytecode,
    (public_input, private_input): (&[F], &[F]),
    poseidons_16_precomputed: &Poseidon16History,
    params: &SnarkParams,
    vm_profiler: bool,
) -> ExecutionProof {
    let mut exec_summary = String::new();
    let ExecutionTrace {
        traces,
        public_memory_size,
        non_zero_memory_size: _, // TODO use the information of the ending zeros for speedup
        mut memory,              // padded with zeros to next power of two
    } = info_span!("Witness generation").in_scope(|| {
        let mut execution_result = info_span!("Executing bytecode").in_scope(|| {
            execute_bytecode(
                bytecode,
                (public_input, private_input),
                vm_profiler,
                poseidons_16_precomputed,
            )
        });
        exec_summary = std::mem::take(&mut execution_result.summary);
        info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result))
    });

    if memory.len() < 1 << MIN_LOG_MEMORY_SIZE {
        memory.resize(1 << MIN_LOG_MEMORY_SIZE, F::ZERO);
    }

    let mut prover_state = build_prover_state();
    prover_state.add_base_scalars(
        &[
            vec![log2_strict_usize(memory.len())],
            traces.values().map(|t| t.log_n_rows).collect::<Vec<_>>(),
        ]
        .concat()
        .into_iter()
        .map(F::from_usize)
        .collect::<Vec<_>>(),
    );

    // TODO parrallelize
    let mut acc = F::zero_vec(memory.len());
    info_span!("Building memory access count").in_scope(|| {
        for (table, trace) in &traces {
            for lookup in table.lookups_f() {
                for i in &trace.base[lookup.index] {
                    for j in 0..lookup.values.len() {
                        acc[i.to_usize() + j] += F::ONE;
                    }
                }
            }
            for lookup in table.lookups_ef() {
                for i in &trace.base[lookup.index] {
                    for j in 0..DIMENSION {
                        acc[i.to_usize() + j] += F::ONE;
                    }
                }
            }
        }
    });

    // 1st Commitment
    let packed_pcs_witness_base = packed_pcs_commit(&mut prover_state, &params.first_whir, &memory, &acc, &traces);
    let first_whir_n_vars = packed_pcs_witness_base.packed_polynomial.by_ref().n_vars();

    // logup (GKR)
    let logup_c = prover_state.sample();
    let logup_alphas = prover_state.sample_vec(log2_ceil_usize(max_bus_width()));
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);

    let logup_statements = prove_generic_logup(
        &mut prover_state,
        logup_c,
        &logup_alphas_eq_poly,
        &memory,
        &acc,
        &traces,
    );
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

    let bus_beta = prover_state.sample();
    let air_alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(max_air_constraints() + 1);

    for (table, trace) in traces.iter() {
        let this_air_claims = prove_bus_and_air(
            &mut prover_state,
            table,
            trace,
            logup_c,
            &logup_alphas_eq_poly,
            bus_beta,
            air_alpha_powers.clone(),
            &logup_statements.points[table],
            logup_statements.bus_numerators_values[table],
            logup_statements.bus_denominators_values[table],
        );
        committed_statements.get_mut(table).unwrap().extend(this_air_claims);
    }

    let bytecode_compression_challenges =
        MultilinearPoint(prover_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);

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
    let bytecode_poly_eq_point = eval_eq(&bytecode_lookup_claim.point);
    let bytecode_pushforward = MleOwned::Extension(compute_pushforward(
        &traces[&Table::execution()].base[COL_PC],
        folded_bytecode.len(),
        &bytecode_poly_eq_point,
    ));

    let bytecode_pushforward_commitment =
        WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len()))
            .commit(&mut prover_state, &bytecode_pushforward);

    let bytecode_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Extension(&folded_bytecode),
        &traces[&Table::execution()].base[COL_PC],
        bytecode_lookup_claim.value,
        &bytecode_poly_eq_point,
        &bytecode_pushforward.by_ref(),
        Some(bytecode.instructions.len()),
    );

    committed_statements.get_mut(&Table::execution()).unwrap().push((
        bytecode_logup_star_statements.on_indexes.point.clone(),
        BTreeMap::from_iter([(COL_PC, bytecode_logup_star_statements.on_indexes.value)]),
    ));

    let public_memory_random_point = MultilinearPoint(prover_state.sample_vec(log2_strict_usize(public_memory_size)));
    let public_memory_eval = (&memory[..public_memory_size]).evaluate(&public_memory_random_point);

    let memory_acc_statements = vec![
        SparseStatement::new(
            packed_pcs_witness_base.packed_n_vars,
            logup_statements.memory_acc_point,
            vec![
                SparseValue::new(0, logup_statements.value_memory),
                SparseValue::new(1, logup_statements.value_acc),
            ],
        ),
        SparseStatement::new(
            packed_pcs_witness_base.packed_n_vars,
            public_memory_random_point,
            vec![SparseValue::new(0, public_memory_eval)],
        ),
    ];

    let table_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let global_statements_base = packed_pcs_global_statements(
        packed_pcs_witness_base.packed_n_vars,
        log2_strict_usize(memory.len()),
        memory_acc_statements,
        &table_heights,
        &committed_statements,
    );

    WhirConfig::new(
        &params.first_whir,
        packed_pcs_witness_base.packed_polynomial.by_ref().n_vars(),
    )
    .prove(
        &mut prover_state,
        global_statements_base,
        packed_pcs_witness_base.inner_witness,
        &packed_pcs_witness_base.packed_polynomial.by_ref(),
    );

    WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len())).prove(
        &mut prover_state,
        bytecode_logup_star_statements
            .on_pushforward
            .into_iter()
            .map(|smt| SparseStatement::dense(smt.point, smt.value))
            .collect::<Vec<_>>(),
        bytecode_pushforward_commitment,
        &bytecode_pushforward.by_ref(),
    );
    let proof_size_fe = prover_state.pruned_proof().proof_size_fe();
    ExecutionProof {
        proof: prover_state.raw_proof(),
        proof_size_fe,
        exec_summary,
        first_whir_n_vars,
    }
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn prove_bus_and_air(
    prover_state: &mut impl FSProver<EF>,
    table: &Table,
    trace: &TableTrace,
    logup_c: EF,
    logup_alphas_eq_poly: &[EF],
    bus_beta: EF,
    air_alpha_powers: Vec<EF>,
    bus_point: &MultilinearPoint<EF>,
    bus_numerator_value: EF,
    bus_denominator_value: EF,
) -> Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>)> {
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

    let air_claims = info_span!("AIR proof", table = table.name()).in_scope(|| {
        macro_rules! prove_air_for_table {
            ($t:expr) => {
                prove_air(
                    prover_state,
                    $t,
                    extra_data,
                    1,
                    &trace.base[..$t.n_columns_f_air()],
                    &trace.ext[..$t.n_columns_ef_air()],
                    Some(bus_virtual_statement),
                    $t.n_columns_air() + $t.total_n_down_columns_air() > 5, // heuristic
                )
            };
        }
        delegate_to_inner!(table => prove_air_for_table)
    });

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
            let transposed = transpose_slice_to_basis_coefficients::<F, EF>(&trace.ext[col_index])
                .iter()
                .map(|base_col| base_col.evaluate(&down_point))
                .collect::<Vec<_>>();
            assert_eq!(dot_product_with_base(&transposed), value); // sanity check
            prover_state.add_extension_scalars(&transposed);
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
    for (col_index, (value, col)) in air_claims.evals_ef.into_iter().zip(&trace.ext).enumerate() {
        let transposed = transpose_slice_to_basis_coefficients::<F, EF>(col)
            .iter()
            .map(|base_col| base_col.evaluate(&air_claims.point))
            .collect::<Vec<_>>();
        prover_state.add_extension_scalars(&transposed);
        assert_eq!(dot_product_with_base(&transposed), value); // sanity check
        for (j, v) in transposed.into_iter().enumerate() {
            let virtual_index = table.n_columns_f_air() + col_index * DIMENSION + j;
            evals.insert(virtual_index, v);
        }
    }

    res.push((air_claims.point.clone(), evals));

    res
}
