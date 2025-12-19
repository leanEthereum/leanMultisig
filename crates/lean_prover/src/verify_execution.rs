use std::collections::BTreeMap;

use crate::*;
use crate::{SnarkParams, common::*};
use air::verify_air;
use itertools::Itertools;
use lean_vm::*;
use lookup::verify_logup_star;
use multilinear_toolkit::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use sub_protocols::*;
use utils::ToUsize;
use whir_p3::WhirConfig;

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof: Vec<F>,
    params: &SnarkParams,
) -> Result<(), ProofError> {
    let mut verifier_state = VerifierState::<EF, _>::new(proof, get_poseidon16().clone());
    verifier_state.duplexing();

    let dims = verifier_state
        .next_base_scalars_vec(1 + N_TABLES)?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>();
    let log_memory = dims[0];
    let table_heights: BTreeMap<Table, VarCount> = (0..N_TABLES).map(|i| (ALL_TABLES[i], dims[i + 1])).collect();
    for &n_vars in table_heights.values() {
        if !(MIN_LOG_N_ROWS_PER_TABLE..=MAX_LOG_N_ROWS_PER_TABLE).contains(&n_vars) {
            return Err(ProofError::InvalidProof);
        }
    }

    // // only keep tables with non-zero rows
    // let table_heights: BTreeMap<_, _> = table_heights
    //     .into_iter()
    //     .filter(|(table, height)| {
    //         height.n_rows_non_padded() > 0 || table == &Table::execution() || table == &Table::poseidon16()
    //     })
    //     .collect();

    let public_memory = build_public_memory(public_input);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    let base_dims = get_base_dims(log_memory, &table_heights);
    let base_packed_dims = PackedDims::compute(&base_dims);
    let parsed_commitment_base =
        packed_pcs_parse_commitment::<F, EF>(&params.first_whir, &mut verifier_state, &base_packed_dims)?;

    let logup_c = verifier_state.sample();
    verifier_state.duplexing();
    let logup_alpha = verifier_state.sample();
    verifier_state.duplexing();

    let mut lookup_into_memory = NormalLookupVerifier::run(
        &mut verifier_state,
        logup_c,
        logup_alpha,
        log_memory,
        table_heights
            .iter()
            .flat_map(|(table, log_n_rows)| vec![*log_n_rows; table.num_lookups_f()])
            .collect(),
        table_heights
            .keys()
            .flat_map(|table| table.lookups_f().iter().map(|l| l.values.len()).collect::<Vec<_>>())
            .collect(),
        table_heights
            .iter()
            .flat_map(|(table, log_n_rows)| vec![*log_n_rows; table.num_lookups_ef()])
            .collect(),
        table_heights
            .iter()
            .flat_map(|(table, log_n_rows)| vec![*log_n_rows; table.num_buses()])
            .collect(),
        UNIVARIATE_SKIPS,
    )?;

    let mut air_points: BTreeMap<Table, MultilinearPoint<EF>> = Default::default();
    let mut evals_f: BTreeMap<Table, Vec<EF>> = Default::default();
    let mut evals_ef: BTreeMap<Table, Vec<EF>> = Default::default();

    let mut bus_offset = 0;
    for (table, log_n_rows) in &table_heights {
        let (this_air_point, this_evals_f, this_evals_ef) = verify_bus_and_air(
            &mut verifier_state,
            table,
            *log_n_rows,
            logup_c,
            logup_alpha,
            &lookup_into_memory.on_bus_numerators[bus_offset..][..table.buses().len()],
            &lookup_into_memory.on_bus_denominators[bus_offset..][..table.buses().len()],
        )?;
        air_points.insert(*table, this_air_point);
        evals_f.insert(*table, this_evals_f);
        evals_ef.insert(*table, this_evals_ef);
        bus_offset += table.buses().len();
    }
    assert_eq_many!(
        bus_offset,
        lookup_into_memory.on_bus_numerators.len(),
        lookup_into_memory.on_bus_denominators.len()
    );

    let bytecode_compression_challenges =
        MultilinearPoint(verifier_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let bytecode_lookup_claim = Evaluation::new(
        air_points[&Table::execution()].clone(),
        padd_with_zero_to_next_power_of_two(&evals_f[&Table::execution()][..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );

    let bytecode_pushforward_parsed_commitment =
        WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len()))
            .parse_commitment::<EF>(&mut verifier_state)?;

    let bytecode_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log2_ceil_usize(bytecode.instructions.len()),
        table_heights[&Table::execution()],
        &[bytecode_lookup_claim],
        EF::ONE,
    )?;
    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);
    if folded_bytecode.evaluate(&bytecode_logup_star_statements.on_table.point)
        != bytecode_logup_star_statements.on_table.value
    {
        return Err(ProofError::InvalidProof);
    }

    let mut public_memory_random_point =
        MultilinearPoint(verifier_state.sample_vec(log2_strict_usize(public_memory.len())));
    let public_memory_eval = public_memory.evaluate(&public_memory_random_point);
    public_memory_random_point.0.splice(
        0..0,
        EF::zero_vec(log2_strict_usize((1 << log_memory) / public_memory.len())),
    );
    let public_memory_statement = Evaluation::new(public_memory_random_point, public_memory_eval);

    let memory_statements = vec![lookup_into_memory.on_table, public_memory_statement];
    let acc_statements = vec![lookup_into_memory.on_acc];

    let mut final_statements: BTreeMap<Table, Vec<Vec<Evaluation<EF>>>> = Default::default();
    for table in table_heights.keys() {
        final_statements.insert(
            *table,
            table.committed_statements_verifier(
                &mut verifier_state,
                &air_points[table],
                &evals_f[table],
                &evals_ef[table],
                &mut lookup_into_memory.on_indexes_f,
                &mut lookup_into_memory.on_indexes_ef,
                &mut lookup_into_memory.on_values_f,
                &mut lookup_into_memory.on_values_ef,
            )?,
        );
    }
    assert!(lookup_into_memory.on_indexes_f.is_empty());
    assert!(lookup_into_memory.on_indexes_ef.is_empty());
    assert!(lookup_into_memory.on_values_f.is_empty());
    assert!(lookup_into_memory.on_values_ef.is_empty());

    let (initial_pc_statement, final_pc_statement) =
        initial_and_final_pc_conditions(table_heights[&Table::execution()]);

    final_statements.get_mut(&Table::execution()).unwrap()[ExecutionTable.find_committed_column_index_f(COL_INDEX_PC)]
        .extend(vec![
            bytecode_logup_star_statements.on_indexes.clone(),
            initial_pc_statement,
            final_pc_statement,
        ]);

    let mut all_base_statements = vec![memory_statements, acc_statements];
    all_base_statements.extend(final_statements.into_values().flatten());

    let global_statements_base = packed_pcs_global_statements(&base_packed_dims, &all_base_statements);

    WhirConfig::new(&params.first_whir, parsed_commitment_base.num_variables).verify(
        &mut verifier_state,
        &parsed_commitment_base,
        global_statements_base,
    )?;

    WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len())).verify(
        &mut verifier_state,
        &bytecode_pushforward_parsed_commitment,
        bytecode_logup_star_statements.on_pushforward,
    )?;

    Ok(())
}

#[allow(clippy::type_complexity)]
fn verify_bus_and_air(
    verifier_state: &mut impl FSVerifier<EF>,
    t: &Table,
    log_n_nrows: usize,
    logup_c: EF,
    logup_alpha: EF,
    bus_numerator_statements: &[Evaluation<EF>],
    bus_denominator_statements: &[Evaluation<EF>],
) -> ProofResult<(MultilinearPoint<EF>, Vec<EF>, Vec<EF>)> {
    assert_eq!(t.buses().len(), bus_numerator_statements.len());
    let bus_point = bus_numerator_statements[0].point.clone();
    assert!(t.buses().iter().all(|_| bus_numerator_statements[0].point == bus_point));
    assert!(
        t.buses()
            .iter()
            .all(|_| bus_denominator_statements[0].point == bus_point)
    );

    let bus_beta = verifier_state.sample();
    verifier_state.duplexing();

    let bus_final_values = bus_numerator_statements
        .iter()
        .zip_eq(bus_denominator_statements)
        .zip_eq(t.buses())
        .map(|((bus_selector_statement, bus_data_statement), bus)| {
            bus_selector_statement.value
                * match bus.direction {
                    BusDirection::Pull => EF::NEG_ONE,
                    BusDirection::Push => EF::ONE,
                }
                + bus_beta * (bus_data_statement.value - logup_c)
        })
        .collect::<Vec<_>>();

    let bus_virtual_statement = MultiEvaluation::new(bus_point, bus_final_values);

    let extra_data = ExtraDataForBuses {
        logup_alpha_powers: logup_alpha.powers().collect_n(max_bus_width()),
        logup_alpha_powers_packed: EFPacking::<EF>::from(logup_alpha)
            .powers()
            .collect_n(max_bus_width()),
        bus_beta,
        bus_beta_packed: EFPacking::<EF>::from(bus_beta),
        alpha_powers: vec![], // filled later
    };

    let (air_point, evals_f, evals_ef) = {
        macro_rules! verify_air_for_table {
            ($t:expr) => {
                verify_air(
                    verifier_state,
                    $t,
                    extra_data,
                    UNIVARIATE_SKIPS,
                    log_n_nrows,
                    &t.air_padding_row_f(),
                    &t.air_padding_row_ef(),
                    Some(bus_virtual_statement),
                )?
            };
        }
        delegate_to_inner!(t => verify_air_for_table)
    };

    Ok((air_point, evals_f, evals_ef))
}
