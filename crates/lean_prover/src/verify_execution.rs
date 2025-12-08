use std::collections::BTreeMap;

use crate::common::*;
use crate::*;
use air::verify_air;
use itertools::Itertools;
use lean_vm::*;
use lookup::verify_gkr_quotient;
use lookup::verify_logup_star;
use multilinear_toolkit::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use sub_protocols::*;
use utils::ToUsize;
use utils::build_challenger;
use whir_p3::WhirConfig;

pub fn verify_execution(bytecode: &Bytecode, public_input: &[F], proof: Proof<F>) -> Result<(), ProofError> {
    let mut verifier_state = VerifierState::new(proof, build_challenger());

    let dims = verifier_state
        .next_base_scalars_vec(1 + N_TABLES)?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>();
    let private_memory_len = dims[0];
    let table_heights: BTreeMap<Table, TableHeight> = (0..N_TABLES)
        .map(|i| (ALL_TABLES[i], TableHeight(dims[i + 1])))
        .collect();

    // only keep tables with non-zero rows
    let table_heights: BTreeMap<_, _> = table_heights
        .into_iter()
        .filter(|(table, height)| {
            height.n_rows_non_padded() > 0 || table == &Table::execution() || table == &Table::poseidon16()
        })
        .collect();

    let public_memory = build_public_memory(public_input);

    let log_public_memory = log2_strict_usize(public_memory.len());
    let log_memory = log2_ceil_usize(public_memory.len() + private_memory_len);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    let base_dims = get_base_dims(log_public_memory, private_memory_len, &table_heights);
    let parsed_commitment_base = packed_pcs_parse_commitment(
        &whir_config_builder_a(),
        &mut verifier_state,
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    )?;

    let bus_challenge = verifier_state.sample();
    let fingerprint_challenge = verifier_state.sample();

    let mut bus_quotients: BTreeMap<Table, EF> = Default::default();
    let mut air_points: BTreeMap<Table, MultilinearPoint<EF>> = Default::default();
    let mut evals_f: BTreeMap<Table, Vec<EF>> = Default::default();
    let mut evals_ef: BTreeMap<Table, Vec<EF>> = Default::default();

    for (table, height) in &table_heights {
        let (this_bus_quotient, this_air_point, this_evals_f, this_evals_ef) = verify_bus_and_air(
            &mut verifier_state,
            table,
            *height,
            bus_challenge,
            fingerprint_challenge,
        )?;
        bus_quotients.insert(*table, this_bus_quotient);
        air_points.insert(*table, this_air_point);
        evals_f.insert(*table, this_evals_f);
        evals_ef.insert(*table, this_evals_ef);
    }

    if bus_quotients.values().copied().sum::<EF>() != EF::ZERO {
        return Err(ProofError::InvalidProof);
    }

    let bytecode_compression_challenges =
        MultilinearPoint(verifier_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let bytecode_lookup_claim = Evaluation::new(
        air_points[&Table::execution()].clone(),
        padd_with_zero_to_next_power_of_two(&evals_f[&Table::execution()][..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );

    let mut lookup_into_memory = NormalPackedLookupVerifier::run(
        &mut verifier_state,
        log_memory,
        table_heights
            .iter()
            .flat_map(|(table, height)| vec![height.n_rows_non_padded_maxed(); table.num_normal_lookups_f()])
            .collect(),
        table_heights
            .iter()
            .flat_map(|(table, height)| vec![height.n_rows_non_padded_maxed(); table.num_normal_lookups_ef()])
            .collect(),
        table_heights
            .iter()
            .flat_map(|(table, height)| vec![height.n_rows_non_padded_maxed(); table.num_vector_lookups()])
            .collect(),
        table_heights
            .keys()
            .flat_map(|table| table.normal_lookup_default_indexes_f())
            .collect(),
        table_heights
            .keys()
            .flat_map(|table| table.normal_lookup_default_indexes_ef())
            .collect(),
        table_heights
            .keys()
            .flat_map(|table| table.vector_lookup_default_indexes())
            .collect(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &public_memory, // we need to pass the first few values of memory, public memory is enough
    )?;

    let bytecode_pushforward_parsed_commitment =
        WhirConfig::new(whir_config_builder_b(), log2_ceil_usize(bytecode.instructions.len()))
            .parse_commitment::<EF>(&mut verifier_state)?;

    let bytecode_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log2_ceil_usize(bytecode.instructions.len()),
        table_heights[&Table::execution()].log_padded(),
        &[bytecode_lookup_claim],
        EF::ONE,
    )?;
    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);
    if folded_bytecode.evaluate(&bytecode_logup_star_statements.on_table.point)
        != bytecode_logup_star_statements.on_table.value
    {
        return Err(ProofError::InvalidProof);
    }
    let memory_statements = vec![lookup_into_memory.on_table.clone()];
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
                &mut lookup_into_memory.on_indexes_vec,
                &mut lookup_into_memory.on_values_f,
                &mut lookup_into_memory.on_values_ef,
                &mut lookup_into_memory.on_values_vec,
            )?,
        );
    }
    assert!(lookup_into_memory.on_indexes_f.is_empty());
    assert!(lookup_into_memory.on_indexes_ef.is_empty());
    assert!(lookup_into_memory.on_indexes_vec.is_empty());
    assert!(lookup_into_memory.on_values_f.is_empty());
    assert!(lookup_into_memory.on_values_ef.is_empty());
    assert!(lookup_into_memory.on_values_vec.is_empty());

    let (initial_pc_statement, final_pc_statement) =
        initial_and_final_pc_conditions(table_heights[&Table::execution()].log_padded());

    final_statements.get_mut(&Table::execution()).unwrap()[ExecutionTable.find_committed_column_index_f(COL_INDEX_PC)]
        .extend(vec![
            bytecode_logup_star_statements.on_indexes.clone(),
            initial_pc_statement,
            final_pc_statement,
        ]);

    let mut all_base_statements = vec![memory_statements, acc_statements];

    all_base_statements.extend(final_statements.into_values().flatten());
    let global_statements_base = packed_pcs_global_statements_for_verifier(
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &all_base_statements,
        &mut verifier_state,
        &[(0, public_memory.clone())].into_iter().collect(),
    )?;

    WhirConfig::new(whir_config_builder_a(), parsed_commitment_base.num_variables).verify(
        &mut verifier_state,
        &parsed_commitment_base,
        global_statements_base,
    )?;

    WhirConfig::new(whir_config_builder_b(), log2_ceil_usize(bytecode.instructions.len())).verify(
        &mut verifier_state,
        &bytecode_pushforward_parsed_commitment,
        bytecode_logup_star_statements.on_pushforward,
    )?;

    Ok(())
}

#[allow(clippy::type_complexity)]
fn verify_bus_and_air(
    verifier_state: &mut VerifierState<PF<EF>, EF, impl FSChallenger<EF>>,
    t: &Table,
    table_height: TableHeight,
    bus_challenge: EF,
    fingerprint_challenge: EF,
) -> ProofResult<(EF, MultilinearPoint<EF>, Vec<EF>, Vec<EF>)> {
    let n_buses = t.buses().len();
    let log_n_buses = log2_ceil_usize(n_buses);
    let log_n_rows = table_height.log_padded();

    assert!(n_buses > 0, "Table {} has no buses", t.name());

    let (mut quotient, bus_point_global, numerator_value_global, denominator_value_global) =
        verify_gkr_quotient::<_, TWO_POW_UNIVARIATE_SKIPS>(verifier_state, log_n_rows + log_n_buses)?;

    let (bus_point, bus_selector_values, bus_data_values) = if n_buses == 1 {
        // easy case
        (
            bus_point_global,
            vec![numerator_value_global],
            vec![denominator_value_global],
        )
    } else {
        let uni_selectors = univariate_selectors::<F>(UNIVARIATE_SKIPS);

        let sub_numerators_evals = verifier_state.next_extension_scalars_vec(n_buses << UNIVARIATE_SKIPS)?;
        assert_eq!(
            numerator_value_global,
            evaluate_univariate_multilinear::<_, _, _, false>(
                &padd_with_zero_to_next_power_of_two(&sub_numerators_evals),
                &bus_point_global[..1 + log_n_buses],
                &uni_selectors,
                None
            ),
        );

        let sub_denominators_evals = verifier_state.next_extension_scalars_vec(n_buses << UNIVARIATE_SKIPS)?;
        assert_eq!(
            denominator_value_global,
            evaluate_univariate_multilinear::<_, _, _, false>(
                &padd_to_next_power_of_two(&sub_denominators_evals, EF::ONE),
                &bus_point_global[..1 + log_n_buses],
                &uni_selectors,
                None
            ),
        );
        let epsilon = verifier_state.sample();
        let bus_point = MultilinearPoint([vec![epsilon], bus_point_global[1 + log_n_buses..].to_vec()].concat());

        let bus_selector_values = sub_numerators_evals
            .chunks_exact(1 << UNIVARIATE_SKIPS)
            .map(|chunk| evaluate_univariate_multilinear::<_, _, _, false>(chunk, &[epsilon], &uni_selectors, None))
            .collect();
        let bus_data_values = sub_denominators_evals
            .chunks_exact(1 << UNIVARIATE_SKIPS)
            .map(|chunk| evaluate_univariate_multilinear::<_, _, _, false>(chunk, &[epsilon], &uni_selectors, None))
            .collect();

        (bus_point, bus_selector_values, bus_data_values)
    };

    let bus_beta = verifier_state.sample();

    let bus_final_values = bus_selector_values
        .iter()
        .zip_eq(&bus_data_values)
        .zip_eq(&t.buses())
        .map(|((&bus_selector_value, &bus_data_value), bus)| {
            bus_selector_value
                * match bus.direction {
                    BusDirection::Pull => EF::NEG_ONE,
                    BusDirection::Push => EF::ONE,
                }
                + bus_beta * (bus_data_value - bus_challenge)
        })
        .collect::<Vec<_>>();

    let bus_virtual_statement = MultiEvaluation::new(bus_point, bus_final_values);

    for bus in t.buses() {
        quotient -= bus.padding_contribution(t, table_height.padding_len(), bus_challenge, fingerprint_challenge);
    }

    let extra_data = ExtraDataForBuses {
        fingerprint_challenge_powers: fingerprint_challenge.powers().collect_n(max_bus_width()),
        fingerprint_challenge_powers_packed: EFPacking::<EF>::from(fingerprint_challenge)
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
                    log_n_rows,
                    &t.air_padding_row_f(),
                    &t.air_padding_row_ef(),
                    Some(bus_virtual_statement),
                )?
            };
        }
        delegate_to_inner!(t => verify_air_for_table)
    };

    Ok((quotient, air_point, evals_f, evals_ef))
}
