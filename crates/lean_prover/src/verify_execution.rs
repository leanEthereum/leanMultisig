use std::collections::BTreeMap;

use crate::common::*;
use crate::*;
use air::verify_air;
use itertools::Itertools;
use lean_vm::*;
use lookup::verify_gkr_quotient;
use lookup::verify_logup_star;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use poseidon_circuit::PoseidonGKRLayers;
use poseidon_circuit::verify_poseidon_gkr;
use sub_protocols::*;
use utils::ToUsize;
use utils::build_challenger;
use whir_p3::WhirConfig;
use whir_p3::WhirConfigBuilder;
use whir_p3::second_batched_whir_config_builder;

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof: Proof<F>,
    whir_config_builder: WhirConfigBuilder,
) -> Result<(), ProofError> {
    let mut verifier_state = VerifierState::new(proof, build_challenger());

    let p16_gkr_layers = PoseidonGKRLayers::<16, N_COMMITED_CUBES_P16>::build(Some(VECTOR_LEN));
    let p24_gkr_layers = PoseidonGKRLayers::<24, N_COMMITED_CUBES_P24>::build(None);

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
        .filter(|(table, height)| height.n_rows_non_padded() > 0 || table == &Table::execution() || table.is_poseidon())
        .collect();

    let public_memory = build_public_memory(public_input);

    let log_public_memory = log2_strict_usize(public_memory.len());
    let log_memory = log2_ceil_usize(public_memory.len() + private_memory_len);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    let base_dims = get_base_dims(
        log_public_memory,
        private_memory_len,
        (&p16_gkr_layers, &p24_gkr_layers),
        &table_heights,
    );
    let parsed_commitment_base = packed_pcs_parse_commitment(
        &whir_config_builder,
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

    let bytecode_lookup_claim_1 = Evaluation::new(
        air_points[&Table::execution()].clone(),
        padd_with_zero_to_next_power_of_two(&evals_f[&Table::execution()][..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );

    let normal_lookup_into_memory = NormalPackedLookupVerifier::step_1(
        &mut verifier_state,
        table_heights
            .iter()
            .flat_map(|(table, height)| vec![height.n_rows_non_padded_maxed(); table.num_normal_lookups_f()])
            .collect(),
        table_heights
            .iter()
            .flat_map(|(table, height)| vec![height.n_rows_non_padded_maxed(); table.num_normal_lookups_ef()])
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
            .flat_map(|table| table.normal_lookups_statements_f(&air_points[table], &evals_f[table]))
            .collect(),
        table_heights
            .keys()
            .flat_map(|table| table.normal_lookups_statements_ef(&air_points[table], &evals_ef[table]))
            .collect(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &public_memory, // we need to pass the first few values of memory, public memory is enough
    )?;

    let vectorized_lookup_into_memory = VectorizedPackedLookupVerifier::<_, VECTOR_LEN>::step_1(
        &mut verifier_state,
        table_heights
            .iter()
            .flat_map(|(table, height)| vec![height.n_rows_non_padded_maxed(); table.num_vector_lookups()])
            .collect(),
        table_heights
            .keys()
            .flat_map(|table| table.vector_lookup_default_indexes())
            .collect(),
        table_heights
            .keys()
            .flat_map(|table| table.vectorized_lookups_statements(&air_points[table], &evals_f[table]))
            .collect(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &public_memory, // we need to pass the first few values of memory, public memory is enough
    )?;

    let extension_dims = vec![
        ColDims::padded(public_memory.len() + private_memory_len, EF::ZERO), // memory pushwordard
        ColDims::padded(
            (public_memory.len() + private_memory_len).div_ceil(VECTOR_LEN),
            EF::ZERO,
        ), // memory (folded) pushwordard
        ColDims::padded(bytecode.instructions.len(), EF::ZERO),              // bytecode pushforward
    ];

    let parsed_commitment_extension = packed_pcs_parse_commitment(
        &second_batched_whir_config_builder(
            whir_config_builder.clone(),
            parsed_commitment_base.num_variables,
            num_packed_vars_for_dims::<EF>(&extension_dims, LOG_SMALLEST_DECOMPOSITION_CHUNK),
        ),
        &mut verifier_state,
        &extension_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    )?;

    let mut normal_lookup_statements = normal_lookup_into_memory.step_2(&mut verifier_state, log_memory)?;

    let vectorized_lookup_statements = vectorized_lookup_into_memory.step_2(&mut verifier_state, log_memory)?;

    let bytecode_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log2_ceil_usize(bytecode.instructions.len()),
        table_heights[&Table::execution()].log_padded(),
        &[bytecode_lookup_claim_1],
        EF::ONE,
    )?;
    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);
    if folded_bytecode.evaluate(&bytecode_logup_star_statements.on_table.point)
        != bytecode_logup_star_statements.on_table.value
    {
        return Err(ProofError::InvalidProof);
    }
    let memory_statements = vec![
        normal_lookup_statements.on_table.clone(),
        vectorized_lookup_statements.on_table.clone(),
    ];

    let mut final_statements: BTreeMap<Table, Vec<_>> = Default::default();
    for table in table_heights.keys() {
        final_statements.insert(
            *table,
            table.committed_statements_verifier(
                &mut verifier_state,
                &air_points[table],
                &evals_f[table],
                &evals_ef[table],
                &mut normal_lookup_statements.on_indexes_f,
                &mut normal_lookup_statements.on_indexes_ef,
            )?,
        );
    }
    assert!(normal_lookup_statements.on_indexes_f.is_empty());
    assert!(normal_lookup_statements.on_indexes_ef.is_empty());

    let p16_gkr = verify_poseidon_gkr(
        &mut verifier_state,
        table_heights[&Table::poseidon16_core()].log_padded(),
        &air_points[&Table::poseidon16_core()].0,
        &p16_gkr_layers,
        UNIVARIATE_SKIPS,
        true,
    );
    assert_eq!(&p16_gkr.output_statements.point, &air_points[&Table::poseidon16_core()]);
    assert_eq!(
        &p16_gkr.output_statements.values,
        &evals_f[&Table::poseidon16_core()][POSEIDON_16_CORE_COL_OUTPUT_START..][..16]
    );

    let p24_gkr = verify_poseidon_gkr(
        &mut verifier_state,
        table_heights[&Table::poseidon24_core()].log_padded(),
        &air_points[&Table::poseidon24_core()].0,
        &p24_gkr_layers,
        UNIVARIATE_SKIPS,
        false,
    );
    assert_eq!(&p24_gkr.output_statements.point, &air_points[&Table::poseidon24_core()]);
    assert_eq!(
        &p24_gkr.output_statements.values[16..],
        &evals_f[&Table::poseidon24_core()][POSEIDON_24_CORE_COL_OUTPUT_START..][..8]
    );

    {
        let mut cursor = 0;
        for table in table_heights.keys() {
            for (statement, lookup) in vectorized_lookup_statements.on_indexes[cursor..]
                .iter()
                .zip(table.vector_lookups())
            {
                final_statements.get_mut(table).unwrap()[lookup.index].extend(statement.clone());
            }
            cursor += table.num_vector_lookups();
        }
    }

    let (initial_pc_statement, final_pc_statement) =
        initial_and_final_pc_conditions(table_heights[&Table::execution()].log_padded());

    final_statements.get_mut(&Table::execution()).unwrap()[ExecutionTable.find_committed_column_index_f(COL_INDEX_PC)]
        .extend(vec![
            bytecode_logup_star_statements.on_indexes.clone(),
            initial_pc_statement,
            final_pc_statement,
        ]);
    let statements_p16_core = final_statements.get_mut(&Table::poseidon16_core()).unwrap();
    for (stmts, gkr_value) in statements_p16_core[POSEIDON_16_CORE_COL_INPUT_START..][..16]
        .iter_mut()
        .zip(&p16_gkr.input_statements.values)
    {
        stmts.push(Evaluation::new(p16_gkr.input_statements.point.clone(), *gkr_value));
    }
    statements_p16_core[POSEIDON_16_CORE_COL_COMPRESSION].push(p16_gkr.on_compression_selector.unwrap());

    let statements_p24_core = final_statements.get_mut(&Table::poseidon24_core()).unwrap();
    for (stmts, gkr_value) in statements_p24_core[POSEIDON_24_CORE_COL_INPUT_START..][..24]
        .iter_mut()
        .zip(&p24_gkr.input_statements.values)
    {
        stmts.push(Evaluation::new(p24_gkr.input_statements.point.clone(), *gkr_value));
    }

    let mut all_base_statements = [
        vec![memory_statements],
        encapsulate_vec(p16_gkr.cubes_statements.split()),
        encapsulate_vec(p24_gkr.cubes_statements.split()),
    ]
    .concat();
    all_base_statements.extend(final_statements.into_values().flatten());
    let global_statements_base = packed_pcs_global_statements_for_verifier(
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &all_base_statements,
        &mut verifier_state,
        &[(0, public_memory.clone())].into_iter().collect(),
    )?;

    let global_statements_extension = packed_pcs_global_statements_for_verifier(
        &extension_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &[
            normal_lookup_statements.on_pushforward,
            vectorized_lookup_statements.on_pushforward,
            bytecode_logup_star_statements.on_pushforward,
        ],
        &mut verifier_state,
        &Default::default(),
    )?;

    WhirConfig::new(whir_config_builder, parsed_commitment_base.num_variables).batch_verify(
        &mut verifier_state,
        &parsed_commitment_base,
        global_statements_base,
        &parsed_commitment_extension,
        global_statements_extension,
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

    let bus_virtual_statement = {
        let mut bus_evals = vec![];
        for degree in Air::degrees(t) {
            bus_evals.push(
                bus_final_values
                    .iter()
                    .zip(t.buses())
                    .filter_map(|(eval, bus)| (bus.degree == degree).then(|| *eval))
                    .collect::<Vec<_>>(),
            );
        }
        assert_eq!(bus_evals.len(), Air::degrees(t).len());
        (bus_point, bus_evals)
    };
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
    };


    dbg!(t.name());

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
