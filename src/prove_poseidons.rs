use air::{check_air_validity, prove_air, verify_air};
use lean_vm::{
    EF, ExtraDataForBuses, F, POSEIDON_16_COL_A, POSEIDON_16_COL_B, POSEIDON_16_COL_FLAG, POSEIDON_16_COL_INPUT_START,
    POSEIDON_16_COL_RES, POSEIDON_16_NULL_HASH_PTR, Poseidon16Precompile, ZERO_VEC_PTR, fill_trace_poseidon_16,
    num_cols_poseidon_16,
};
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{
    build_prover_state, build_verifier_state, collect_refs, init_tracing, padd_with_zero_to_next_power_of_two,
};

const WIDTH: usize = 16;
const UNIVARIATE_SKIPS: usize = 3;

#[test]
fn test_benchmark_air_poseidon_16() {
    benchmark_prove_poseidon_16(11, false);
}

#[allow(clippy::too_many_lines)]
pub fn benchmark_prove_poseidon_16(log_n_rows: usize, tracing: bool) {
    if tracing {
        init_tracing();
    }
    let n_rows = 1 << log_n_rows;
    let mut rng = StdRng::seed_from_u64(0);
    let mut trace = vec![vec![F::ZERO; n_rows]; num_cols_poseidon_16()];
    for t in trace.iter_mut().skip(POSEIDON_16_COL_INPUT_START).take(WIDTH) {
        *t = (0..n_rows).map(|_| rng.random()).collect();
    }
    trace[POSEIDON_16_COL_FLAG] = (0..n_rows).map(|_| F::ONE).collect();
    trace[POSEIDON_16_COL_RES] = (0..n_rows).map(|_| F::from_usize(POSEIDON_16_NULL_HASH_PTR)).collect();
    trace[POSEIDON_16_COL_A] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR)).collect();
    trace[POSEIDON_16_COL_B] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR)).collect();
    fill_trace_poseidon_16(&mut trace);

    let whir_config = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 123,
        starting_log_inv_rate: 1,
    };

    let air = Poseidon16Precompile::<false>;

    check_air_validity(
        &air,
        &ExtraDataForBuses::default(),
        &collect_refs(&trace),
        &[] as &[&[EF]],
        &[],
        &[],
    )
    .unwrap();

    let mut prover_state = build_prover_state();

    let packed_n_vars = log2_ceil_usize(num_cols_poseidon_16() << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config, packed_n_vars);

    let time = std::time::Instant::now();

    {
        let mut commitmed_pol = F::zero_vec((num_cols_poseidon_16() << log_n_rows).next_power_of_two());
        for (i, col) in trace.iter().enumerate() {
            commitmed_pol[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col);
        }
        let committed_pol = MleOwned::Base(commitmed_pol);
        let witness = whir_config.commit(&mut prover_state, &committed_pol);

        let alpha = prover_state.sample();
        let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints() + 1);
        let extra_data = ExtraDataForBuses {
            alpha_powers: air_alpha_powers,
            ..Default::default()
        };

        let air_claims = prove_air::<EF, _>(
            &mut prover_state,
            &air,
            extra_data,
            UNIVARIATE_SKIPS,
            &collect_refs(&trace),
            &[] as &[&[EF]],
            None,
            true,
        );
        assert!(air_claims.down_point.is_none());
        assert_eq!(air_claims.evals_f.len(), air.n_columns_air());

        let betas = prover_state.sample_vec(log2_ceil_usize(num_cols_poseidon_16()));
        let packed_point = MultilinearPoint([betas.clone(), air_claims.point.0].concat());
        let packed_eval = padd_with_zero_to_next_power_of_two(&air_claims.evals_f).evaluate(&MultilinearPoint(betas));

        whir_config.prove(
            &mut prover_state,
            vec![SparseStatement::dense(packed_point, packed_eval)],
            witness,
            &committed_pol.by_ref(),
        );
    }

    println!(
        "{} Poseidons / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );

    {
        let mut verifier_state = build_verifier_state(prover_state);

        let parsed_commitment = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();

        let alpha = verifier_state.sample();
        let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints() + 1);
        let extra_data = ExtraDataForBuses {
            alpha_powers: air_alpha_powers,
            ..Default::default()
        };
        let air_claims = verify_air(
            &mut verifier_state,
            &air,
            extra_data,
            UNIVARIATE_SKIPS,
            log2_ceil_usize(n_rows),
            None,
        )
        .unwrap();

        let betas = verifier_state.sample_vec(log2_ceil_usize(num_cols_poseidon_16()));
        let packed_point = MultilinearPoint([betas.clone(), air_claims.point.0].concat());
        let packed_eval = padd_with_zero_to_next_power_of_two(&air_claims.evals_f).evaluate(&MultilinearPoint(betas));

        whir_config
            .verify(
                &mut verifier_state,
                &parsed_commitment,
                vec![SparseStatement::dense(packed_point, packed_eval)],
            )
            .unwrap();
    }
}
