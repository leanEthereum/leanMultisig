use air::{check_air_validity, prove_air, verify_air};
use backend::*;
use blake3_air::{Blake3Air, NUM_BLAKE3_COLS, generate_blake3_trace};
use utils::{
    build_prover_state, build_verifier_state, collect_refs, init_tracing, padd_with_zero_to_next_power_of_two,
};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

#[test]
fn test_benchmark_air_blake3() {
    benchmark_prove_blake3(8, false);
}

#[allow(clippy::too_many_lines)]
pub fn benchmark_prove_blake3(log_n_rows: usize, tracing: bool) {
    if tracing {
        init_tracing();
    }
    let n_rows = 1 << log_n_rows;

    let trace = generate_blake3_trace::<F>(n_rows);

    let air = Blake3Air;

    check_air_validity::<_, EF>(&air, &vec![], &collect_refs(&trace), &[] as &[&[EF]]).unwrap();

    let whir_config = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 123,
        starting_log_inv_rate: 1,
    };

    let mut prover_state = build_prover_state();

    let packed_n_vars = log2_ceil_usize(NUM_BLAKE3_COLS << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config, packed_n_vars);

    let time = std::time::Instant::now();

    {
        let mut committed_pol = F::zero_vec((NUM_BLAKE3_COLS << log_n_rows).next_power_of_two());
        for (i, col) in trace.iter().enumerate() {
            committed_pol[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col);
        }
        let committed_pol = MleOwned::Base(committed_pol);
        let witness = whir_config.commit(&mut prover_state, &committed_pol, NUM_BLAKE3_COLS << log_n_rows);

        let alpha = prover_state.sample();
        let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints() + 1);

        let air_claims = prove_air::<EF, _>(
            &mut prover_state,
            &air,
            air_alpha_powers,
            &collect_refs(&trace),
            &[] as &[&[EF]],
            None,
            true,
        );
        assert!(air_claims.down_point.is_none());
        assert_eq!(air_claims.evals_f.len(), air.n_columns_air());

        let betas = prover_state.sample_vec(log2_ceil_usize(NUM_BLAKE3_COLS));
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
        "{} Blake3 hashes / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );
    let proof_size = (prover_state.pruned_proof().proof_size_fe() * 31 / 8) / 1024;
    println!("Proof size: {} KB", proof_size);
    

    {
        let mut verifier_state = build_verifier_state(prover_state);

        let parsed_commitment = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();

        let alpha = verifier_state.sample();
        let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints() + 1);

        let air_claims = verify_air(
            &mut verifier_state,
            &air,
            air_alpha_powers,
            log2_ceil_usize(n_rows),
            None,
        )
        .unwrap();

        let betas = verifier_state.sample_vec(log2_ceil_usize(NUM_BLAKE3_COLS));
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
