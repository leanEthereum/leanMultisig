use air::table::AirTable;
use multilinear_toolkit::prelude::*;
use p3_air::BaseAir;
use p3_field::PrimeField64;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_symmetric::Permutation;
use packed_pcs::{
    ColDims, packed_pcs_commit, packed_pcs_global_statements_for_prover,
    packed_pcs_global_statements_for_verifier, packed_pcs_parse_commitment,
};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::collections::BTreeMap;
use std::fmt;
use std::time::{Duration, Instant};
use utils::{
    MyChallenger, Poseidon16Air, Poseidon24Air, build_poseidon_16_air,
    build_poseidon_16_air_packed, build_poseidon_24_air, build_poseidon_24_air_packed,
    build_prover_state, build_verifier_state, generate_trace_poseidon_16,
    generate_trace_poseidon_24, get_poseidon16, get_poseidon24, init_tracing,
};
use whir_p3::{
    FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder, precompute_dft_twiddles,
};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

#[derive(Clone, Debug)]
pub struct Poseidon2Benchmark {
    pub log_n_poseidons_16: usize,
    pub log_n_poseidons_24: usize,
    pub prover_time: Duration,
    pub verifier_time: Duration,
    pub proof_size: f64, // in bytes
}

impl fmt::Display for Poseidon2Benchmark {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Proved {} poseidon2-16 and {} poseidon2-24 in {:.3} s ({} / s)",
            1 << self.log_n_poseidons_16,
            1 << self.log_n_poseidons_24,
            self.prover_time.as_millis() as f64 / 1000.0,
            (f64::from((1 << self.log_n_poseidons_16) + (1 << self.log_n_poseidons_24))
                / self.prover_time.as_secs_f64())
            .round() as usize
        )?;
        writeln!(
            f,
            "Proof size: {:.1} KiB (not optimized)",
            self.proof_size / 1024.0
        )?;
        writeln!(f, "Verification: {} ms", self.verifier_time.as_millis())
    }
}

#[derive(Clone, Debug)]
pub struct Poseidon2Config {
    pub log_n_poseidons_16: usize,
    pub log_n_poseidons_24: usize,
    pub univariate_skips: usize,
    pub folding_factor: FoldingFactor,
    pub log_inv_rate: usize,
    pub soundness_type: SecurityAssumption,
    pub pow_bits: usize,
    pub security_level: usize,
    pub rs_domain_initial_reduction_factor: usize,
    pub max_num_variables_to_send_coeffs: usize,
    pub display_logs: bool,
}

struct PoseidonSetup {
    n_columns_16: usize,
    n_columns_24: usize,
    witness_columns_16: Vec<Vec<F>>,
    witness_columns_24: Vec<Vec<F>>,
    table_16: AirTable<EF, Poseidon16Air<F>, Poseidon16Air<PFPacking<F>>>,
    table_24: AirTable<EF, Poseidon24Air<F>, Poseidon24Air<PFPacking<F>>>,
}

struct ProverArtifacts {
    prover_time: Duration,
    whir_config_builder: WhirConfigBuilder,
    whir_config: WhirConfig<EF>,
    dims: Vec<ColDims<F>>,
}

fn prepare_poseidon(config: &Poseidon2Config) -> PoseidonSetup {
    let n_poseidons_16 = 1 << config.log_n_poseidons_16;
    let n_poseidons_24 = 1 << config.log_n_poseidons_24;

    let poseidon_air_16 = build_poseidon_16_air();
    let poseidon_air_16_packed = build_poseidon_16_air_packed();
    let poseidon_air_24 = build_poseidon_24_air();
    let poseidon_air_24_packed = build_poseidon_24_air_packed();

    let n_columns_16 = poseidon_air_16.width();
    let n_columns_24 = poseidon_air_24.width();

    let mut rng = StdRng::seed_from_u64(0);
    let inputs_16: Vec<[F; 16]> = (0..n_poseidons_16).map(|_| Default::default()).collect();
    let inputs_24: Vec<[F; 24]> = (0..n_poseidons_24)
        .map(|_| std::array::from_fn(|_| rng.random()))
        .collect();
    let compress = vec![true; n_poseidons_16];
    let index_res: Vec<usize> = vec![0; n_poseidons_16]; // unused

    let witness_matrix_16 = generate_trace_poseidon_16(&inputs_16, &compress, &index_res);
    let witness_matrix_24 = generate_trace_poseidon_24(&inputs_24);

    assert_eq!(
        &witness_matrix_16.values[n_columns_16 - 16..n_columns_16 - 8],
        &get_poseidon16().permute(witness_matrix_16.values[0..16].try_into().unwrap())[..8]
    );
    assert_eq!(
        &witness_matrix_24.values[n_columns_24 - 8..n_columns_24],
        &get_poseidon24().permute(witness_matrix_24.values[0..24].try_into().unwrap())[16..]
    );

    let witness_matrix_16_transposed = witness_matrix_16.transpose();
    let witness_matrix_24_transposed = witness_matrix_24.transpose();

    let witness_columns_16 = (0..n_columns_16)
        .map(|row| {
            witness_matrix_16_transposed.values[row * n_poseidons_16..(row + 1) * n_poseidons_16]
                .to_vec()
        })
        .collect::<Vec<_>>();
    let witness_columns_24 = (0..n_columns_24)
        .map(|row| {
            witness_matrix_24_transposed.values[row * n_poseidons_24..(row + 1) * n_poseidons_24]
                .to_vec()
        })
        .collect::<Vec<_>>();

    let table_16: AirTable<EF, Poseidon16Air<F>, Poseidon16Air<PFPacking<F>>> =
        AirTable::new(poseidon_air_16, poseidon_air_16_packed);
    let table_24: AirTable<EF, Poseidon24Air<F>, Poseidon24Air<PFPacking<F>>> =
        AirTable::new(poseidon_air_24, poseidon_air_24_packed);

    PoseidonSetup {
        n_columns_16,
        n_columns_24,
        witness_columns_16,
        witness_columns_24,
        table_16,
        table_24,
    }
}

fn run_prover_phase(
    config: &Poseidon2Config,
    setup: &PoseidonSetup,
    witness_16: &[&[F]],
    witness_24: &[&[F]],
    prover_state: &mut FSProver<EF, MyChallenger>,
) -> ProverArtifacts {
    let start = Instant::now();

    let whir_config_builder = WhirConfigBuilder {
        folding_factor: config.folding_factor,
        soundness_type: config.soundness_type,
        pow_bits: config.pow_bits,
        max_num_variables_to_send_coeffs: config.max_num_variables_to_send_coeffs,
        rs_domain_initial_reduction_factor: config.rs_domain_initial_reduction_factor,
        security_level: config.security_level,
        starting_log_inv_rate: config.log_inv_rate,
    };

    precompute_dft_twiddles::<F>(1 << 24);

    let dims = [
        vec![ColDims::full(config.log_n_poseidons_16); setup.n_columns_16],
        vec![ColDims::full(config.log_n_poseidons_24); setup.n_columns_24],
    ]
    .concat();
    let log_smallest_decomposition_chunk = 0;
    let commited_slices = setup
        .witness_columns_16
        .iter()
        .chain(setup.witness_columns_24.iter())
        .map(Vec::as_slice)
        .collect::<Vec<_>>();

    let commitment_witness = packed_pcs_commit(
        &whir_config_builder,
        &commited_slices,
        &dims,
        prover_state,
        log_smallest_decomposition_chunk,
    );

    let (p16_point, evaluations_remaining_to_prove_16) =
        setup
            .table_16
            .prove_base(prover_state, config.univariate_skips, witness_16);
    let (p24_point, evaluations_remaining_to_prove_24) =
        setup
            .table_24
            .prove_base(prover_state, config.univariate_skips, witness_24);

    let global_statements_to_prove = packed_pcs_global_statements_for_prover(
        &commited_slices,
        &dims,
        log_smallest_decomposition_chunk,
        &evaluations_remaining_to_prove_16
            .into_iter()
            .map(|v| vec![Evaluation::new(p16_point.clone(), v)])
            .chain(
                evaluations_remaining_to_prove_24
                    .into_iter()
                    .map(|v| vec![Evaluation::new(p24_point.clone(), v)]),
            )
            .collect::<Vec<_>>(),
        prover_state,
    );
    let whir_config = WhirConfig::new(
        whir_config_builder.clone(),
        commitment_witness.packed_polynomial.by_ref().n_vars(),
    );
    whir_config.prove(
        prover_state,
        global_statements_to_prove,
        commitment_witness.inner_witness,
        &commitment_witness.packed_polynomial.by_ref(),
    );

    ProverArtifacts {
        prover_time: start.elapsed(),
        whir_config_builder,
        whir_config,
        dims,
    }
}

fn run_verifier_phase(
    config: &Poseidon2Config,
    setup: &PoseidonSetup,
    artifacts: &ProverArtifacts,
    prover_state: &FSProver<EF, MyChallenger>,
) -> Duration {
    let start = Instant::now();
    let mut verifier_state = build_verifier_state(prover_state);
    let log_smallest_decomposition_chunk = 0; // unused (everything is power of two)

    let packed_parsed_commitment = packed_pcs_parse_commitment(
        &artifacts.whir_config_builder,
        &mut verifier_state,
        &artifacts.dims,
        log_smallest_decomposition_chunk,
    )
    .unwrap();

    let (p16_point, evaluations_remaining_to_verify_16) = setup
        .table_16
        .verify(
            &mut verifier_state,
            config.univariate_skips,
            config.log_n_poseidons_16,
        )
        .unwrap();
    let (p24_point, evaluations_remaining_to_verify_24) = setup
        .table_24
        .verify(
            &mut verifier_state,
            config.univariate_skips,
            config.log_n_poseidons_24,
        )
        .unwrap();

    let global_statements_to_verify = packed_pcs_global_statements_for_verifier(
        &artifacts.dims,
        log_smallest_decomposition_chunk,
        &evaluations_remaining_to_verify_16
            .into_iter()
            .map(|v| vec![Evaluation::new(p16_point.clone(), v)])
            .chain(
                evaluations_remaining_to_verify_24
                    .into_iter()
                    .map(|v| vec![Evaluation::new(p24_point.clone(), v)]),
            )
            .collect::<Vec<_>>(),
        &mut verifier_state,
        &BTreeMap::default(),
    )
    .unwrap();
    artifacts
        .whir_config
        .verify(
            &mut verifier_state,
            &packed_parsed_commitment,
            global_statements_to_verify,
        )
        .unwrap();

    start.elapsed()
}

#[must_use]
pub fn prove_poseidon2(config: &Poseidon2Config) -> Poseidon2Benchmark {
    if config.display_logs {
        init_tracing();
    }

    let setup = prepare_poseidon(config);

    let mut prover_state = build_prover_state();
    let artifacts = run_prover_phase(
        config,
        &setup,
        &setup
            .witness_columns_16
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>(),
        &setup
            .witness_columns_24
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>(),
        &mut prover_state,
    );
    let verifier_time = run_verifier_phase(config, &setup, &artifacts, &prover_state);

    let proof_size = prover_state.proof_data().len() as f64 * (F::ORDER_U64 as f64).log2() / 8.0;

    Poseidon2Benchmark {
        log_n_poseidons_16: config.log_n_poseidons_16,
        log_n_poseidons_24: config.log_n_poseidons_24,
        prover_time: artifacts.prover_time,
        verifier_time,
        proof_size,
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_prove_poseidon2() {
        let config = Poseidon2Config {
            log_n_poseidons_16: 13,
            log_n_poseidons_24: 12,
            univariate_skips: 4,
            folding_factor: FoldingFactor::new(5, 3),
            log_inv_rate: 2,
            soundness_type: SecurityAssumption::CapacityBound,
            pow_bits: 13,
            security_level: 128,
            rs_domain_initial_reduction_factor: 1,
            max_num_variables_to_send_coeffs: 7,
            display_logs: false,
        };
        let benchmark = prove_poseidon2(&config);
        println!("\n{benchmark}");
    }
}
