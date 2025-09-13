use air::table::AirTable;
use air::witness::AirWitness;
use p3_air::BaseAir;
use p3_field::PrimeField64;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_symmetric::Permutation;
use p3_util::log2_ceil_usize;
use pcs::{
    ColDims, PCS, packed_pcs_commit, packed_pcs_global_statements_for_prover,
    packed_pcs_global_statements_for_verifier, packed_pcs_parse_commitment,
};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::fmt;
use std::marker::PhantomData;
use std::time::{Duration, Instant};
use utils::{
    build_merkle_compress, build_merkle_hash, build_poseidon_16_air, build_poseidon_16_air_packed,
    build_poseidon_24_air, build_poseidon_24_air_packed, build_prover_state, build_verifier_state,
    generate_trace_poseidon_16, generate_trace_poseidon_24, get_poseidon16, get_poseidon24,
    init_tracing, padd_with_zero_to_next_power_of_two,
};
use whir_p3::dft::EvalsDft;
use whir_p3::whir::config::{FoldingFactor, SecurityAssumption, WhirConfigBuilder};

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
            (((1 << self.log_n_poseidons_16) + (1 << self.log_n_poseidons_24)) as f64
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

pub fn prove_poseidon2(
    log_n_poseidons_16: usize,
    log_n_poseidons_24: usize,
    univariate_skips: usize,
    folding_factor: FoldingFactor,
    log_inv_rate: usize,
    soundness_type: SecurityAssumption,
    pow_bits: usize,
    security_level: usize,
    rs_domain_initial_reduction_factor: usize,
    max_num_variables_to_send_coeffs: usize,
    display_logs: bool,
) -> Poseidon2Benchmark {
    if display_logs {
        init_tracing();
    }

    let n_poseidons_16 = 1 << log_n_poseidons_16;
    let n_poseidons_24 = 1 << log_n_poseidons_24;

    let poseidon_air_16 = build_poseidon_16_air();
    let poseidon_air_16_packed = build_poseidon_16_air_packed();
    let poseidon_air_24 = build_poseidon_24_air();
    let poseidon_air_24_packed = build_poseidon_24_air_packed();

    let n_columns_16 = poseidon_air_16.width();
    let n_columns_24 = poseidon_air_24.width();
    let log_table_area_16 = log_n_poseidons_16 + log2_ceil_usize(n_columns_16);
    let log_table_area_24 = log_n_poseidons_24 + log2_ceil_usize(n_columns_24);

    let mut rng = StdRng::seed_from_u64(0);
    let inputs_16: Vec<[F; 16]> = (0..n_poseidons_16).map(|_| Default::default()).collect();
    let inputs_24: Vec<[F; 24]> = (0..n_poseidons_24)
        .map(|_| std::array::from_fn(|_| rng.random()))
        .collect();

    let witness_matrix_16 = generate_trace_poseidon_16(inputs_16);
    let witness_matrix_24 = generate_trace_poseidon_24(inputs_24);

    assert_eq!(
        &witness_matrix_16.values[n_columns_16 - 16..n_columns_16],
        get_poseidon16().permute(witness_matrix_16.values[0..16].try_into().unwrap())
    );
    assert_eq!(
        &witness_matrix_24.values[n_columns_24 - 24..n_columns_24],
        get_poseidon24().permute(witness_matrix_24.values[0..24].try_into().unwrap())
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
    let column_groups_16 = vec![0..n_columns_16];
    let column_groups_24 = vec![0..n_columns_24];
    let witness_16 = AirWitness::new(&witness_columns_16, &column_groups_16);
    let witness_24 = AirWitness::new(&witness_columns_24, &column_groups_24);

    let table_16 = AirTable::<EF, _, _>::new(poseidon_air_16, poseidon_air_16_packed);
    let table_24 = AirTable::<EF, _, _>::new(poseidon_air_24, poseidon_air_24_packed);

    let t = Instant::now();

    let mut prover_state = build_prover_state();

    let pcs = WhirConfigBuilder {
        folding_factor,
        soundness_type,
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        pow_bits,
        max_num_variables_to_send_coeffs,
        rs_domain_initial_reduction_factor,
        security_level,
        starting_log_inv_rate: log_inv_rate,
        base_field: PhantomData::<F>,
        extension_field: PhantomData::<EF>,
    };

    // let pcs = RingSwitching::<F, EF, _, EXTENSION_DEGREE>::new(pcs);
    let dft = EvalsDft::new(
        1 << (log2_ceil_usize(n_columns_24)
            + log_n_poseidons_16.max(log_n_poseidons_24)
            + log_inv_rate
            - pcs.folding_factor.at_round(0)),
    );

    let commited_trace_polynomial_16 =
        padd_with_zero_to_next_power_of_two(&witness_columns_16.concat());
    let commited_trace_polynomial_24 =
        padd_with_zero_to_next_power_of_two(&witness_columns_24.concat());

    let dims = [
        ColDims::dense(log_table_area_16),
        ColDims::dense(log_table_area_24),
    ];
    let log_smallest_decomposition_chunk = 0; // UNUSED because verything is power of 2

    let commited_data = [
        commited_trace_polynomial_16.as_slice(),
        commited_trace_polynomial_24.as_slice(),
    ];
    let commitment_witness =
        packed_pcs_commit(&pcs, &commited_data, &dims, &dft, &mut prover_state, 0);

    let evaluations_remaining_to_prove_16 =
        table_16.prove_base(&mut prover_state, univariate_skips, witness_16);
    let evaluations_remaining_to_prove_24 =
        table_24.prove_base(&mut prover_state, univariate_skips, witness_24);

    let global_statements_to_prove = packed_pcs_global_statements_for_prover(
        &commited_data,
        &dims,
        log_smallest_decomposition_chunk,
        &[
            evaluations_remaining_to_prove_16,
            evaluations_remaining_to_prove_24,
        ],
        &mut prover_state,
    );
    pcs.open(
        &dft,
        &mut prover_state,
        &global_statements_to_prove,
        commitment_witness.inner_witness,
        &commitment_witness.packed_polynomial,
    );

    let prover_time = t.elapsed();
    let time = Instant::now();

    let mut verifier_state = build_verifier_state(&prover_state);

    let packed_parsed_commitment = packed_pcs_parse_commitment(
        &pcs,
        &mut verifier_state,
        &dims,
        log_smallest_decomposition_chunk,
    )
    .unwrap();

    let evaluations_remaining_to_verify_16 = table_16
        .verify(
            &mut verifier_state,
            univariate_skips,
            log_n_poseidons_16,
            &column_groups_16,
        )
        .unwrap();
    let evaluations_remaining_to_verify_24 = table_24
        .verify(
            &mut verifier_state,
            univariate_skips,
            log_n_poseidons_24,
            &column_groups_24,
        )
        .unwrap();

    let global_statements_to_verify = packed_pcs_global_statements_for_verifier(
        &dims,
        log_smallest_decomposition_chunk,
        &[
            evaluations_remaining_to_verify_16,
            evaluations_remaining_to_verify_24,
        ],
        &mut verifier_state,
        &Default::default(),
    )
    .unwrap();
    pcs.verify(
        &mut verifier_state,
        &packed_parsed_commitment,
        &global_statements_to_verify,
    )
    .unwrap();

    let verifier_time = time.elapsed();

    let proof_size = prover_state.proof_data().len() as f64 * (F::ORDER_U64 as f64).log2() / 8.0;

    Poseidon2Benchmark {
        log_n_poseidons_16,
        log_n_poseidons_24,
        prover_time,
        verifier_time,
        proof_size,
    }
}

#[cfg(test)]
mod tests {
    use whir_p3::whir::config::{FoldingFactor, SecurityAssumption};

    use super::*;

    #[test]
    fn test_prove_poseidon2() {
        let benchmark = prove_poseidon2(
            13,
            12,
            4,
            FoldingFactor::ConstantFromSecondRound(5, 3),
            2,
            SecurityAssumption::CapacityBound,
            13,
            128,
            1,
            5,
            false,
        );
        println!("\n{benchmark}");
    }
}
