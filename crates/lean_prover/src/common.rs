use multilinear_toolkit::prelude::*;
use p3_field::{Algebra, BasedVectorSpace};
use p3_field::{ExtensionField, PrimeCharacteristicRing};
use p3_util::log2_ceil_usize;
use packed_pcs::ColDims;

use crate::*;
use lean_vm::*;

pub fn get_base_dims(
    n_cycles: usize,
    log_public_memory: usize,
    private_memory_len: usize,
    bytecode_ending_pc: usize,
    poseidon_counts: (usize, usize),
    poseidon_widths: (usize, usize),
    n_rows_table_dot_products: usize,
) -> Vec<ColDims<F>> {
    let (n_poseidons_16, n_poseidons_24) = poseidon_counts;
    let (p16_air_width, p24_air_width) = poseidon_widths;
    let (default_p16_row, default_p24_row) = build_poseidon_columns(
        &[WitnessPoseidon16::poseidon_of_zero()],
        &[WitnessPoseidon24::poseidon_of_zero()],
    );

    [
        vec![
            ColDims::padded_with_public_data(Some(log_public_memory), private_memory_len, F::ZERO), //  memory
            ColDims::padded(n_cycles, F::from_usize(bytecode_ending_pc)), // pc
            ColDims::padded(n_cycles, F::ZERO),                           // fp
            ColDims::padded(n_cycles, F::ZERO),                           // mem_addr_a
            ColDims::padded(n_cycles, F::ZERO),                           // mem_addr_b
            ColDims::padded(n_cycles, F::ZERO),                           // mem_addr_c
            ColDims::padded(n_poseidons_16, F::from_usize(ZERO_VEC_PTR)), // poseidon16 index a
            ColDims::padded(n_poseidons_16, F::from_usize(ZERO_VEC_PTR)), // poseidon16 index b
            ColDims::padded(n_poseidons_24, F::from_usize(ZERO_VEC_PTR)), // poseidon24 index a
            ColDims::padded(n_poseidons_24, F::from_usize(ZERO_VEC_PTR)), // poseidon24 index b
            ColDims::padded(n_poseidons_24, F::from_usize(POSEIDON_24_NULL_HASH_PTR)), // poseidon24 index res
        ],
        (0..p16_air_width - 16 * 2)
            .map(|i| ColDims::padded(n_poseidons_16, default_p16_row[16 + i][0]))
            .collect::<Vec<_>>(), // rest of poseidon16 table
        (0..p24_air_width - 24 * 2)
            .map(|i| ColDims::padded(n_poseidons_24, default_p24_row[24 + i][0]))
            .collect::<Vec<_>>(), // rest of poseidon24 table
        vec![
            ColDims::padded(n_rows_table_dot_products, F::ONE), // dot product: (start) flag
            ColDims::padded(n_rows_table_dot_products, F::ONE), // dot product: length
            ColDims::padded(n_rows_table_dot_products, F::ZERO), // dot product: index a
            ColDims::padded(n_rows_table_dot_products, F::ZERO), // dot product: index b
            ColDims::padded(n_rows_table_dot_products, F::ZERO), // dot product: index res
        ],
        vec![ColDims::padded(n_rows_table_dot_products, F::ZERO); DIMENSION], // dot product: computation
    ]
    .concat()
}

pub fn fold_bytecode(bytecode: &Bytecode, folding_challenges: &MultilinearPoint<EF>) -> Vec<EF> {
    let encoded_bytecode = padd_with_zero_to_next_power_of_two(
        &bytecode
            .instructions
            .par_iter()
            .flat_map(|i| padd_with_zero_to_next_power_of_two(&field_representation(i)))
            .collect::<Vec<_>>(),
    );
    fold_multilinear_chunks(&encoded_bytecode, folding_challenges)
}

pub fn intitial_and_final_pc_conditions(
    bytecode: &Bytecode,
    log_n_cycles: usize,
) -> (Evaluation<EF>, Evaluation<EF>) {
    let initial_pc_statement = Evaluation::new(EF::zero_vec(log_n_cycles), EF::ZERO);
    let final_pc_statement = Evaluation::new(
        vec![EF::ONE; log_n_cycles],
        EF::from_usize(bytecode.ending_pc),
    );
    (initial_pc_statement, final_pc_statement)
}

pub fn add_memory_statements_for_dot_product_precompile(
    entry: &RowMultilinearEval,
    log_memory: usize,
    log_public_memory: usize,
    challenger: &mut impl ChallengeSampler<EF>,
    memory_statements: &mut Vec<Evaluation<EF>>,
) -> Result<(), ProofError> {
    // point lookup into memory
    let log_point_len = log2_ceil_usize(entry.n_vars() * DIMENSION);
    let point_random_challenge = challenger.sample_vec(log_point_len);
    let point_random_value = {
        let mut point_mle = flatten_scalars_to_base::<PF<EF>, EF>(&entry.point);
        point_mle.resize(point_mle.len().next_power_of_two(), F::ZERO);
        point_mle.evaluate(&MultilinearPoint(point_random_challenge.clone()))
    };
    memory_statements.push(Evaluation::new(
        [
            to_big_endian_in_field(entry.addr_point, log_memory - log_point_len),
            point_random_challenge.clone(),
        ]
        .concat(),
        point_random_value,
    ));

    // result lookup into memory
    let random_challenge = challenger.sample_vec(LOG_VECTOR_LEN);
    let res_random_value = {
        let mut res_mle = entry.res.as_basis_coefficients_slice().to_vec();
        res_mle.resize(VECTOR_LEN, F::ZERO);
        res_mle.evaluate(&MultilinearPoint(random_challenge.clone()))
    };
    memory_statements.push(Evaluation::new(
        [
            to_big_endian_in_field(entry.addr_res, log_memory - LOG_VECTOR_LEN),
            random_challenge.clone(),
        ]
        .concat(),
        res_random_value,
    ));

    {
        if entry.n_vars() > log_memory {
            return Err(ProofError::InvalidProof);
        }
        if entry.addr_coeffs >= 1 << (log_memory - entry.n_vars()) {
            return Err(ProofError::InvalidProof);
        }
        if entry.n_vars() >= log_public_memory {
            todo!("vm multilinear eval accross multiple memory chunks")
        }
        let addr_bits = to_big_endian_in_field(entry.addr_coeffs, log_memory - entry.n_vars());
        let statement = Evaluation::new([addr_bits, entry.point.clone()].concat(), entry.res);
        memory_statements.push(statement);
    }

    Ok(())
}

pub struct PrecompileFootprint {
    pub global_challenge: EF,
    pub p16_powers: [EF; 6],
    pub p24_powers: [EF; 5],
    pub dot_product_powers: [EF; 6],
    pub multilinear_eval_powers: [EF; 6],
}

impl PrecompileFootprint {
    fn air_eval<
        PointF: PrimeCharacteristicRing + Copy,
        ResultF: Algebra<EF> + Algebra<PointF> + Copy,
    >(
        &self,
        point: &[PointF],
        mul_point_f_and_ef: impl Fn(PointF, EF) -> ResultF,
    ) -> ResultF {
        let nu_a = (ResultF::ONE - point[COL_INDEX_FLAG_A]) * point[COL_INDEX_MEM_VALUE_A]
            + point[COL_INDEX_FLAG_A] * point[COL_INDEX_OPERAND_A];
        let nu_b = (ResultF::ONE - point[COL_INDEX_FLAG_B]) * point[COL_INDEX_MEM_VALUE_B]
            + point[COL_INDEX_FLAG_B] * point[COL_INDEX_OPERAND_B];
        let nu_c = (ResultF::ONE - point[COL_INDEX_FLAG_C]) * point[COL_INDEX_MEM_VALUE_C]
            + point[COL_INDEX_FLAG_C] * point[COL_INDEX_FP];

        (nu_a * self.p16_powers[2]
            + nu_b * self.p16_powers[3]
            + nu_c * self.p16_powers[4]
            + mul_point_f_and_ef(point[COL_INDEX_AUX], self.p16_powers[5])
            + self.p16_powers[1])
            * point[COL_INDEX_POSEIDON_16]
            + (nu_a * self.p24_powers[2]
                + nu_b * self.p24_powers[3]
                + nu_c * self.p24_powers[4]
                + self.p24_powers[1])
                * point[COL_INDEX_POSEIDON_24]
            + (nu_a * self.dot_product_powers[2]
                + nu_b * self.dot_product_powers[3]
                + nu_c * self.dot_product_powers[4]
                + mul_point_f_and_ef(point[COL_INDEX_AUX], self.dot_product_powers[5])
                + self.dot_product_powers[1])
                * point[COL_INDEX_DOT_PRODUCT]
            + (nu_a * self.multilinear_eval_powers[2]
                + nu_b * self.multilinear_eval_powers[3]
                + nu_c * self.multilinear_eval_powers[4]
                + mul_point_f_and_ef(point[COL_INDEX_AUX], self.multilinear_eval_powers[5])
                + self.multilinear_eval_powers[1])
                * point[COL_INDEX_MULTILINEAR_EVAL]
            + self.global_challenge
    }
}

impl<N: ExtensionField<F>> SumcheckComputation<N, EF> for PrecompileFootprint
where
    EF: ExtensionField<N>,
{
    fn degree(&self) -> usize {
        3
    }
    fn eval(&self, point: &[N], _: &[EF]) -> EF {
        self.air_eval(point, |p, c| c * p)
    }
}

impl SumcheckComputationPacked<EF> for PrecompileFootprint {
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        self.air_eval(point, |p, c| p * c)
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        self.air_eval(point, |p, c| EFPacking::<EF>::from(p) * c)
    }
}

pub struct DotProductFootprint {
    pub global_challenge: EF,
    pub dot_product_challenge: [EF; 6],
}

impl DotProductFootprint {
    fn air_eval<
        PointF: PrimeCharacteristicRing + Copy,
        ResultF: Algebra<EF> + Algebra<PointF> + Copy,
    >(
        &self,
        point: &[PointF],
        mul_point_f_and_ef: impl Fn(PointF, EF) -> ResultF,
    ) -> ResultF {
        (mul_point_f_and_ef(point[2], self.dot_product_challenge[2])
            + mul_point_f_and_ef(point[3], self.dot_product_challenge[3])
            + mul_point_f_and_ef(point[4], self.dot_product_challenge[4])
            + mul_point_f_and_ef(point[1], self.dot_product_challenge[5]))
            * point[0]
            + self.dot_product_challenge[1]
            + self.global_challenge
    }
}

impl<N: ExtensionField<PF<EF>>> SumcheckComputation<N, EF> for DotProductFootprint
where
    EF: ExtensionField<N>,
{
    fn degree(&self) -> usize {
        2
    }

    fn eval(&self, point: &[N], _: &[EF]) -> EF {
        self.air_eval(point, |p, c| c * p)
    }
}

impl SumcheckComputationPacked<EF> for DotProductFootprint {
    fn degree(&self) -> usize {
        2
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        self.air_eval(point, |p, c| p * c)
    }
    fn eval_packed_base(&self, point: &[PFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        self.air_eval(point, |p, c| EFPacking::<EF>::from(p) * c)
    }
}

pub fn get_poseidon_lookup_statements(
    (p16_air_width, p24_air_width): (usize, usize),
    (log_n_p16, log_n_p24): (usize, usize),
    (p16_evals, p24_evals): (&[EF], &[EF]),
    (p16_air_point, p24_air_point): (&MultilinearPoint<EF>, &MultilinearPoint<EF>),
    memory_folding_challenges: &MultilinearPoint<EF>,
) -> Vec<Evaluation<EF>> {
    let p16_folded_eval_addr_a = (&p16_evals[..8]).evaluate(memory_folding_challenges);
    let p16_folded_eval_addr_b = (&p16_evals[8..16]).evaluate(memory_folding_challenges);
    let p16_folded_eval_addr_res_a =
        (&p16_evals[p16_air_width - 16..p16_air_width - 8]).evaluate(memory_folding_challenges);
    let p16_folded_eval_addr_res_b =
        (&p16_evals[p16_air_width - 8..]).evaluate(memory_folding_challenges);

    let p24_folded_eval_addr_a = (&p24_evals[..8]).evaluate(memory_folding_challenges);
    let p24_folded_eval_addr_b = (&p24_evals[8..16]).evaluate(memory_folding_challenges);
    let p24_folded_eval_addr_c = (&p24_evals[16..24]).evaluate(memory_folding_challenges);
    let p24_folded_eval_addr_res =
        (&p24_evals[p24_air_width - 8..]).evaluate(memory_folding_challenges);

    let padding_p16 = EF::zero_vec(log_n_p16.max(log_n_p24) - log_n_p16);
    let padding_p24 = EF::zero_vec(log_n_p16.max(log_n_p24) - log_n_p24);

    vec![
        Evaluation::new(
            [
                vec![EF::ZERO; 3],
                padding_p16.clone(),
                p16_air_point.0.clone(),
            ]
            .concat(),
            p16_folded_eval_addr_a,
        ),
        Evaluation::new(
            [
                vec![EF::ZERO, EF::ZERO, EF::ONE],
                padding_p16.clone(),
                p16_air_point.0.clone(),
            ]
            .concat(),
            p16_folded_eval_addr_b,
        ),
        Evaluation::new(
            [
                vec![EF::ZERO, EF::ONE, EF::ZERO],
                padding_p16.clone(),
                p16_air_point.0.clone(),
            ]
            .concat(),
            p16_folded_eval_addr_res_a,
        ),
        Evaluation::new(
            [
                vec![EF::ZERO, EF::ONE, EF::ONE],
                padding_p16.clone(),
                p16_air_point.0.clone(),
            ]
            .concat(),
            p16_folded_eval_addr_res_b,
        ),
        Evaluation::new(
            [
                vec![EF::ONE, EF::ZERO, EF::ZERO],
                padding_p24.clone(),
                p24_air_point.0.clone(),
            ]
            .concat(),
            p24_folded_eval_addr_a,
        ),
        Evaluation::new(
            [
                vec![EF::ONE, EF::ZERO, EF::ONE],
                padding_p24.clone(),
                p24_air_point.0.clone(),
            ]
            .concat(),
            p24_folded_eval_addr_b,
        ),
        Evaluation::new(
            [
                vec![EF::ONE, EF::ONE, EF::ZERO],
                padding_p24.clone(),
                p24_air_point.0.clone(),
            ]
            .concat(),
            p24_folded_eval_addr_c,
        ),
        Evaluation::new(
            [
                vec![EF::ONE, EF::ONE, EF::ONE],
                padding_p24.clone(),
                p24_air_point.0.clone(),
            ]
            .concat(),
            p24_folded_eval_addr_res,
        ),
    ]
}

pub fn poseidon_lookup_correcting_factors(
    log_n_p16: usize,
    log_n_p24: usize,
    index_lookup_point: &MultilinearPoint<EF>,
) -> (EF, EF) {
    let correcting_factor = index_lookup_point[3..3 + log_n_p16.abs_diff(log_n_p24)]
        .iter()
        .map(|&x| EF::ONE - x)
        .product::<EF>();
    if log_n_p16 > log_n_p24 {
        (EF::ONE, correcting_factor)
    } else {
        (correcting_factor, EF::ONE)
    }
}

pub fn add_poseidon_lookup_statements_on_indexes(
    log_n_p16: usize,
    log_n_p24: usize,
    index_lookup_point: &MultilinearPoint<EF>,
    inner_values: &[EF],
    p16_indexe_statements: [&mut Vec<Evaluation<EF>>; 4], // a, b, res_1, res_2
    p24_indexe_statements: [&mut Vec<Evaluation<EF>>; 3], // a, b, res
) {
    assert_eq!(inner_values.len(), 7);
    let mut idx_point_right_p16 = MultilinearPoint(index_lookup_point[3..].to_vec());
    let mut idx_point_right_p24 =
        MultilinearPoint(index_lookup_point[3 + log_n_p16.abs_diff(log_n_p24)..].to_vec());
    if log_n_p16 < log_n_p24 {
        std::mem::swap(&mut idx_point_right_p16, &mut idx_point_right_p24);
    }
    for (i, stmt) in p16_indexe_statements.into_iter().enumerate() {
        stmt.push(Evaluation::new(
            idx_point_right_p16.clone(),
            inner_values[i],
        ));
    }
    for (i, stmt) in p24_indexe_statements.into_iter().enumerate() {
        stmt.push(Evaluation::new(
            idx_point_right_p24.clone(),
            inner_values[i + 4],
        ));
    }
}
