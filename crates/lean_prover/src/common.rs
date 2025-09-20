use p3_air::BaseAir;
use p3_field::{ExtensionField, PrimeCharacteristicRing};
use packed_pcs::ColDims;
use rayon::prelude::*;
use std::ops::Range;
use sumcheck::{SumcheckComputation, SumcheckComputationPacked};
use utils::{EFPacking, PF, Poseidon16Air, Poseidon24Air, padd_with_zero_to_next_power_of_two};
use whir_p3::poly::{
    evals::fold_multilinear,
    multilinear::{Evaluation, MultilinearPoint},
};

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
            ColDims::sparse_with_public_data(Some(log_public_memory), private_memory_len, F::ZERO), //  memory
            ColDims::sparse(n_cycles, F::from_usize(bytecode_ending_pc)), // pc
            ColDims::sparse(n_cycles, F::ZERO),                           // fp
            ColDims::sparse(n_cycles, F::ZERO),                           // mem_addr_a
            ColDims::sparse(n_cycles, F::ZERO),                           // mem_addr_b
            ColDims::sparse(n_cycles, F::ZERO),                           // mem_addr_c
            ColDims::sparse(n_poseidons_16, F::from_usize(ZERO_VEC_PTR)), // poseidon16 index a
            ColDims::sparse(n_poseidons_16, F::from_usize(ZERO_VEC_PTR)), // poseidon16 index b
            ColDims::sparse(n_poseidons_16, F::from_usize(POSEIDON_16_NULL_HASH_PTR)), // poseidon16 index res
            ColDims::sparse(n_poseidons_24, F::from_usize(ZERO_VEC_PTR)), // poseidon24 index a
            ColDims::sparse(n_poseidons_24, F::from_usize(ZERO_VEC_PTR)), // poseidon24 index b
            ColDims::sparse(n_poseidons_24, F::from_usize(POSEIDON_24_NULL_HASH_PTR)), // poseidon24 index res
        ],
        (0..p16_air_width - 16 * 2)
            .map(|i| ColDims::sparse(n_poseidons_16, default_p16_row[16 + i][0]))
            .collect::<Vec<_>>(), // rest of poseidon16 table
        (0..p24_air_width - 24 * 2)
            .map(|i| ColDims::sparse(n_poseidons_24, default_p24_row[24 + i][0]))
            .collect::<Vec<_>>(), // rest of poseidon24 table
        vec![
            ColDims::sparse(n_rows_table_dot_products, F::ONE), // dot product: (start) flag
            ColDims::sparse(n_rows_table_dot_products, F::ONE), // dot product: length
            ColDims::sparse(n_rows_table_dot_products, F::ZERO), // dot product: index a
            ColDims::sparse(n_rows_table_dot_products, F::ZERO), // dot product: index b
            ColDims::sparse(n_rows_table_dot_products, F::ZERO), // dot product: index res
        ],
        vec![ColDims::sparse(n_rows_table_dot_products, F::ZERO); DIMENSION], // dot product: computation
    ]
    .concat()
}

pub fn poseidon_16_column_groups(poseidon_16_air: &Poseidon16Air<F>) -> Vec<Range<usize>> {
    (0..poseidon_16_air.width()).map(|i| i..i + 1).collect()
}

pub fn poseidon_24_column_groups(poseidon_24_air: &Poseidon24Air<F>) -> Vec<Range<usize>> {
    (0..poseidon_24_air.width()).map(|i| i..i + 1).collect()
}

pub fn fold_bytecode(bytecode: &Bytecode, folding_challenges: &MultilinearPoint<EF>) -> Vec<EF> {
    let encoded_bytecode = padd_with_zero_to_next_power_of_two(
        &bytecode
            .instructions
            .par_iter()
            .flat_map(|i| padd_with_zero_to_next_power_of_two(&field_representation(i)))
            .collect::<Vec<_>>(),
    );
    fold_multilinear(&encoded_bytecode, folding_challenges)
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

pub struct PrecompileFootprint {
    pub grand_product_challenge_global: EF,
    pub grand_product_challenge_p16: [EF; 5],
    pub grand_product_challenge_p24: [EF; 5],
    pub grand_product_challenge_dot_product: [EF; 6],
    pub grand_product_challenge_vm_multilinear_eval: [EF; 6],
}

impl<N: ExtensionField<PF<EF>>> SumcheckComputation<N, EF> for PrecompileFootprint
where
    EF: ExtensionField<N>,
{
    fn degree(&self) -> usize {
        3
    }
    fn eval(&self, point: &[N], _: &[EF]) -> EF {
        // TODO not all columns are used

        let nu_a = (EF::ONE - point[COL_INDEX_FLAG_A]) * point[COL_INDEX_MEM_VALUE_A]
            + point[COL_INDEX_FLAG_A] * point[COL_INDEX_OPERAND_A];
        let nu_b = (EF::ONE - point[COL_INDEX_FLAG_B]) * point[COL_INDEX_MEM_VALUE_B]
            + point[COL_INDEX_FLAG_B] * point[COL_INDEX_OPERAND_B];
        let nu_c = (EF::ONE - point[COL_INDEX_FLAG_C]) * point[COL_INDEX_MEM_VALUE_C]
            + point[COL_INDEX_FLAG_C] * point[COL_INDEX_FP];

        self.grand_product_challenge_global
            + (self.grand_product_challenge_p16[1]
                + self.grand_product_challenge_p16[2] * nu_a
                + self.grand_product_challenge_p16[3] * nu_b
                + self.grand_product_challenge_p16[4] * nu_c)
                * point[COL_INDEX_POSEIDON_16]
            + (self.grand_product_challenge_p24[1]
                + self.grand_product_challenge_p24[2] * nu_a
                + self.grand_product_challenge_p24[3] * nu_b
                + self.grand_product_challenge_p24[4] * nu_c)
                * point[COL_INDEX_POSEIDON_24]
            + (self.grand_product_challenge_dot_product[1]
                + self.grand_product_challenge_dot_product[2] * nu_a
                + self.grand_product_challenge_dot_product[3] * nu_b
                + self.grand_product_challenge_dot_product[4] * nu_c
                + self.grand_product_challenge_dot_product[5] * point[COL_INDEX_AUX])
                * point[COL_INDEX_DOT_PRODUCT]
            + (self.grand_product_challenge_vm_multilinear_eval[1]
                + self.grand_product_challenge_vm_multilinear_eval[2] * nu_a
                + self.grand_product_challenge_vm_multilinear_eval[3] * nu_b
                + self.grand_product_challenge_vm_multilinear_eval[4] * nu_c
                + self.grand_product_challenge_vm_multilinear_eval[5] * point[COL_INDEX_AUX])
                * point[COL_INDEX_MULTILINEAR_EVAL]
    }
}

impl SumcheckComputationPacked<EF> for PrecompileFootprint {
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_extension(&self, _point: &[EFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        todo!()
    }

    fn eval_packed_base(&self, _point: &[utils::PFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        todo!()
    }
}

pub struct DotProductFootprint {
    pub grand_product_challenge_global: EF,
    pub grand_product_challenge_dot_product: [EF; 6],
}

impl<N: ExtensionField<PF<EF>>> SumcheckComputation<N, EF> for DotProductFootprint
where
    EF: ExtensionField<N>,
{
    fn degree(&self) -> usize {
        2
    }

    fn eval(&self, point: &[N], _: &[EF]) -> EF {
        self.grand_product_challenge_global
            + self.grand_product_challenge_dot_product[1]
            + (self.grand_product_challenge_dot_product[2] * point[2]
                + self.grand_product_challenge_dot_product[3] * point[3]
                + self.grand_product_challenge_dot_product[4] * point[4]
                + self.grand_product_challenge_dot_product[5] * point[1])
                * point[0]
    }
}

impl SumcheckComputationPacked<EF> for DotProductFootprint {
    fn degree(&self) -> usize {
        2
    }

    fn eval_packed_extension(&self, _point: &[EFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        todo!()
    }
    fn eval_packed_base(&self, _point: &[utils::PFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        todo!()
    }
}
