use p3_air::BaseAir;
use p3_field::{ExtensionField, Field, PrimeCharacteristicRing};
use p3_util::log2_ceil_usize;
use rayon::prelude::*;
use std::ops::Range;
use sumcheck::{SumcheckComputation, SumcheckComputationPacked};
use utils::{
    EFPacking, Evaluation, PF, Poseidon16Air, Poseidon24Air, from_end,
    padd_with_zero_to_next_power_of_two, remove_end,
};
use whir_p3::{
    fiat_shamir::errors::ProofError,
    poly::{
        evals::{EvaluationsList, fold_multilinear},
        multilinear::MultilinearPoint,
    },
};

use crate::*;
use vm::*;

pub fn poseidon_16_column_groups(poseidon_16_air: &Poseidon16Air<F>) -> Vec<Range<usize>> {
    vec![
        0..8,
        8..16,
        16..poseidon_16_air.width() - 16,
        poseidon_16_air.width() - 16..poseidon_16_air.width() - 8,
        poseidon_16_air.width() - 8..poseidon_16_air.width(),
    ]
}

pub fn poseidon_24_column_groups(poseidon_24_air: &Poseidon24Air<F>) -> Vec<Range<usize>> {
    vec![
        0..8,
        8..16,
        16..24,
        24..poseidon_24_air.width() - 24,
        poseidon_24_air.width() - 24..poseidon_24_air.width() - 8, // TODO should we commit to this part ? Probably not, but careful here, we will not check evaluations for this part
        poseidon_24_air.width() - 8..poseidon_24_air.width(),
    ]
}

pub fn poseidon_lookup_value<EF: Field>(
    n_poseidons_16: usize,
    n_poseidons_24: usize,
    poseidon16_evals: &[Evaluation<EF>],
    poseidon24_evals: &[Evaluation<EF>],
    poseidon_lookup_batching_chalenges: &MultilinearPoint<EF>,
) -> EF {
    let (point, diff) = if n_poseidons_16 > n_poseidons_24 {
        (
            &poseidon16_evals[0].point,
            log2_ceil_usize(n_poseidons_16) - log2_ceil_usize(n_poseidons_24),
        )
    } else {
        (
            &poseidon24_evals[0].point,
            log2_ceil_usize(n_poseidons_24) - log2_ceil_usize(n_poseidons_16),
        )
    };
    let factor: EF = from_end(point, diff).iter().map(|&f| EF::ONE - f).product();
    let (s16, s24) = if n_poseidons_16 > n_poseidons_24 {
        (EF::ONE, factor)
    } else {
        (factor, EF::ONE)
    };
    [
        poseidon16_evals[0].value * s16,
        poseidon16_evals[1].value * s16,
        poseidon16_evals[3].value * s16,
        poseidon16_evals[4].value * s16,
        poseidon24_evals[0].value * s24,
        poseidon24_evals[1].value * s24,
        poseidon24_evals[2].value * s24,
        poseidon24_evals[5].value * s24,
    ]
    .evaluate(poseidon_lookup_batching_chalenges)
}

pub fn poseidon_lookup_index_statements(
    poseidon_index_evals: &[EF],
    n_poseidons_16: usize,
    n_poseidons_24: usize,
    poseidon_logup_star_statements_indexes_point: &MultilinearPoint<EF>,
) -> Result<(Vec<Evaluation<EF>>, Vec<Evaluation<EF>>), ProofError> {
    let log_n_p16 = log2_ceil_usize(n_poseidons_16);
    let log_n_p24 = log2_ceil_usize(n_poseidons_24);
    let correcting_factor = from_end(
        poseidon_logup_star_statements_indexes_point,
        log_n_p16.abs_diff(log_n_p24),
    )
    .iter()
    .map(|&x| EF::ONE - x)
    .product::<EF>();
    let (correcting_factor_p16, correcting_factor_p24) = if n_poseidons_16 > n_poseidons_24 {
        (EF::ONE, correcting_factor)
    } else {
        (correcting_factor, EF::ONE)
    };
    let mut idx_point_right_p16 = poseidon_logup_star_statements_indexes_point[3..].to_vec();
    let mut idx_point_right_p24 = remove_end(
        &poseidon_logup_star_statements_indexes_point[3..],
        log_n_p16.abs_diff(log_n_p24),
    )
    .to_vec();
    if n_poseidons_16 < n_poseidons_24 {
        std::mem::swap(&mut idx_point_right_p16, &mut idx_point_right_p24);
    }
    let p16_indexes_statements = vec![
        Evaluation {
            point: MultilinearPoint(
                [vec![EF::ZERO, EF::ZERO], idx_point_right_p16.clone()].concat(),
            ),
            value: poseidon_index_evals[0] / correcting_factor_p16,
        },
        Evaluation {
            point: MultilinearPoint(
                [vec![EF::ZERO, EF::ONE], idx_point_right_p16.clone()].concat(),
            ),
            value: poseidon_index_evals[1] / correcting_factor_p16,
        },
        Evaluation {
            point: MultilinearPoint(
                [vec![EF::ONE, EF::ZERO], idx_point_right_p16.clone()].concat(),
            ),
            value: poseidon_index_evals[2] / correcting_factor_p16,
        },
    ];

    let p24_indexes_statements = vec![
        Evaluation {
            point: MultilinearPoint(
                [vec![EF::ZERO, EF::ZERO], idx_point_right_p24.clone()].concat(),
            ),
            value: poseidon_index_evals[4] / correcting_factor_p24,
        },
        Evaluation {
            point: MultilinearPoint(
                [vec![EF::ZERO, EF::ONE], idx_point_right_p24.clone()].concat(),
            ),
            value: poseidon_index_evals[6] / correcting_factor_p24,
        },
        Evaluation {
            point: MultilinearPoint(
                [vec![EF::ONE, EF::ZERO], idx_point_right_p24.clone()].concat(),
            ),
            value: poseidon_index_evals[7] / correcting_factor_p24,
        },
    ];

    if poseidon_index_evals[3] != poseidon_index_evals[2] + correcting_factor_p16 {
        return Err(ProofError::InvalidProof);
    }
    if poseidon_index_evals[5] != poseidon_index_evals[4] + correcting_factor_p24 {
        return Err(ProofError::InvalidProof);
    }
    Ok((p16_indexes_statements, p24_indexes_statements))
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
    let initial_pc_statement = Evaluation {
        point: MultilinearPoint(EF::zero_vec(log_n_cycles)),
        value: EF::ZERO,
    };
    let final_pc_statement = Evaluation {
        point: MultilinearPoint(vec![EF::ONE; log_n_cycles]),
        value: EF::from_usize(bytecode.ending_pc),
    };
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
