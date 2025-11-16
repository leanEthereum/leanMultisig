use std::{
    any::TypeId,
    mem::{transmute, transmute_copy},
};

use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_uni_stark::SymbolicExpression;

pub const N_INSTRUCTION_COLUMNS: usize = 13;
pub const N_COMMITTED_EXEC_COLUMNS: usize = 5;
pub const N_MEMORY_VALUE_COLUMNS: usize = 3; // virtual (lookup into memory, with logup*)
pub const N_EXEC_AIR_COLUMNS: usize =
    N_INSTRUCTION_COLUMNS + N_COMMITTED_EXEC_COLUMNS + N_MEMORY_VALUE_COLUMNS;

// Instruction columns
pub const COL_INDEX_OPERAND_A: usize = 0;
pub const COL_INDEX_OPERAND_B: usize = 1;
pub const COL_INDEX_OPERAND_C: usize = 2;
pub const COL_INDEX_FLAG_A: usize = 3;
pub const COL_INDEX_FLAG_B: usize = 4;
pub const COL_INDEX_FLAG_C: usize = 5;
pub const COL_INDEX_ADD: usize = 6;
pub const COL_INDEX_MUL: usize = 7;
pub const COL_INDEX_DEREF: usize = 8;
pub const COL_INDEX_JUMP: usize = 9;
pub const COL_INDEX_AUX: usize = 10;
pub const COL_INDEX_IS_PRECOMPILE: usize = 11;
pub const COL_INDEX_PRECOMPILE_INDEX: usize = 12;

// Execution columns
pub const COL_INDEX_MEM_VALUE_A: usize = 13; // virtual with logup*
pub const COL_INDEX_MEM_VALUE_B: usize = 14; // virtual with logup*
pub const COL_INDEX_MEM_VALUE_C: usize = 15; // virtual with logup*
pub const COL_INDEX_PC: usize = 16;
pub const COL_INDEX_FP: usize = 17;
pub const COL_INDEX_MEM_ADDRESS_A: usize = 18;
pub const COL_INDEX_MEM_ADDRESS_B: usize = 19;
pub const COL_INDEX_MEM_ADDRESS_C: usize = 20;

#[derive(Debug)]
pub struct VMAir<EF> {
    // GKR grand product challenges
    pub global_challenge: EF,
    pub fingerprint_challenge_powers: [EF; 5],
}

impl <EF>SumcheckComputationForAir for VMAir<EF> {}

impl<F, EF: Send + Sync> BaseAir<F> for VMAir<EF> {
    fn width(&self) -> usize {
        N_EXEC_AIR_COLUMNS
    }
    fn degree(&self) -> usize {
        5
    }
    fn columns_with_shift(&self) -> Vec<usize> {
        vec![COL_INDEX_PC, COL_INDEX_FP]
    }
}

impl<AB: AirBuilder, EF: ExtensionField<PF<EF>>> Air<AB> for VMAir<EF>
where
    AB::Var: 'static,
    AB::Expr: 'static,
    AB::FinalOutput: 'static,
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = &main[..N_EXEC_AIR_COLUMNS];
        let down = &main[N_EXEC_AIR_COLUMNS..];

        let next_pc = down[0].clone();
        let next_fp = down[1].clone();

        let (operand_a, operand_b, operand_c) = (
            up[COL_INDEX_OPERAND_A].clone(),
            up[COL_INDEX_OPERAND_B].clone(),
            up[COL_INDEX_OPERAND_C].clone(),
        );
        let (flag_a, flag_b, flag_c) = (
            up[COL_INDEX_FLAG_A].clone(),
            up[COL_INDEX_FLAG_B].clone(),
            up[COL_INDEX_FLAG_C].clone(),
        );
        let add = up[COL_INDEX_ADD].clone();
        let mul = up[COL_INDEX_MUL].clone();
        let deref = up[COL_INDEX_DEREF].clone();
        let jump = up[COL_INDEX_JUMP].clone();
        let aux = up[COL_INDEX_AUX].clone();
        let is_precompile = up[COL_INDEX_IS_PRECOMPILE].clone();
        let precompile_index = up[COL_INDEX_PRECOMPILE_INDEX].clone();

        let (value_a, value_b, value_c) = (
            up[COL_INDEX_MEM_VALUE_A].clone(),
            up[COL_INDEX_MEM_VALUE_B].clone(),
            up[COL_INDEX_MEM_VALUE_C].clone(),
        );
        let pc = up[COL_INDEX_PC].clone();
        let fp = up[COL_INDEX_FP].clone();
        let (addr_a, addr_b, addr_c) = (
            up[COL_INDEX_MEM_ADDRESS_A].clone(),
            up[COL_INDEX_MEM_ADDRESS_B].clone(),
            up[COL_INDEX_MEM_ADDRESS_C].clone(),
        );

        let flag_a_minus_one = flag_a.clone() - AB::F::ONE;
        let flag_b_minus_one = flag_b.clone() - AB::F::ONE;
        let flag_c_minus_one = flag_c.clone() - AB::F::ONE;

        let nu_a = flag_a * operand_a.clone() + value_a.clone() * -flag_a_minus_one.clone();
        let nu_b = flag_b * operand_b.clone() + value_b.clone() * -flag_b_minus_one.clone();
        let nu_c = flag_c * fp.clone() + value_c.clone() * -flag_c_minus_one.clone();

        let fp_plus_operand_a = fp.clone() + operand_a.clone();
        let fp_plus_operand_b = fp.clone() + operand_b.clone();
        let fp_plus_operand_c = fp.clone() + operand_c.clone();
        let pc_plus_one = pc + AB::F::ONE;
        let nu_a_minus_one = nu_a.clone() - AB::F::ONE;

        builder.add_custom(<VMAir<EF> as Air<AB>>::eval_custom(
            self,
            &[
                nu_a.clone(),
                nu_b.clone(),
                nu_c.clone(),
                aux.clone().into(),
                is_precompile.into(),
                precompile_index.into(),
            ],
        ));

        builder.assert_zero(flag_a_minus_one * (addr_a.clone() - fp_plus_operand_a));
        builder.assert_zero(flag_b_minus_one * (addr_b.clone() - fp_plus_operand_b));
        builder.assert_zero(flag_c_minus_one * (addr_c.clone() - fp_plus_operand_c));

        builder.assert_zero(add * (nu_b.clone() - (nu_a.clone() + nu_c.clone())));
        builder.assert_zero(mul * (nu_b.clone() - nu_a.clone() * nu_c.clone()));

        builder
            .assert_zero(deref.clone() * (addr_c.clone() - (value_a.clone() + operand_c.clone())));
        builder.assert_zero(deref.clone() * aux.clone() * (value_c.clone() - nu_b.clone()));
        builder.assert_zero(
            deref.clone() * (aux.clone() - AB::F::ONE) * (value_c.clone() - fp.clone()),
        );

        builder.assert_zero((jump.clone() - AB::F::ONE) * (next_pc.clone() - pc_plus_one.clone()));
        builder.assert_zero((jump.clone() - AB::F::ONE) * (next_fp.clone() - fp.clone()));

        builder.assert_zero(jump.clone() * nu_a.clone() * nu_a_minus_one.clone());
        builder.assert_zero(jump.clone() * nu_a.clone() * (next_pc.clone() - nu_b.clone()));
        builder.assert_zero(jump.clone() * nu_a.clone() * (next_fp.clone() - nu_c.clone()));
        builder.assert_zero(
            jump.clone() * nu_a_minus_one.clone() * (next_pc.clone() - pc_plus_one.clone()),
        );
        builder.assert_zero(jump.clone() * nu_a_minus_one.clone() * (next_fp.clone() - fp.clone()));
    }

    fn eval_custom(&self, inputs: &[<AB as AirBuilder>::Expr]) -> <AB as AirBuilder>::FinalOutput {
        let type_id_final_output = TypeId::of::<<AB as AirBuilder>::FinalOutput>();
        let type_id_expr = TypeId::of::<<AB as AirBuilder>::Expr>();
        // let type_id_f = TypeId::of::<PF<EF>>();
        let type_id_ef = TypeId::of::<EF>();
        let type_id_f_packing = TypeId::of::<PFPacking<EF>>();
        let type_id_ef_packing = TypeId::of::<EFPacking<EF>>();

        if type_id_expr == type_id_ef {
            assert_eq!(type_id_final_output, type_id_ef);
            let inputs = unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[EF]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| c * p);
            unsafe { transmute_copy::<EF, <AB as AirBuilder>::FinalOutput>(&res) }
        } else if type_id_expr == type_id_ef_packing {
            assert_eq!(type_id_final_output, type_id_ef_packing);
            let inputs =
                unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[EFPacking<EF>]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| p * c);
            unsafe { transmute_copy::<EFPacking<EF>, <AB as AirBuilder>::FinalOutput>(&res) }
        } else if type_id_expr == type_id_f_packing {
            assert_eq!(type_id_final_output, type_id_ef_packing);
            let inputs =
                unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[PFPacking<EF>]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| EFPacking::<EF>::from(p) * c);
            unsafe { transmute_copy::<EFPacking<EF>, <AB as AirBuilder>::FinalOutput>(&res) }
        } else {
            assert_eq!(type_id_expr, TypeId::of::<SymbolicExpression<PF<EF>>>());
            unsafe { transmute_copy(&SymbolicExpression::<PF<EF>>::default()) }
        }
    }
}

impl<EF: Copy> VMAir<EF> {
    fn gkr_virtual_column_eval<
        PointF: PrimeCharacteristicRing + Copy,
        ResultF: Algebra<EF> + Algebra<PointF> + Copy,
    >(
        &self,
        point: &[PointF],
        mul_point_f_and_ef: impl Fn(PointF, EF) -> ResultF,
    ) -> ResultF {
        let nu_a = point[0];
        let nu_b = point[1];
        let nu_c = point[2];
        let aux = point[3];
        let is_precompile = point[4];
        let precompile_index = point[5];

        let nu_a_mul_challenge_1 = mul_point_f_and_ef(nu_a, self.fingerprint_challenge_powers[1]);
        let nu_b_mul_challenge_2 = mul_point_f_and_ef(nu_b, self.fingerprint_challenge_powers[2]);
        let nu_c_mul_challenge_3 = mul_point_f_and_ef(nu_c, self.fingerprint_challenge_powers[3]);

        let nu_sums = nu_a_mul_challenge_1 + nu_b_mul_challenge_2 + nu_c_mul_challenge_3;
        let aux_mul_challenge_4 = mul_point_f_and_ef(aux, self.fingerprint_challenge_powers[4]);
        (nu_sums + aux_mul_challenge_4 + precompile_index) * is_precompile + self.global_challenge
    }
}

pub fn execution_air_padding_row<F: Field>(ending_pc: usize) -> Vec<F> {
    // only the shifted columns
    vec![
        F::from_usize(ending_pc), // PC
        F::ZERO,                  // FP
    ]
}
