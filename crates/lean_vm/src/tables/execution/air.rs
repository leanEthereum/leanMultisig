use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder};

use crate::{EF, ExecutionTable, ExtraDataForBuses, eval_virtual_bus_column};

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

// Temporary columns (stored to avoid duplicate computations)
pub const N_TEMPORARY_EXEC_COLUMNS: usize = 3;
pub const COL_INDEX_EXEC_NU_A: usize = 21;
pub const COL_INDEX_EXEC_NU_B: usize = 22;
pub const COL_INDEX_EXEC_NU_C: usize = 23;

impl Air for ExecutionTable {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns_f_air(&self) -> usize {
        N_EXEC_AIR_COLUMNS
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        5
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![COL_INDEX_PC, COL_INDEX_FP]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        16
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up_f();
        let down = builder.down_f();

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

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            precompile_index.clone(),
            is_precompile.clone(),
            nu_a.clone(),
            nu_b.clone(),
            nu_c.clone(),
            aux.clone(),
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
}
