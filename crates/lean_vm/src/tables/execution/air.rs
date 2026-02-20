use crate::{EF, ExecutionTable, ExtraDataForBuses, eval_virtual_bus_column};
use backend::*;

pub const N_RUNTIME_COLUMNS: usize = 8;
pub const N_INSTRUCTION_COLUMNS: usize = 11;
pub const N_TOTAL_EXECUTION_COLUMNS: usize = N_INSTRUCTION_COLUMNS + N_RUNTIME_COLUMNS;

// Committed columns (IMPORTANT: they must be the first columns)
pub const COL_PC: usize = 0;
pub const COL_FP: usize = 1;
pub const COL_MEM_ADDRESS_A: usize = 2;
pub const COL_MEM_ADDRESS_B: usize = 3;
pub const COL_MEM_ADDRESS_C: usize = 4;
pub const COL_MEM_VALUE_A: usize = 5;
pub const COL_MEM_VALUE_B: usize = 6;
pub const COL_MEM_VALUE_C: usize = 7;

// Decoded instruction columns
pub const COL_OPERAND_A: usize = 8;
pub const COL_OPERAND_B: usize = 9;
pub const COL_OPERAND_C: usize = 10;
pub const COL_FLAG_A: usize = 11;
pub const COL_FLAG_B: usize = 12;
pub const COL_FLAG_C: usize = 13;
pub const COL_FLAG_FP: usize = 14;
pub const COL_MUL: usize = 15;
pub const COL_JUMP: usize = 16;
pub const COL_AUX: usize = 17;
pub const COL_PRECOMPILE_DATA: usize = 18;

// Temporary columns (stored to avoid duplicate computations)
pub const N_TEMPORARY_EXEC_COLUMNS: usize = 4;
pub const COL_IS_PRECOMPILE: usize = 19;
pub const COL_EXEC_NU_A: usize = 20;
pub const COL_EXEC_NU_B: usize = 21;
pub const COL_EXEC_NU_C: usize = 22;

impl<const BUS: bool> Air for ExecutionTable<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns_f_air(&self) -> usize {
        N_TOTAL_EXECUTION_COLUMNS
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree_air(&self) -> usize {
        5
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![COL_PC, COL_FP]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        13
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up_f();
        let down = builder.down_f();

        let next_pc = down[0].clone();
        let next_fp = down[1].clone();

        let (operand_a, operand_b, operand_c) = (
            up[COL_OPERAND_A].clone(),
            up[COL_OPERAND_B].clone(),
            up[COL_OPERAND_C].clone(),
        );
        let (flag_a, flag_b, flag_c) = (up[COL_FLAG_A].clone(), up[COL_FLAG_B].clone(), up[COL_FLAG_C].clone());
        let flag_fp = up[COL_FLAG_FP].clone();
        let mul = up[COL_MUL].clone();
        let jump = up[COL_JUMP].clone();
        let aux = up[COL_AUX].clone();
        let precompile_data = up[COL_PRECOMPILE_DATA].clone();

        let (value_a, value_b, value_c) = (
            up[COL_MEM_VALUE_A].clone(),
            up[COL_MEM_VALUE_B].clone(),
            up[COL_MEM_VALUE_C].clone(),
        );
        let pc = up[COL_PC].clone();
        let fp = up[COL_FP].clone();
        let (addr_a, addr_b, addr_c) = (
            up[COL_MEM_ADDRESS_A].clone(),
            up[COL_MEM_ADDRESS_B].clone(),
            up[COL_MEM_ADDRESS_C].clone(),
        );

        let flag_a_minus_one = flag_a.clone() - AB::F::ONE;
        let flag_b_minus_one = flag_b.clone() - AB::F::ONE;
        let one_minus_flag_c_and_flag_fp = AB::F::ONE - (flag_c.clone() + flag_fp.clone());

        let nu_a = flag_a * operand_a.clone() + value_a.clone() * -flag_a_minus_one.clone();
        let nu_b = flag_b * operand_b.clone() + value_b.clone() * -flag_b_minus_one.clone();
        // nu_C = flag_C * operand_C + (1 - flag_C - flag_fp) * value_C + flag_fp * fp
        let nu_c = flag_c.clone() * operand_c.clone()
            + one_minus_flag_c_and_flag_fp.clone() * value_c.clone()
            + flag_fp.clone() * fp.clone();

        let fp_plus_operand_a = fp.clone() + operand_a.clone();
        let fp_plus_operand_b = fp.clone() + operand_b.clone();
        let fp_plus_operand_c = fp.clone() + operand_c.clone();
        let pc_plus_one = pc + AB::F::ONE;
        let nu_a_minus_one = nu_a.clone() - AB::F::ONE;

        let add = aux.clone() * (AB::F::TWO - aux.clone()); // equals 1 when aux = 1, else equals 0 (when aux = 0 or aux = 2)
        let deref = aux.clone() * (aux.clone() - AB::F::ONE) * AB::F::INVERSE_OF_TWO; // equals 1 when aux = 2, else equals 0 (when aux = 0 or aux = 1)
        let is_precompile = AB::F::ONE - (add.clone() + mul.clone() + deref.clone() + jump.clone());

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                is_precompile.clone(),
                &[precompile_data.clone(), nu_a.clone(), nu_b.clone(), nu_c.clone()],
            ));
        } else {
            builder.declare_values(&[is_precompile]);
            builder.declare_values(&[precompile_data.clone(), nu_a.clone(), nu_b.clone(), nu_c.clone()]);
        }

        builder.assert_zero(flag_a_minus_one * (addr_a.clone() - fp_plus_operand_a));
        builder.assert_zero(flag_b_minus_one * (addr_b.clone() - fp_plus_operand_b));
        builder.assert_zero(one_minus_flag_c_and_flag_fp.clone() * (addr_c.clone() - fp_plus_operand_c));

        builder.assert_zero(add * (nu_b.clone() - (nu_a.clone() + nu_c.clone())));
        builder.assert_zero(mul * (nu_b.clone() - nu_a.clone() * nu_c.clone()));

        // DEREF: addr_B = value_A + operand_B, result in value_B, compared to nu_C
        builder.assert_zero(deref.clone() * (addr_b.clone() - (value_a.clone() + operand_b.clone())));
        builder.assert_zero(deref * (value_b.clone() - nu_c.clone()));

        let jump_and_condition = jump.clone() * nu_a.clone();

        builder.assert_zero(jump_and_condition.clone() * nu_a_minus_one.clone());
        builder.assert_zero(jump_and_condition.clone() * (next_pc.clone() - nu_b.clone()));
        builder.assert_zero(jump_and_condition.clone() * (next_fp.clone() - nu_c.clone()));
        let not_jump_and_condition = AB::F::ONE - jump_and_condition;
        builder.assert_zero(not_jump_and_condition.clone() * (next_pc.clone() - pc_plus_one.clone()));
        builder.assert_zero(not_jump_and_condition * (next_fp.clone() - fp.clone()));
    }
}

pub const fn instr_idx(col_index_in_air: usize) -> usize {
    col_index_in_air - N_RUNTIME_COLUMNS
}
