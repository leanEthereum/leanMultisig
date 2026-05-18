use crate::{EF, ExecutionTable, ExtraDataForBuses, eval_virtual_bus_column};
use backend::*;

pub const N_RUNTIME_COLUMNS: usize = 8;
pub const N_INSTRUCTION_COLUMNS: usize = 12;
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
pub const COL_FLAG_C_FP: usize = 14;
pub const COL_FLAG_AB_FP: usize = 15;
pub const COL_MUL: usize = 16;
pub const COL_JUMP: usize = 17;
pub const COL_AUX: usize = 18;
pub const COL_PRECOMPILE_DATA: usize = 19;

// Temporary columns (stored to avoid duplicate computations)
pub const N_TEMPORARY_EXEC_COLUMNS: usize = 4;
pub const COL_IS_PRECOMPILE: usize = 20;
pub const COL_EXEC_NU_A: usize = 21;
pub const COL_EXEC_NU_B: usize = 22;
pub const COL_EXEC_NU_C: usize = 23;

impl<const BUS: bool> Air for ExecutionTable<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        N_TOTAL_EXECUTION_COLUMNS
    }
    fn degree_air(&self) -> usize {
        5
    }
    fn n_shift_columns(&self) -> usize {
        2
    }
    fn n_constraints(&self) -> usize {
        13
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let flat = builder.flat();
        let shift = builder.shift();

        let pc_shift = shift[COL_PC];
        let fp_shift = shift[COL_FP];

        let (operand_a, operand_b, operand_c) = (flat[COL_OPERAND_A], flat[COL_OPERAND_B], flat[COL_OPERAND_C]);
        let (flag_a, flag_b, flag_c) = (flat[COL_FLAG_A], flat[COL_FLAG_B], flat[COL_FLAG_C]);
        let flag_c_fp = flat[COL_FLAG_C_FP];
        let flag_ab_fp = flat[COL_FLAG_AB_FP];
        let mul = flat[COL_MUL];
        let jump = flat[COL_JUMP];
        let aux = flat[COL_AUX];
        let precompile_data = flat[COL_PRECOMPILE_DATA];

        let (value_a, value_b, value_c) = (flat[COL_MEM_VALUE_A], flat[COL_MEM_VALUE_B], flat[COL_MEM_VALUE_C]);
        let pc = flat[COL_PC];
        let fp = flat[COL_FP];
        let (addr_a, addr_b, addr_c) = (
            flat[COL_MEM_ADDRESS_A],
            flat[COL_MEM_ADDRESS_B],
            flat[COL_MEM_ADDRESS_C],
        );

        let one_minus_flag_a_and_flag_ab_fp = -(flag_a + flag_ab_fp - AB::F::ONE);
        let one_minus_flag_b_and_flag_ab_fp = -(flag_b + flag_ab_fp - AB::F::ONE);
        let one_minus_flag_c_and_flag_c_fp = -(flag_c + flag_c_fp - AB::F::ONE);

        let nu_a = flag_a * operand_a + one_minus_flag_a_and_flag_ab_fp * value_a + flag_ab_fp * (fp + operand_a);
        let nu_b = flag_b * operand_b + one_minus_flag_b_and_flag_ab_fp * value_b + flag_ab_fp * (fp + operand_b);
        let nu_c = flag_c * operand_c + one_minus_flag_c_and_flag_c_fp * value_c + flag_c_fp * (fp + operand_c);

        let fp_plus_operand_a = fp + operand_a;
        let fp_plus_operand_b = fp + operand_b;
        let fp_plus_operand_c = fp + operand_c;
        let pc_plus_one = pc + AB::F::ONE;
        let nu_a_minus_one = nu_a - AB::F::ONE;

        let add = aux * AB::F::TWO - aux * aux;
        let deref = (aux * (aux - AB::F::ONE)).halve();
        let is_precompile = -(add + mul + deref + jump - AB::F::ONE);

        if BUS {
            builder.assert_zero_ef(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                is_precompile,
                &[precompile_data, nu_a, nu_b, nu_c],
            ));
        } else {
            builder.declare_values(&[is_precompile]);
            builder.declare_values(&[precompile_data, nu_a, nu_b, nu_c]);
        }

        builder.assert_zero(one_minus_flag_a_and_flag_ab_fp * (addr_a - fp_plus_operand_a));
        builder.assert_zero(one_minus_flag_b_and_flag_ab_fp * (addr_b - fp_plus_operand_b));
        builder.assert_zero(one_minus_flag_c_and_flag_c_fp * (addr_c - fp_plus_operand_c));

        builder.assert_zero(add * (nu_b - (nu_a + nu_c)));
        builder.assert_zero(mul * (nu_b - nu_a * nu_c));

        // DEREF: addr_B = value_A + operand_B, result in value_B, compared to nu_C
        builder.assert_zero(deref * (addr_b - (value_a + operand_b)));
        builder.assert_zero(deref * (value_b - nu_c));

        let jump_and_condition = jump * nu_a;

        builder.assert_zero(jump_and_condition * nu_a_minus_one);
        builder.assert_zero(jump_and_condition * (pc_shift - nu_b));
        builder.assert_zero(jump_and_condition * (fp_shift - nu_c));
        let not_jump_and_condition = -(jump_and_condition - AB::F::ONE);
        builder.assert_zero(not_jump_and_condition * (pc_shift - pc_plus_one));
        builder.assert_zero(not_jump_and_condition * (fp_shift - fp));
    }
}

pub const fn instr_idx(col_index_in_air: usize) -> usize {
    col_index_in_air - N_RUNTIME_COLUMNS
}
