use crate::{ALL_TABLES, EF, ExecutionTable, ExtraDataForBuses, F, eval_virtual_bus_column};
use multilinear_toolkit::prelude::*;

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
pub const COL_ADD: usize = 14;
pub const COL_MUL: usize = 15;
pub const COL_DEREF: usize = 16;
pub const COL_JUMP: usize = 17;
pub const COL_AUX: usize = 18;
pub const COL_PRECOMPILE_INDEX: usize = 19;

// Temporary columns (stored to avoid duplicate computations)
pub const N_TEMPORARY_EXEC_COLUMNS: usize = 4;
pub const COL_IS_PRECOMPILE: usize = 20;
pub const COL_EXEC_NU_A: usize = 21;
pub const COL_EXEC_NU_B: usize = 22;
pub const COL_EXEC_NU_C: usize = 23;

const PRECOMPILE_A_INDEX: F = F::new(ALL_TABLES[1].index() as u32);
const PRECOMPILE_B_INDEX: F = F::new(ALL_TABLES[2].index() as u32);
const MINUS_ONE_OVER_AB_PRECOMPILES: usize = 1065353216;
const MINUS_A_MINUS_B_PRECOMPILES: usize = 2130706430;

#[test]
fn test_precompile_indices() {
    const _: () = assert!(crate::N_TABLES - 1 == 2); // ONLY 2 PRECOMPILES
    assert!(crate::TableT::is_execution_table(&ALL_TABLES[0])); // First table must be execution table
    assert_eq!(
        -(PRECOMPILE_A_INDEX * PRECOMPILE_B_INDEX).inverse(),
        F::from_usize(MINUS_ONE_OVER_AB_PRECOMPILES)
    );
    assert_eq!(
        -PRECOMPILE_A_INDEX - PRECOMPILE_B_INDEX,
        F::from_usize(MINUS_A_MINUS_B_PRECOMPILES)
    );
}

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
        16
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
        let add = up[COL_ADD].clone();
        let mul = up[COL_MUL].clone();
        let deref = up[COL_DEREF].clone();
        let jump = up[COL_JUMP].clone();
        let aux = up[COL_AUX].clone();
        let precompile_index = up[COL_PRECOMPILE_INDEX].clone();

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
        let flag_c_minus_one = flag_c.clone() - AB::F::ONE;

        let nu_a = flag_a * operand_a.clone() + value_a.clone() * -flag_a_minus_one.clone();
        let nu_b = flag_b * operand_b.clone() + value_b.clone() * -flag_b_minus_one.clone();
        let nu_c = flag_c * fp.clone() + value_c.clone() * -flag_c_minus_one.clone();

        let fp_plus_operand_a = fp.clone() + operand_a.clone();
        let fp_plus_operand_b = fp.clone() + operand_b.clone();
        let fp_plus_operand_c = fp.clone() + operand_c.clone();
        let pc_plus_one = pc + AB::F::ONE;
        let nu_a_minus_one = nu_a.clone() - AB::F::ONE;

        /*
        A = index_of_precompile_A
        B = index_of_precompile_B
        X = precompile_index (0 by default, set to A or B when calling precompile)
        is_precompile = X * (-1/(A*B)) * (X + (-A - B)) (= 1 if X == A or X == B, 0 if X == 0)
        */
        let is_precompile = precompile_index.clone()
            * AB::F::from_usize(MINUS_ONE_OVER_AB_PRECOMPILES)
            * (precompile_index.clone() + AB::F::from_usize(MINUS_A_MINUS_B_PRECOMPILES));

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                precompile_index.clone(),
                is_precompile.clone(),
                &[nu_a.clone(), nu_b.clone(), nu_c.clone(), aux.clone()],
            ));
        } else {
            builder.declare_values(&[is_precompile]);
            builder.declare_values(&[nu_a.clone(), nu_b.clone(), nu_c.clone(), aux.clone()]);
        }

        builder.assert_zero(flag_a_minus_one * (addr_a.clone() - fp_plus_operand_a));
        builder.assert_zero(flag_b_minus_one * (addr_b.clone() - fp_plus_operand_b));
        builder.assert_zero(flag_c_minus_one * (addr_c.clone() - fp_plus_operand_c));

        builder.assert_zero(add * (nu_b.clone() - (nu_a.clone() + nu_c.clone())));
        builder.assert_zero(mul * (nu_b.clone() - nu_a.clone() * nu_c.clone()));

        builder.assert_zero(deref.clone() * (addr_c.clone() - (value_a.clone() + operand_c.clone())));
        builder.assert_zero(deref.clone() * aux.clone() * (value_c.clone() - nu_b.clone()));
        builder.assert_zero(deref.clone() * (aux.clone() - AB::F::ONE) * (value_c.clone() - fp.clone()));

        builder.assert_zero((jump.clone() - AB::F::ONE) * (next_pc.clone() - pc_plus_one.clone()));
        builder.assert_zero((jump.clone() - AB::F::ONE) * (next_fp.clone() - fp.clone()));

        builder.assert_zero(jump.clone() * nu_a.clone() * nu_a_minus_one.clone());
        builder.assert_zero(jump.clone() * nu_a.clone() * (next_pc.clone() - nu_b.clone()));
        builder.assert_zero(jump.clone() * nu_a.clone() * (next_fp.clone() - nu_c.clone()));
        builder.assert_zero(jump.clone() * nu_a_minus_one.clone() * (next_pc.clone() - pc_plus_one.clone()));
        builder.assert_zero(jump.clone() * nu_a_minus_one.clone() * (next_fp.clone() - fp.clone()));
    }
}

pub const fn instr_idx(col_index_in_air: usize) -> usize {
    col_index_in_air - N_RUNTIME_COLUMNS
}
