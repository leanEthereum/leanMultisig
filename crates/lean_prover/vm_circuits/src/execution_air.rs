use std::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use witness_generation::*;

/*

Bytecode columns:

0: OPERAND_A
1: OPERAND_B
2: OPERAND_C
3: FLAG_A
4: FLAG_B
5: FLAG_C
6: ADD
7: MUL
8: DEREF
9: JUMP
10: AUX

Execution columns:

11: VALUE_A (virtual)
12: VALUE_B (virtual)
13: VALUE_C (virtual)
14: PC
15: FP
16: ADDR_A
17: ADDR_B
18: ADDR_C

*/

#[derive(Debug)]
pub struct VMAir;

impl<F> BaseAir<F> for VMAir {
    fn width(&self) -> usize {
        N_EXEC_AIR_COLUMNS
    }
    fn structured(&self) -> bool {
        true
    }
    fn degree(&self) -> usize {
        5
    }
}

impl<AB: AirBuilder> Air<AB> for VMAir {
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = main.row_slice(0).unwrap();
        let up: &[AB::Var] = (*up).borrow();
        assert_eq!(up.len(), N_EXEC_AIR_COLUMNS);
        let down = main.row_slice(1).unwrap();
        let down: &[AB::Var] = (*down).borrow();
        assert_eq!(down.len(), N_EXEC_AIR_COLUMNS);

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

        let (value_a, value_b, value_c) = (
            up[COL_INDEX_MEM_VALUE_A.index_in_air()].clone(),
            up[COL_INDEX_MEM_VALUE_B.index_in_air()].clone(),
            up[COL_INDEX_MEM_VALUE_C.index_in_air()].clone(),
        );
        let (pc, next_pc) = (
            up[COL_INDEX_PC.index_in_air()].clone(),
            down[COL_INDEX_PC.index_in_air()].clone(),
        );
        let (fp, next_fp) = (
            up[COL_INDEX_FP.index_in_air()].clone(),
            down[COL_INDEX_FP.index_in_air()].clone(),
        );
        let (addr_a, addr_b, addr_c) = (
            up[COL_INDEX_MEM_ADDRESS_A.index_in_air()].clone(),
            up[COL_INDEX_MEM_ADDRESS_B.index_in_air()].clone(),
            up[COL_INDEX_MEM_ADDRESS_C.index_in_air()].clone(),
        );

        let flag_a_minus_one = flag_a.clone() - AB::F::ONE;
        let flag_b_minus_one = flag_b.clone() - AB::F::ONE;
        let flag_c_minus_one = flag_c.clone() - AB::F::ONE;

        let nu_a = flag_a.clone() * operand_a.clone() + value_a.clone() * -flag_a_minus_one.clone();
        let nu_b = flag_b.clone() * operand_b.clone() + value_b * -flag_b_minus_one.clone();
        let nu_c = flag_c.clone() * fp.clone() + value_c.clone() * -flag_c_minus_one.clone();

        let fp_plus_operand_a = fp.clone() + operand_a;
        let fp_plus_operand_b = fp.clone() + operand_b;
        let fp_plus_operand_c = fp.clone() + operand_c.clone();
        let pc_plus_one = pc.clone() + AB::F::ONE;
        let nu_a_minus_one = nu_a.clone() - AB::F::ONE;

        builder.assert_zero(flag_a_minus_one * (addr_a - fp_plus_operand_a));
        builder.assert_zero(flag_b_minus_one * (addr_b - fp_plus_operand_b));
        builder.assert_zero(flag_c_minus_one * (addr_c.clone() - fp_plus_operand_c));

        builder.assert_zero(add * (nu_b.clone() - (nu_a.clone() + nu_c.clone())));
        builder.assert_zero(mul * (nu_b.clone() - nu_a.clone() * nu_c.clone()));

        builder.assert_zero(deref.clone() * (addr_c - (value_a + operand_c)));
        builder.assert_zero(deref.clone() * aux.clone() * (value_c.clone() - nu_b.clone()));
        builder.assert_zero(deref * (aux - AB::F::ONE) * (value_c - fp.clone()));

        builder.assert_zero((jump.clone() - AB::F::ONE) * (next_pc.clone() - pc_plus_one.clone()));
        builder.assert_zero((jump.clone() - AB::F::ONE) * (next_fp.clone() - fp.clone()));

        builder.assert_zero(jump.clone() * nu_a.clone() * nu_a_minus_one.clone());
        builder.assert_zero(jump.clone() * nu_a.clone() * (next_pc.clone() - nu_b));
        builder.assert_zero(jump.clone() * nu_a.clone() * (next_fp.clone() - nu_c));
        builder.assert_zero(jump.clone() * nu_a_minus_one.clone() * (next_pc - pc_plus_one));
        builder.assert_zero(jump * nu_a_minus_one * (next_fp - fp));
    }
}
