use std::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use zk_vm_trace::*;

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

        let (operand_a, operand_b, operand_c): (AB::Expr, AB::Expr, AB::Expr) = (
            up[COL_INDEX_OPERAND_A].clone().into(),
            up[COL_INDEX_OPERAND_B].clone().into(),
            up[COL_INDEX_OPERAND_C].clone().into(),
        );
        let (flag_a, flag_b, flag_c): (AB::Expr, AB::Expr, AB::Expr) = (
            up[COL_INDEX_FLAG_A].clone().into(),
            up[COL_INDEX_FLAG_B].clone().into(),
            up[COL_INDEX_FLAG_C].clone().into(),
        );
        let add: AB::Expr = up[COL_INDEX_ADD].clone().into();
        let mul: AB::Expr = up[COL_INDEX_MUL].clone().into();
        let deref: AB::Expr = up[COL_INDEX_DEREF].clone().into();
        let jump: AB::Expr = up[COL_INDEX_JUMP].clone().into();
        let aux: AB::Expr = up[COL_INDEX_AUX].clone().into();

        let (value_a, value_b, value_c): (AB::Expr, AB::Expr, AB::Expr) = (
            up[COL_INDEX_MEM_VALUE_A.index_in_air()].clone().into(),
            up[COL_INDEX_MEM_VALUE_B.index_in_air()].clone().into(),
            up[COL_INDEX_MEM_VALUE_C.index_in_air()].clone().into(),
        );
        let (pc, next_pc): (AB::Expr, AB::Expr) = (
            up[COL_INDEX_PC.index_in_air()].clone().into(),
            down[COL_INDEX_PC.index_in_air()].clone().into(),
        );
        let (fp, next_fp): (AB::Expr, AB::Expr) = (
            up[COL_INDEX_FP.index_in_air()].clone().into(),
            down[COL_INDEX_FP.index_in_air()].clone().into(),
        );
        let (addr_a, addr_b, addr_c): (AB::Expr, AB::Expr, AB::Expr) = (
            up[COL_INDEX_MEM_ADDRESS_A.index_in_air()].clone().into(),
            up[COL_INDEX_MEM_ADDRESS_B.index_in_air()].clone().into(),
            up[COL_INDEX_MEM_ADDRESS_C.index_in_air()].clone().into(),
        );

        let nu_a =
            flag_a.clone() * operand_a.clone() + value_a.clone() * (AB::Expr::ONE - flag_a.clone());
        let nu_b = flag_b.clone() * operand_b.clone() + value_b * (AB::Expr::ONE - flag_b.clone());
        let nu_c = flag_c.clone() * fp.clone() + value_c.clone() * (AB::Expr::ONE - flag_c.clone());

        builder.assert_zero((AB::Expr::ONE - flag_a) * (addr_a - (fp.clone() + operand_a)));
        builder.assert_zero((AB::Expr::ONE - flag_b) * (addr_b - (fp.clone() + operand_b)));
        builder.assert_zero(
            (AB::Expr::ONE - flag_c) * (addr_c.clone() - (fp.clone() + operand_c.clone())),
        );

        builder.assert_zero(add * (nu_b.clone() - (nu_a.clone() + nu_c.clone())));
        builder.assert_zero(mul * (nu_b.clone() - nu_a.clone() * nu_c.clone()));

        builder.assert_zero(deref.clone() * (addr_c - (value_a + operand_c)));
        builder.assert_zero(deref.clone() * aux.clone() * (value_c.clone() - nu_b.clone()));
        builder.assert_zero(deref * (AB::Expr::ONE - aux) * (value_c - fp.clone()));

        builder.assert_zero(
            (AB::Expr::ONE - jump.clone()) * (next_pc.clone() - (pc.clone() + AB::Expr::ONE)),
        );
        builder.assert_zero((AB::Expr::ONE - jump.clone()) * (next_fp.clone() - fp.clone()));

        builder.assert_zero(jump.clone() * nu_a.clone() * (AB::Expr::ONE - nu_a.clone()));
        builder.assert_zero(jump.clone() * nu_a.clone() * (next_pc.clone() - nu_b));
        builder.assert_zero(jump.clone() * nu_a.clone() * (next_fp.clone() - nu_c));
        builder.assert_zero(
            jump.clone() * (AB::Expr::ONE - nu_a.clone()) * (next_pc - (pc + AB::Expr::ONE)),
        );
        builder.assert_zero(jump * (AB::Expr::ONE - nu_a) * (next_fp - fp));
    }
}
