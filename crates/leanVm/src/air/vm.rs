use std::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

use crate::air::constant::{
    COL_INDEX_ADD, COL_INDEX_ADDR_A, COL_INDEX_ADDR_B, COL_INDEX_ADDR_C, COL_INDEX_AUX,
    COL_INDEX_DEREF, COL_INDEX_FLAG_A, COL_INDEX_FLAG_B, COL_INDEX_FLAG_C, COL_INDEX_FP,
    COL_INDEX_JUZ, COL_INDEX_MEM_VALUE_A, COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C,
    COL_INDEX_MUL, COL_INDEX_OPERAND_A, COL_INDEX_OPERAND_B, COL_INDEX_OPERAND_C, COL_INDEX_PC,
    N_EXEC_AIR_COLUMNS,
};

/// Virtual Machine AIR
#[derive(Debug)]
pub struct VMAir;

impl<F> BaseAir<F> for VMAir {
    /// The total number of columns in the execution trace.
    fn width(&self) -> usize {
        N_EXEC_AIR_COLUMNS
    }
}

impl<AB: AirBuilder> Air<AB> for VMAir {
    #[inline]
    fn eval(&self, builder: &mut AB) {
        // Get a view of the main execution trace.
        let main = builder.main();

        // Get the current row (`local`) and the next row (`next`) from the trace.
        let local = main.row_slice(0).unwrap();
        let local = local.borrow();

        let next = main.row_slice(1).unwrap();
        let next = next.borrow();

        // INSTRUCTION DECODING
        //
        // Extract instruction fields (operands, flags, and opcodes) from the local row.
        //
        // These are treated as constants for a given row, looked up from the bytecode.
        let operand_a = local[COL_INDEX_OPERAND_A].clone().into();
        let operand_b = local[COL_INDEX_OPERAND_B].clone().into();
        let operand_c = local[COL_INDEX_OPERAND_C].clone().into();
        let flag_a = local[COL_INDEX_FLAG_A].clone().into();
        let flag_b = local[COL_INDEX_FLAG_B].clone().into();
        let flag_c = local[COL_INDEX_FLAG_C].clone().into();
        let add = local[COL_INDEX_ADD].clone().into();
        let mul = local[COL_INDEX_MUL].clone().into();
        let deref = local[COL_INDEX_DEREF].clone().into();
        let juz = local[COL_INDEX_JUZ].clone().into();
        let aux = local[COL_INDEX_AUX].clone().into();

        // REGISTER & MEMORY VALUES
        //
        // Extract register values and memory access data from the trace.
        let (pc, next_pc) = (
            local[COL_INDEX_PC].clone().into(),
            next[COL_INDEX_PC].clone().into(),
        );
        let (fp, next_fp) = (
            local[COL_INDEX_FP].clone().into(),
            next[COL_INDEX_FP].clone().into(),
        );
        let (addr_a, addr_b, addr_c) = (
            local[COL_INDEX_ADDR_A].clone().into(),
            local[COL_INDEX_ADDR_B].clone().into(),
            local[COL_INDEX_ADDR_C].clone().into(),
        );
        let (value_a, value_b, value_c) = (
            local[COL_INDEX_MEM_VALUE_A].clone().into(),
            local[COL_INDEX_MEM_VALUE_B].clone().into(),
            local[COL_INDEX_MEM_VALUE_C].clone().into(),
        );

        // OPERAND RECONSTRUCTION
        //
        // Compute the effective values of the operands (`nu_a`, `nu_b`, `nu_c`).
        //
        // Each operand can be either:
        // - an immediate value (from `operand_x`),
        // - a value loaded from memory (from `value_x`), selected by `flag_x`.
        //
        // Formula: nu_x = flag_x * operand_x + (1 - flag_x) * value_x
        let nu_a =
            flag_a.clone() * operand_a.clone() + (AB::Expr::ONE - flag_a.clone()) * value_a.clone();
        let nu_b = flag_b.clone() * operand_b.clone() + (AB::Expr::ONE - flag_b.clone()) * value_b;
        // Operand `c` is special: its immediate value can be the frame pointer `fp` itself.
        let nu_c = flag_c.clone() * fp.clone() + (AB::Expr::ONE - flag_c.clone()) * value_c.clone();

        // MEMORY ADDRESS CONSTRAINTS
        //
        // Enforce that if an operand is loaded from memory (`flag_x` = 0), its address
        // (`addr_x`) must correctly correspond to the frame pointer plus its offset (`fp + operand_x`).
        //
        // If `flag_x` = 1, the constraint is `0 * ... = 0`, so it is satisfied.
        builder.assert_zero((AB::Expr::ONE - flag_a) * (addr_a - (fp.clone() + operand_a)));
        builder.assert_zero((AB::Expr::ONE - flag_b) * (addr_b - (fp.clone() + operand_b)));
        builder.assert_zero(
            (AB::Expr::ONE - flag_c) * (addr_c.clone() - (fp.clone() + operand_c.clone())),
        );

        // INSTRUCTION CONSTRAINTS

        // ADD Instruction Constraint
        //
        // If the `add` opcode is active, enforce `nu_a + nu_c = nu_b`.
        builder.assert_zero(add * (nu_b.clone() - (nu_a.clone() + nu_c.clone())));

        // MUL Instruction Constraint
        //
        // If the `mul` opcode is active, enforce `nu_a * nu_c = nu_b`.
        builder.assert_zero(mul * (nu_b.clone() - nu_a.clone() * nu_c.clone()));

        // DEREF Instruction Constraints
        //
        // This instruction computes `m[m[fp + α] + β] = res`.
        //
        // 1. Enforce that the final address `addr_c` is computed correctly: `addr_c = value_a + operand_c`.
        //
        // Here, `value_a` is the pointer `m[fp + α]` and `operand_c` is the offset `β`.
        builder.assert_zero(deref.clone() * (addr_c - (value_a + operand_c)));
        // 2. If `aux` = 1, the result `res` is a normal value (`nu_b`). Enforce `value_c = nu_b`.
        builder.assert_zero(deref.clone() * aux.clone() * (value_c.clone() - nu_b.clone()));
        // 3. If `aux` = 0, the result `res` is the frame pointer itself. Enforce `value_c = fp`.
        builder.assert_zero(deref * (AB::Expr::ONE - aux) * (value_c - fp.clone()));

        // JUZ (Jump Unless Zero) and Program Flow Constraints

        // Default Program Flow (No Jump)
        //
        // If `juz` is not active, the program counter must increment by 1.
        builder.assert_zero(
            (AB::Expr::ONE - juz.clone()) * (next_pc.clone() - (pc.clone() + AB::Expr::ONE)),
        );
        // If `juz` is not active, the frame pointer must remain unchanged.
        builder.assert_zero((AB::Expr::ONE - juz.clone()) * (next_fp.clone() - fp.clone()));

        // JUZ Active Program Flow
        //
        // The condition for the jump is `nu_a`.
        // 1. Enforce that the condition `nu_a` is boolean (0 or 1).
        builder.assert_zero(juz.clone() * nu_a.clone() * (AB::Expr::ONE - nu_a.clone()));
        // 2. If jump is taken (`nu_a` = 1), the next `pc` must be the destination `nu_b`.
        builder.assert_zero(juz.clone() * nu_a.clone() * (next_pc.clone() - nu_b));
        // 3. If jump is taken (`nu_a` = 1), the next `fp` must be the new frame pointer `nu_c`.
        builder.assert_zero(juz.clone() * nu_a.clone() * (next_fp.clone() - nu_c));
        // 4. If jump is NOT taken (`nu_a` = 0), the next `pc` must be `pc + 1`.
        builder.assert_zero(
            juz.clone() * (AB::Expr::ONE - nu_a.clone()) * (next_pc - (pc + AB::Expr::ONE)),
        );
        // 5. If jump is NOT taken (`nu_a` = 0), the next `fp` must be the same as the current `fp`.
        builder.assert_zero(juz * (AB::Expr::ONE - nu_a) * (next_fp - fp));
    }
}
