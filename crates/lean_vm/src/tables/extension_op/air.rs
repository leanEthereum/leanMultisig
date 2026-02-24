use crate::{
    EF, ExtraDataForBuses, eval_virtual_bus_column,
    tables::extension_op::{EXT_OP_LEN_MULTIPLIER, ExtensionOpPrecompile},
};
use backend::*;

// F columns
pub(super) const COL_IS_BE: usize = 0;
pub(super) const COL_START: usize = 1;
pub(super) const COL_FLAG_ADD: usize = 2;
pub(super) const COL_FLAG_MUL: usize = 3;
pub(super) const COL_FLAG_POLY_EQ: usize = 4;
pub(super) const COL_LEN: usize = 5;
pub(super) const COL_IDX_A: usize = 6;
pub(super) const COL_IDX_B: usize = 7;
pub(super) const COL_IDX_RES: usize = 8;
pub(super) const COL_VALUE_A_F: usize = 9;

// Virtual (F) columns
pub(super) const COL_ACTIVATION_FLAG: usize = 10;
pub(super) const COL_AUX_EXTENSION_OP: usize = 11;

// EF columns (AIR, 4 total)
pub(super) const COL_VALUE_A_EF: usize = 0;
pub(super) const COL_VALUE_B: usize = 1;
pub(super) const COL_VALUE_RES: usize = 2;
pub(super) const COL_COMPUTATION: usize = 3;

impl<const BUS: bool> Air for ExtensionOpPrecompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns_f_air(&self) -> usize {
        10
    }
    fn n_columns_ef_air(&self) -> usize {
        4
    }
    fn degree_air(&self) -> usize {
        6
    }
    fn n_constraints(&self) -> usize {
        17
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![
            COL_START,
            COL_IS_BE,
            COL_LEN,
            COL_FLAG_ADD,
            COL_FLAG_MUL,
            COL_FLAG_POLY_EQ,
            COL_IDX_A,
            COL_IDX_B,
        ]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![COL_COMPUTATION]
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up_f = builder.up_f();
        let down_f = builder.down_f();
        let up_ef = builder.up_ef();
        let down_ef = builder.down_ef();

        let is_be = up_f[COL_IS_BE].clone();
        let start = up_f[COL_START].clone();
        let flag_add = up_f[COL_FLAG_ADD].clone();
        let flag_mul = up_f[COL_FLAG_MUL].clone();
        let flag_poly_eq = up_f[COL_FLAG_POLY_EQ].clone();
        let len = up_f[COL_LEN].clone();
        let idx_a = up_f[COL_IDX_A].clone();
        let idx_b = up_f[COL_IDX_B].clone();
        let value_a_f = up_f[COL_VALUE_A_F].clone();

        let start_down = down_f[0].clone(); // COL_START
        let is_be_down = down_f[1].clone(); // COL_IS_BE
        let len_down = down_f[2].clone(); // COL_LEN
        let flag_add_down = down_f[3].clone(); // COL_FLAG_ADD
        let flag_mul_down = down_f[4].clone(); // COL_FLAG_MUL
        let flag_poly_eq_down = down_f[5].clone(); // COL_FLAG_POLY_EQ
        let idx_a_down = down_f[6].clone(); // COL_IDX_A
        let idx_b_down = down_f[7].clone(); // COL_IDX_B

        let value_a_ef = up_ef[COL_VALUE_A_EF].clone();
        let value_b = up_ef[COL_VALUE_B].clone();
        let res = up_ef[COL_VALUE_RES].clone();
        let computation = up_ef[COL_COMPUTATION].clone();

        let computation_down = down_ef[0].clone(); // COL_COMPUTATION

        let active = flag_add.clone() + flag_mul.clone() + flag_poly_eq.clone();

        let activation_flag = start.clone() * active.clone();

        // aux = 2*is_be + 4*flag_add + 8*flag_mul + 16*flag_poly_eq + 32*len (virtual)
        let aux = is_be.clone().double()
            + flag_add.clone() * AB::F::from_usize(4)
            + flag_mul.clone() * AB::F::from_usize(8)
            + flag_poly_eq.clone() * AB::F::from_usize(16)
            + len.clone() * AB::F::from_usize(EXT_OP_LEN_MULTIPLIER);

        let idx_r = up_f[COL_IDX_RES].clone();

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                activation_flag,
                &[aux, idx_a.clone(), idx_b.clone(), idx_r],
            ));
        } else {
            builder.declare_values(&[activation_flag]);
            builder.declare_values(&[aux, idx_a.clone(), idx_b.clone(), idx_r]);
        }

        let is_ee = AB::F::ONE - is_be.clone();
        let v_a = value_a_ef * is_ee.clone() + is_be.clone() * value_a_f;

        let not_start_down = AB::F::ONE - start_down.clone();

        builder.assert_bool(is_be.clone());
        builder.assert_bool(start.clone());
        builder.assert_bool(flag_add.clone());
        builder.assert_bool(flag_mul.clone());
        builder.assert_bool(flag_poly_eq.clone());

        let comp_tail = computation_down.clone() * not_start_down.clone();

        builder.assert_zero_ef(
            (computation.clone() - (v_a.clone() + value_b.clone() + comp_tail.clone())) * flag_add.clone(),
        );
        builder.assert_zero_ef((computation.clone() - (v_a.clone() * value_b.clone() + comp_tail)) * flag_mul.clone());
        let poly_eq_val = (v_a.clone() * value_b.clone()).double() - v_a - value_b + AB::F::ONE;
        let comp_down_or_one = computation_down * not_start_down.clone() + start_down.clone();
        builder.assert_zero_ef((computation.clone() - poly_eq_val * comp_down_or_one) * flag_poly_eq.clone());

        builder.assert_zero_ef((computation - res) * start.clone());

        builder.assert_zero(not_start_down.clone() * (len.clone() - len_down - AB::F::ONE));
        builder.assert_zero(not_start_down.clone() * (is_be.clone() - is_be_down));
        builder.assert_zero(not_start_down.clone() * (flag_add - flag_add_down));
        builder.assert_zero(not_start_down.clone() * (flag_mul - flag_mul_down));
        builder.assert_zero(not_start_down.clone() * (flag_poly_eq - flag_poly_eq_down));
        let a_increment = is_be.clone() + is_ee * AB::F::from_usize(crate::DIMENSION);
        builder.assert_zero(not_start_down.clone() * (idx_a_down - idx_a - a_increment));
        builder.assert_zero(not_start_down * (idx_b_down - idx_b - AB::F::from_usize(crate::DIMENSION)));

        builder.assert_zero(start_down * (len - AB::F::ONE));
    }
}
