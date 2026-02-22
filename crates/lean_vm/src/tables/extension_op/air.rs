use crate::{EF, ExtraDataForBuses, eval_virtual_bus_column, tables::extension_op::ExtensionOpPrecompile};
use backend::*;

// F columns (AIR)
pub(super) const EXT_COL_IS_BE: usize = 0;
pub(super) const EXT_COL_FLAG: usize = 1;
pub(super) const EXT_COL_FLAG_ADD: usize = 2;
pub(super) const EXT_COL_FLAG_MUL: usize = 3;
pub(super) const EXT_COL_FLAG_POLY_EQ: usize = 4;
pub(super) const EXT_COL_ARG_A: usize = 5;
pub(super) const EXT_COL_IDX_B: usize = 6;
pub(super) const EXT_COL_IDX_R: usize = 7;
pub(super) const EXT_COL_VALUE_A_F: usize = 8;
// F columns (non-AIR, used only for bus data in logup (prover side))
// aux = 2*is_be + 4*flag_add + 8*flag_mul + 16*flag_poly_eq
pub(super) const EXT_COL_AUX: usize = 9;
// EF columns
pub(super) const EXT_COL_VALUE_A_EF: usize = 0;
pub(super) const EXT_COL_VALUE_B: usize = 1;
pub(super) const EXT_COL_VALUE_RES: usize = 2;

impl<const BUS: bool> Air for ExtensionOpPrecompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns_f_air(&self) -> usize {
        9
    }
    fn n_columns_ef_air(&self) -> usize {
        3
    }
    fn degree_air(&self) -> usize {
        4 // due to flag_mul * (res - v_A * v_B) where v_A involves is_be * arg_A
    }
    fn n_constraints(&self) -> usize {
        9
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![] // no transition constraints
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![] // no transition constraints
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up_f = builder.up_f();
        let up_ef = builder.up_ef();

        let is_be = up_f[EXT_COL_IS_BE].clone();
        let flag = up_f[EXT_COL_FLAG].clone();
        let flag_add = up_f[EXT_COL_FLAG_ADD].clone();
        let flag_mul = up_f[EXT_COL_FLAG_MUL].clone();
        let flag_poly_eq = up_f[EXT_COL_FLAG_POLY_EQ].clone();
        let arg_a = up_f[EXT_COL_ARG_A].clone();
        let idx_b = up_f[EXT_COL_IDX_B].clone();
        let idx_r = up_f[EXT_COL_IDX_R].clone();
        let value_a_f = up_f[EXT_COL_VALUE_A_F].clone();

        let value_a_ef = up_ef[EXT_COL_VALUE_A_EF].clone();
        let value_b = up_ef[EXT_COL_VALUE_B].clone();
        let res = up_ef[EXT_COL_VALUE_RES].clone();

        // aux = 2*is_be + 4*flag_add + 8*flag_mul + 16*flag_poly_eq (virtual)
        let aux = is_be.double()
            + flag_add.clone() * AB::F::from_usize(4)
            + flag_mul.clone() * AB::F::from_usize(8)
            + flag_poly_eq.clone() * AB::F::from_usize(16);

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                flag.clone(),
                &[aux, arg_a.clone(), idx_b, idx_r],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&flag));
            builder.declare_values(&[aux, arg_a.clone(), idx_b, idx_r]);
        }

        // v_A = is_be * [VALUE_A_F, 0, 0, 0, 0] + (1 - is_be) * v_A_EF  (virtual, over Fq)
        let is_ee = AB::F::ONE - is_be.clone();
        let v_a = AB::EF::from(is_be.clone() * value_a_f) + value_a_ef * is_ee;

        // 1. is_be * (1 - is_be) = 0
        builder.assert_bool(is_be);
        // 2. flag * (1 - flag) = 0
        builder.assert_bool(flag.clone());
        // 3. flag_add * (1 - flag_add) = 0
        builder.assert_bool(flag_add.clone());
        // 4. flag_mul * (1 - flag_mul) = 0
        builder.assert_bool(flag_mul.clone());
        // 5. flag_poly_eq * (1 - flag_poly_eq) = 0
        builder.assert_bool(flag_poly_eq.clone());
        // 6. flag_add + flag_mul + flag_poly_eq - flag = 0
        builder.assert_zero(flag_add.clone() + flag_mul.clone() + flag_poly_eq.clone() - flag);

        // 7. flag_add * (res - v_A - v_B) = 0  (over Fq)
        builder.assert_zero_ef(AB::EF::from(flag_add) * (res.clone() - v_a.clone() - value_b.clone()));
        // 8. flag_mul * (res - v_A * v_B) = 0  (over Fq)
        builder.assert_zero_ef(AB::EF::from(flag_mul) * (res.clone() - v_a.clone() * value_b.clone()));
        // 9. flag_poly_eq * (res - v_A * v_B - (1 - v_A) * (1 - v_B)) = 0  (over Fq)
        let one = AB::EF::ONE;
        let poly_eq_val = v_a.clone() * value_b.clone() + (one.clone() - v_a) * (one - value_b);
        builder.assert_zero_ef(AB::EF::from(flag_poly_eq) * (res - poly_eq_val));
    }
}
