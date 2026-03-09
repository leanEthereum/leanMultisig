use crate::{
    EF, ExtraDataForBuses, eval_virtual_bus_column,
    tables::extension_op::{EXT_OP_LEN_MULTIPLIER, ExtensionOpPrecompile},
};
use backend::*;

//0..5 columns (AIR, 29 total)
pub(super) const COL_IS_BE: usize = 0;
pub(super) const COL_START: usize = 1;
pub(super) const COL_FLAG_ADD: usize = 2;
pub(super) const COL_FLAG_MUL: usize = 3;
pub(super) const COL_FLAG_POLY_EQ: usize = 4;
pub(super) const COL_LEN: usize = 5;
pub(super) const COL_IDX_A: usize = 6;
pub(super) const COL_IDX_B: usize = 7;
pub(super) const COL_IDX_RES: usize = 8;

/// value_a coordinates (5 columns)
pub(super) const COL_VA: usize = 9;
/// value_b coordinates (5 columns)
pub(super) const COL_VB: usize = 14;
/// result coordinates (5 columns).
pub(super) const COL_VRES: usize = 19;
/// computation coordinates (5 columns)
pub(super) const COL_COMP: usize = 24;

// Virtual columns (not explicitely in AIR)
pub(super) const COL_ACTIVATION_FLAG: usize = 29;
pub(super) const COL_AUX_EXTENSION_OP: usize = 30;

use backend::quintic_extension::extension::quintic_mul;

#[inline]
fn quintic_mul_air<T: PrimeCharacteristicRing>(a: &[T; 5], b: &[T; 5]) -> [T; 5] {
    quintic_mul(a, b, |x, y| {
        x[0] * y[0] + x[1] * y[1] + x[2] * y[2] + x[3] * y[3] + x[4] * y[4]
    })
}

impl<const BUS: bool> Air for ExtensionOpPrecompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        29
    }
    fn degree_air(&self) -> usize {
        6
    }
    fn n_constraints(&self) -> usize {
        33
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![
            COL_START,
            COL_IS_BE,
            COL_LEN,
            COL_FLAG_ADD,
            COL_FLAG_MUL,
            COL_FLAG_POLY_EQ,
            COL_IDX_A,
            COL_IDX_B,
            COL_COMP,
            COL_COMP + 1,
            COL_COMP + 2,
            COL_COMP + 3,
            COL_COMP + 4,
        ]
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up();
        let down = builder.down();

        let is_be = up[COL_IS_BE];
        let start = up[COL_START];
        let flag_add = up[COL_FLAG_ADD];
        let flag_mul = up[COL_FLAG_MUL];
        let flag_poly_eq = up[COL_FLAG_POLY_EQ];
        let len = up[COL_LEN];
        let idx_a = up[COL_IDX_A];
        let idx_b = up[COL_IDX_B];

        let va: [AB::F; 5] = std::array::from_fn(|k| up[COL_VA + k]);
        let vb: [AB::F; 5] = std::array::from_fn(|k| up[COL_VB + k]);
        let vres: [AB::F; 5] = std::array::from_fn(|k| up[COL_VRES + k]);
        let comp: [AB::F; 5] = std::array::from_fn(|k| up[COL_COMP + k]);

        let start_down = down[0]; // COL_START
        let is_be_down = down[1]; // COL_IS_BE
        let len_down = down[2]; // COL_LEN
        let flag_add_down = down[3]; // COL_FLAG_ADD
        let flag_mul_down = down[4]; // COL_FLAG_MUL
        let flag_poly_eq_down = down[5]; // COL_FLAG_POLY_EQ
        let idx_a_down = down[6]; // COL_IDX_A
        let idx_b_down = down[7]; // COL_IDX_B
        let comp_down: [AB::F; 5] = std::array::from_fn(|k| down[8 + k]); // COL_COMP+0..5

        let active = flag_add + flag_mul + flag_poly_eq;
        let activation_flag = start * active;

        let aux = is_be.double()
            + flag_add * AB::F::from_usize(4)
            + flag_mul * AB::F::from_usize(8)
            + flag_poly_eq * AB::F::from_usize(16)
            + len * AB::F::from_usize(EXT_OP_LEN_MULTIPLIER);

        let idx_r = up[COL_IDX_RES];

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                activation_flag,
                &[aux, idx_a, idx_b, idx_r],
            ));
        } else {
            builder.declare_values(&[activation_flag]);
            builder.declare_values(&[aux, idx_a, idx_b, idx_r]);
        }

        let is_ee = AB::F::ONE - is_be;
        let not_start_down = AB::F::ONE - start_down;

        let va_f_or_ef: [AB::F; 5] = std::array::from_fn(|k| if k == 0 { va[0] } else { va[k] * is_ee });

        let comp_tail: [AB::F; 5] = std::array::from_fn(|k| comp_down[k] * not_start_down);

        builder.assert_bool(is_be);
        builder.assert_bool(start);
        builder.assert_bool(flag_add);
        builder.assert_bool(flag_mul);
        builder.assert_bool(flag_poly_eq);

        for k in 0..5 {
            builder.assert_zero((comp[k] - (va_f_or_ef[k] + vb[k] + comp_tail[k])) * flag_add);
        }

        let va_times_vb = quintic_mul_air(&va_f_or_ef, &vb);

        for k in 0..5 {
            builder.assert_zero((comp[k] - (va_times_vb[k] + comp_tail[k])) * flag_mul);
        }

        let poly_eq_val: [AB::F; 5] = std::array::from_fn(|k| {
            let base = va_times_vb[k].double() - va_f_or_ef[k] - vb[k];
            if k == 0 { base + AB::F::ONE } else { base }
        });
        let comp_down_or_one: [AB::F; 5] = std::array::from_fn(|k| {
            if k == 0 {
                comp_down[0] * not_start_down + start_down
            } else {
                comp_down[k] * not_start_down
            }
        });
        let poly_eq_result = quintic_mul_air(&poly_eq_val, &comp_down_or_one);
        for k in 0..5 {
            builder.assert_zero((comp[k] - poly_eq_result[k]) * flag_poly_eq);
        }

        for k in 0..5 {
            builder.assert_zero((comp[k] - vres[k]) * start);
        }

        builder.assert_zero(not_start_down * (len - len_down - AB::F::ONE));
        builder.assert_zero(not_start_down * (is_be - is_be_down));
        builder.assert_zero(not_start_down * (flag_add - flag_add_down));
        builder.assert_zero(not_start_down * (flag_mul - flag_mul_down));
        builder.assert_zero(not_start_down * (flag_poly_eq - flag_poly_eq_down));
        let a_increment = is_be + is_ee * AB::F::from_usize(crate::DIMENSION);
        builder.assert_zero(not_start_down * (idx_a_down - idx_a - a_increment));
        builder.assert_zero(not_start_down * (idx_b_down - idx_b - AB::F::from_usize(crate::DIMENSION)));

        builder.assert_zero(start_down * (len - AB::F::ONE));
    }
}
