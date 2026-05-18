use crate::{
    EF, EXT_OP_FLAG_ADD, EXT_OP_FLAG_IS_BE, EXT_OP_FLAG_MUL, EXT_OP_FLAG_POLY_EQ, ExtraDataForBuses, TableT,
    eval_virtual_bus_column,
    tables::extension_op::{EXT_OP_LEN_MULTIPLIER, ExtensionOpPrecompile},
};
use backend::*;

// Shift columns first, in positions 0..13 (see `n_shift_columns` below).
// Flat-only columns follow.
pub(super) const COL_IS_BE: usize = 0;
pub(super) const COL_START: usize = 1;
pub(super) const COL_LEN: usize = 2;
pub(super) const COL_FLAG_ADD: usize = 3;
pub(super) const COL_FLAG_MUL: usize = 4;
pub(super) const COL_FLAG_POLY_EQ: usize = 5;
pub(super) const COL_IDX_A: usize = 6;
pub(super) const COL_IDX_B: usize = 7;
/// computation coordinates (5 columns).
pub(super) const COL_COMP: usize = 8;
// --- flat-only columns ---
pub(super) const COL_IDX_RES: usize = 13;
/// value_a coordinates (5 columns).
pub(super) const COL_VA: usize = 14;
/// value_b coordinates (5 columns).
pub(super) const COL_VB: usize = 19;
/// result coordinates (5 columns).
pub(super) const COL_VRES: usize = 24;

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
    fn n_air_constraints(&self) -> usize {
        33
    }
    fn n_shift_columns(&self) -> usize {
        COL_COMP + 5
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let flat = builder.flat();
        let shift = builder.shift();

        let is_be = flat[COL_IS_BE];
        let start = flat[COL_START];
        let flag_add = flat[COL_FLAG_ADD];
        let flag_mul = flat[COL_FLAG_MUL];
        let flag_poly_eq = flat[COL_FLAG_POLY_EQ];
        let len = flat[COL_LEN];
        let idx_a = flat[COL_IDX_A];
        let idx_b = flat[COL_IDX_B];

        let va: [AB::IF; 5] = std::array::from_fn(|k| flat[COL_VA + k]);
        let vb: [AB::IF; 5] = std::array::from_fn(|k| flat[COL_VB + k]);
        let vres: [AB::IF; 5] = std::array::from_fn(|k| flat[COL_VRES + k]);
        let comp: [AB::IF; 5] = std::array::from_fn(|k| flat[COL_COMP + k]);

        // Shift columns map 1:1 onto the first 13 columns by convention.
        let is_be_shift = shift[COL_IS_BE];
        let start_shift = shift[COL_START];
        let len_shift = shift[COL_LEN];
        let flag_add_shift = shift[COL_FLAG_ADD];
        let flag_mul_shift = shift[COL_FLAG_MUL];
        let flag_poly_eq_shift = shift[COL_FLAG_POLY_EQ];
        let idx_a_shift = shift[COL_IDX_A];
        let idx_b_shift = shift[COL_IDX_B];
        let comp_shift: [AB::IF; 5] = std::array::from_fn(|k| shift[COL_COMP + k]);

        let active = flag_add + flag_mul + flag_poly_eq;
        let activation_flag = start * active;

        let aux = is_be * AB::F::from_usize(EXT_OP_FLAG_IS_BE)
            + flag_add * AB::F::from_usize(EXT_OP_FLAG_ADD)
            + flag_mul * AB::F::from_usize(EXT_OP_FLAG_MUL)
            + flag_poly_eq * AB::F::from_usize(EXT_OP_FLAG_POLY_EQ)
            + len * AB::F::from_usize(EXT_OP_LEN_MULTIPLIER);

        let idx_r = flat[COL_IDX_RES];

        if BUS {
            builder.assert_zero_ef(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                activation_flag,
                &[aux, idx_a, idx_b, idx_r],
            ));
            for col in self.logup_claim_columns() {
                let val = builder.flat()[col];
                builder.assert_zero(val);
            }
        } else {
            builder.declare_values(&[activation_flag]);
            builder.declare_values(&[aux, idx_a, idx_b, idx_r]);
        }

        let is_ee = -(is_be - AB::F::ONE);
        let not_start_shift = -(start_shift - AB::F::ONE);

        let va_f_or_ef: [AB::IF; 5] = std::array::from_fn(|k| if k == 0 { va[0] } else { va[k] * is_ee });

        let comp_tail: [AB::IF; 5] = std::array::from_fn(|k| comp_shift[k] * not_start_shift);

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

        let poly_eq_val: [AB::IF; 5] = std::array::from_fn(|k| {
            let base = va_times_vb[k].double() - va_f_or_ef[k] - vb[k];
            if k == 0 { base + AB::F::ONE } else { base }
        });
        let comp_shift_or_one: [AB::IF; 5] = std::array::from_fn(|k| {
            if k == 0 {
                comp_shift[0] * not_start_shift + start_shift
            } else {
                comp_shift[k] * not_start_shift
            }
        });
        let poly_eq_result = quintic_mul_air(&poly_eq_val, &comp_shift_or_one);
        for k in 0..5 {
            builder.assert_zero((comp[k] - poly_eq_result[k]) * flag_poly_eq);
        }

        for k in 0..5 {
            builder.assert_zero((comp[k] - vres[k]) * start);
        }

        builder.assert_zero(not_start_shift * (len - len_shift - AB::F::ONE));
        builder.assert_zero(not_start_shift * (is_be - is_be_shift));
        builder.assert_zero(not_start_shift * (flag_add - flag_add_shift));
        builder.assert_zero(not_start_shift * (flag_mul - flag_mul_shift));
        builder.assert_zero(not_start_shift * (flag_poly_eq - flag_poly_eq_shift));
        let a_increment = is_be + is_ee * AB::F::from_usize(crate::DIMENSION);
        builder.assert_zero(not_start_shift * (idx_a_shift - idx_a - a_increment));
        builder.assert_zero(not_start_shift * (idx_b_shift - idx_b - AB::F::from_usize(crate::DIMENSION)));

        builder.assert_zero(start_shift * (len - AB::F::ONE));
    }
}
