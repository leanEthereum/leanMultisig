use crate::{
    EF, EXT_OP_FLAG_ADD, EXT_OP_FLAG_IS_BE, EXT_OP_FLAG_MEMCOPY_4, EXT_OP_FLAG_MUL, EXT_OP_FLAG_POLY_EQ,
    ExtraDataForBuses, eval_virtual_bus_column,
    tables::extension_op::{EXT_OP_LEN_MULTIPLIER, ExtensionOpPrecompile, MEMCOPY_4_STRIDE_OUT, MEMCOPY4_STRIDES},
};
use backend::*;

// AIR columns (30 total)
pub(super) const COL_IS_BE: usize = 0;
pub(super) const COL_START: usize = 1;
pub(super) const COL_FLAG_ADD: usize = 2;
pub(super) const COL_FLAG_MUL: usize = 3;
pub(super) const COL_FLAG_POLY_EQ: usize = 4;
pub(super) const COL_FLAG_MEMCOPY_4: usize = 5;
pub(super) const COL_LEN: usize = 6;
pub(super) const COL_IDX_A: usize = 7;
pub(super) const COL_IDX_B: usize = 8;
pub(super) const COL_IDX_RES: usize = 9;

/// value_a coordinates (5 columns)
pub(super) const COL_VA: usize = 10;
/// value_b coordinates (5 columns)
pub(super) const COL_VB: usize = 15;
/// result coordinates (5 columns).
pub(super) const COL_VRES: usize = 20;
/// computation coordinates (5 columns)
pub(super) const COL_COMP: usize = 25;

// Virtual columns (not explicitely in AIR)
pub(super) const COL_ACTIVATION_FLAG: usize = 30;
pub(super) const COL_AUX_EXTENSION_OP: usize = 31;

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
        30
    }
    fn degree_air(&self) -> usize {
        6
    }
    fn n_constraints(&self) -> usize {
        // 33 original constraints + 7 memcopy_4-specific constraints:
        //   1 bool(flag_memcopy_4)
        //   1 mutual exclusivity with add/mul/poly_eq
        //   1 flag_memcopy_4 constancy across non-start rows
        //   4 copy equality va[k] == vb[k] (only the first 4 — the 5th is don't-care)
        // The two stride constraints (idx_a_down, idx_b_down) are generalized in place,
        // not added separately.
        33 + 7
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![
            COL_START,          // down[0]
            COL_IS_BE,          // down[1]
            COL_LEN,            // down[2]
            COL_FLAG_ADD,       // down[3]
            COL_FLAG_MUL,       // down[4]
            COL_FLAG_POLY_EQ,   // down[5]
            COL_FLAG_MEMCOPY_4, // down[6]
            COL_IDX_A,          // down[7]
            COL_IDX_B,          // down[8]
            COL_COMP,           // down[9]
            COL_COMP + 1,       // down[10]
            COL_COMP + 2,       // down[11]
            COL_COMP + 3,       // down[12]
            COL_COMP + 4,       // down[13]
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
        let flag_memcopy_4 = up[COL_FLAG_MEMCOPY_4];
        let len = up[COL_LEN];
        let idx_a = up[COL_IDX_A];
        let idx_b = up[COL_IDX_B];

        let va: [AB::IF; 5] = std::array::from_fn(|k| up[COL_VA + k]);
        let vb: [AB::IF; 5] = std::array::from_fn(|k| up[COL_VB + k]);
        let vres: [AB::IF; 5] = std::array::from_fn(|k| up[COL_VRES + k]);
        let comp: [AB::IF; 5] = std::array::from_fn(|k| up[COL_COMP + k]);

        let start_down = down[0]; // COL_START
        let is_be_down = down[1]; // COL_IS_BE
        let len_down = down[2]; // COL_LEN
        let flag_add_down = down[3]; // COL_FLAG_ADD
        let flag_mul_down = down[4]; // COL_FLAG_MUL
        let flag_poly_eq_down = down[5]; // COL_FLAG_POLY_EQ
        let flag_memcopy_4_down = down[6]; // COL_FLAG_MEMCOPY_4
        let idx_a_down = down[7]; // COL_IDX_A
        let idx_b_down = down[8]; // COL_IDX_B
        let comp_down: [AB::IF; 5] = std::array::from_fn(|k| down[9 + k]); // COL_COMP+0..5

        // A row is "active" on the bus when it's the start row of a valid call.
        let active = flag_add + flag_mul + flag_poly_eq + flag_memcopy_4;
        let activation_flag = start * active;

        // Virtual aux column: reconstructed from the individual flag/len columns.
        // Must match the packed PRECOMPILE_DATA value pushed by the execution table.
        // For memcopy_4, `is_be` encodes the stride_in variant (0 or 4) — see below.
        let aux = is_be * AB::F::from_usize(EXT_OP_FLAG_IS_BE)
            + flag_add * AB::F::from_usize(EXT_OP_FLAG_ADD)
            + flag_mul * AB::F::from_usize(EXT_OP_FLAG_MUL)
            + flag_poly_eq * AB::F::from_usize(EXT_OP_FLAG_POLY_EQ)
            + flag_memcopy_4 * AB::F::from_usize(EXT_OP_FLAG_MEMCOPY_4)
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

        let is_ee = -(is_be - AB::F::ONE);
        let not_start_down = -(start_down - AB::F::ONE);

        let va_f_or_ef: [AB::IF; 5] = std::array::from_fn(|k| if k == 0 { va[0] } else { va[k] * is_ee });

        let comp_tail: [AB::IF; 5] = std::array::from_fn(|k| comp_down[k] * not_start_down);

        builder.assert_bool(is_be);
        builder.assert_bool(start);
        builder.assert_bool(flag_add);
        builder.assert_bool(flag_mul);
        builder.assert_bool(flag_poly_eq);
        builder.assert_bool(flag_memcopy_4);

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
        let comp_down_or_one: [AB::IF; 5] = std::array::from_fn(|k| {
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

        // Memcopy_4 copy equality: va[k] == vb[k] for the first 4 coordinates.
        // The 5th is don't-care (the "4" in memcopy_4).
        for k in 0..4 {
            builder.assert_zero(flag_memcopy_4 * (va[k] - vb[k]));
        }

        for k in 0..5 {
            builder.assert_zero((comp[k] - vres[k]) * start);
        }

        builder.assert_zero(not_start_down * (len - len_down - AB::F::ONE));
        builder.assert_zero(not_start_down * (is_be - is_be_down));
        builder.assert_zero(not_start_down * (flag_add - flag_add_down));
        builder.assert_zero(not_start_down * (flag_mul - flag_mul_down));
        builder.assert_zero(not_start_down * (flag_poly_eq - flag_poly_eq_down));
        builder.assert_zero(not_start_down * (flag_memcopy_4 - flag_memcopy_4_down));
        // Address stride constraints:
        //   - Existing (non-memcopy_4) modes: idx_a advances by `is_be + is_ee * DIMENSION`
        //     (= 1 for BE, = DIMENSION for EE), idx_b by `DIMENSION`.
        //   - memcopy_4: idx_a advances by `MEMCOPY4_STRIDES[1] * is_be` (STRIDES[0] or STRIDES[1]),
        //     idx_b by MEMCOPY_4_STRIDE_OUT. The variant column selects the stride.
        //     (Works because MEMCOPY4_STRIDES[0] == 0; generalize if that changes.)
        let one_minus_memcopy_4 = -(flag_memcopy_4 - AB::F::ONE);
        let default_a_incr = is_be + is_ee * AB::F::from_usize(crate::DIMENSION);
        let a_increment =
            flag_memcopy_4 * is_be * AB::F::from_usize(MEMCOPY4_STRIDES[1]) + one_minus_memcopy_4 * default_a_incr;
        let b_increment = flag_memcopy_4 * AB::F::from_usize(MEMCOPY_4_STRIDE_OUT)
            + one_minus_memcopy_4 * AB::F::from_usize(crate::DIMENSION);
        builder.assert_zero(not_start_down * (idx_a_down - idx_a - a_increment));
        builder.assert_zero(not_start_down * (idx_b_down - idx_b - b_increment));

        builder.assert_zero(start_down * (len - AB::F::ONE));
    }
}
