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
fn quintic_mul_air<T: PrimeCharacteristicRing + Clone>(a: &[T; 5], b: &[T; 5]) -> [T; 5] {
    quintic_mul(a, b, |x, y| {
        x[0].clone() * y[0].clone()
            + x[1].clone() * y[1].clone()
            + x[2].clone() * y[2].clone()
            + x[3].clone() * y[3].clone()
            + x[4].clone() * y[4].clone()
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

        let is_be = up[COL_IS_BE].clone();
        let start = up[COL_START].clone();
        let flag_add = up[COL_FLAG_ADD].clone();
        let flag_mul = up[COL_FLAG_MUL].clone();
        let flag_poly_eq = up[COL_FLAG_POLY_EQ].clone();
        let len = up[COL_LEN].clone();
        let idx_a = up[COL_IDX_A].clone();
        let idx_b = up[COL_IDX_B].clone();

        let va: [AB::F; 5] = std::array::from_fn(|k| up[COL_VA + k].clone());
        let vb: [AB::F; 5] = std::array::from_fn(|k| up[COL_VB + k].clone());
        let vres: [AB::F; 5] = std::array::from_fn(|k| up[COL_VRES + k].clone());
        let comp: [AB::F; 5] = std::array::from_fn(|k| up[COL_COMP + k].clone());

        let start_down = down[0].clone(); // COL_START
        let is_be_down = down[1].clone(); // COL_IS_BE
        let len_down = down[2].clone(); // COL_LEN
        let flag_add_down = down[3].clone(); // COL_FLAG_ADD
        let flag_mul_down = down[4].clone(); // COL_FLAG_MUL
        let flag_poly_eq_down = down[5].clone(); // COL_FLAG_POLY_EQ
        let idx_a_down = down[6].clone(); // COL_IDX_A
        let idx_b_down = down[7].clone(); // COL_IDX_B
        let comp_down: [AB::F; 5] = std::array::from_fn(|k| down[8 + k].clone()); // COL_COMP+0..5

        let active = flag_add.clone() + flag_mul.clone() + flag_poly_eq.clone();
        let activation_flag = start.clone() * active.clone();

        let aux = is_be.clone().double()
            + flag_add.clone() * AB::F::from_usize(4)
            + flag_mul.clone() * AB::F::from_usize(8)
            + flag_poly_eq.clone() * AB::F::from_usize(16)
            + len.clone() * AB::F::from_usize(EXT_OP_LEN_MULTIPLIER);

        let idx_r = up[COL_IDX_RES].clone();

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
        let not_start_down = AB::F::ONE - start_down.clone();

        let va_f_or_ef: [AB::F; 5] = std::array::from_fn(|k| {
            if k == 0 {
                va[0].clone()
            } else {
                va[k].clone() * is_ee.clone()
            }
        });

        let comp_tail: [AB::F; 5] = std::array::from_fn(|k| comp_down[k].clone() * not_start_down.clone());

        builder.assert_bool(is_be.clone());
        builder.assert_bool(start.clone());
        builder.assert_bool(flag_add.clone());
        builder.assert_bool(flag_mul.clone());
        builder.assert_bool(flag_poly_eq.clone());

        for k in 0..5 {
            builder.assert_zero(
                (comp[k].clone() - (va_f_or_ef[k].clone() + vb[k].clone() + comp_tail[k].clone())) * flag_add.clone(),
            );
        }

        let va_times_vb = quintic_mul_air(&va_f_or_ef, &vb);

        for k in 0..5 {
            builder.assert_zero((comp[k].clone() - (va_times_vb[k].clone() + comp_tail[k].clone())) * flag_mul.clone());
        }

        let poly_eq_val: [AB::F; 5] = std::array::from_fn(|k| {
            let base = va_times_vb[k].clone().double() - va_f_or_ef[k].clone() - vb[k].clone();
            if k == 0 { base + AB::F::ONE } else { base }
        });
        let comp_down_or_one: [AB::F; 5] = std::array::from_fn(|k| {
            if k == 0 {
                comp_down[0].clone() * not_start_down.clone() + start_down.clone()
            } else {
                comp_down[k].clone() * not_start_down.clone()
            }
        });
        let poly_eq_result = quintic_mul_air(&poly_eq_val, &comp_down_or_one);
        for k in 0..5 {
            builder.assert_zero((comp[k].clone() - poly_eq_result[k].clone()) * flag_poly_eq.clone());
        }

        for k in 0..5 {
            builder.assert_zero((comp[k].clone() - vres[k].clone()) * start.clone());
        }

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
