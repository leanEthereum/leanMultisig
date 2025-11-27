use crate::{
    DIMENSION, EF, ExtraDataForBuses, TableT, eval_virtual_bus_column,
    tables::eq_poly_base_ext::EqPolyBaseExtPrecompile,
};
use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder};

// F columns
pub(super) const COL_FLAG: usize = 0;
pub(super) const COL_LEN: usize = 1;
pub(super) const COL_INDEX_A: usize = 2;
pub(super) const COL_INDEX_B: usize = 3;
pub(super) const COL_INDEX_RES: usize = 4;
pub(super) const COL_VALUE_A: usize = 5;

// EF columns
pub(super) const COL_VALUE_B: usize = 0;
pub(super) const COL_VALUE_RES: usize = 1;
pub(super) const COL_COMPUTATION: usize = 2;

pub(super) const N_COLS_F: usize = 6;
pub(super) const N_COLS_EF: usize = 3;

impl Air for EqPolyBaseExtPrecompile {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns_f_air(&self) -> usize {
        N_COLS_F
    }
    fn n_columns_ef_air(&self) -> usize {
        N_COLS_EF
    }
    fn degree(&self) -> usize {
        4
    }
    fn n_constraints(&self) -> usize {
        8
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![COL_FLAG, COL_LEN, COL_INDEX_A, COL_INDEX_B]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![COL_COMPUTATION]
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up_f = builder.up_f();
        let up_ef = builder.up_ef();
        let down_f = builder.down_f();
        let down_ef = builder.down_ef();

        let flag = up_f[COL_FLAG].clone();
        let len = up_f[COL_LEN].clone();
        let index_a = up_f[COL_INDEX_A].clone();
        let index_b = up_f[COL_INDEX_B].clone();
        let index_res = up_f[COL_INDEX_RES].clone();
        let value_a = up_f[COL_VALUE_A].clone();

        let value_b = up_ef[COL_VALUE_B].clone();
        let res = up_ef[COL_VALUE_RES].clone();
        let computation = up_ef[COL_COMPUTATION].clone();

        let flag_down = down_f[0].clone();
        let len_down = down_f[1].clone();
        let index_a_down = down_f[2].clone();
        let index_b_down = down_f[3].clone();

        let computation_down = down_ef[0].clone();

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            AB::F::from_usize(self.identifier().index()),
            flag.clone(),
            &[index_a.clone(),
            index_b.clone(),
            index_res.clone(),
            len.clone()],
        ));

        builder.assert_bool(flag.clone());

        let product_up =
            value_b.clone() * value_a.clone() + (AB::EF::ONE - value_b.clone()) * (AB::F::ONE - value_a.clone());
        let not_flag_down = AB::F::ONE - flag_down.clone();
        builder.assert_eq_ef(
            computation.clone(),
            product_up.clone() * (computation_down * not_flag_down.clone() + flag_down.clone()),
        );
        builder.assert_zero(not_flag_down.clone() * (len.clone() - (len_down + AB::F::ONE)));
        builder.assert_zero(flag_down * (len - AB::F::ONE));
        let index_a_increment = AB::F::ONE;
        builder.assert_zero(not_flag_down.clone() * (index_a - (index_a_down - index_a_increment)));
        builder.assert_zero(not_flag_down * (index_b - (index_b_down - AB::F::from_usize(DIMENSION))));

        builder.assert_zero_ef((computation - res) * flag);
    }
}
