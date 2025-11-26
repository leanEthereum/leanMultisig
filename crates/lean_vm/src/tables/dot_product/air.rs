use crate::{
    DIMENSION, EF, ExtraDataForBuses, TableT, eval_virtual_bus_column, tables::dot_product::DotProductPrecompile,
};
use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder};

/*
(DIMENSION = 5)

|    Flag   | Len | IndexA | IndexB | IndexRes | ValueA        | ValueB      | Res                | Computation                              |
| --------- | --- | ------ | ------ | -------- | ------------- | ----------- | ------------------ | ---------------------------------------- |
| 1         | 4   | 90     | 211    | 74       | m[90]         | m[211..216] | m[74..79] = r3     | r3 = m[90] x m[211..216] + r2            |
| 0         | 3   | 91     | 216    | 74       | m[91]         | m[216..221] | m[74..79]          | r2 = m[91] x m[216..221] + r1            |
| 0         | 2   | 92     | 221    | 74       | m[92]         | m[221..226] | m[74..79]          | r1 = m[92] x m[221..226] + r0            |
| 0         | 1   | 93     | 226    | 74       | m[93]         | m[226..231] | m[74..79]          | r0 = m[93] x m[226..231]                 |
| 1         | 10  | 1008   | 859    | 325      | m[1008]       | m[859..864] | m[325..330] = r10' | r10' = m[1008] x m[859..864] + r9'       |
| 0         | 9   | 1009   | 864    | 325      | m[1009]       | m[864..869] | m[325..330]        | r9' = m[1009] x m[864..869] + r8'        |
| 0         | 8   | 1010   | 869    | 325      | m[1010]       | m[869..874] | m[325..330]        | r8' = m[1010] x m[869..874] + r7'        |
| 0         | 7   | 1011   | 874    | 325      | m[1011]       | m[874..879] | m[325..330]        | r7' = m[1011] x m[874..879] + r6'        |
| ...       | ... | ...    | ...    | ...      | ...           | ...         | ...                | ...                                      |
*/

// F columns
pub(super) const COL_FLAG: usize = 0;
pub(super) const COL_LEN: usize = 1;
pub(super) const COL_INDEX_A: usize = 2;
pub(super) const COL_INDEX_B: usize = 3;
pub(super) const COL_INDEX_RES: usize = 4;

// EF columns
pub(super) const COL_VALUE_B: usize = 0;
pub(super) const COL_VALUE_RES: usize = 1;
pub(super) const COL_COMPUTATION: usize = 2;

pub(super) const fn dot_product_air_col_value_a(be: bool) -> usize {
    if be { 5 } else { 3 }
}

pub(super) const fn dot_product_air_n_cols_f(be: bool) -> usize {
    if be { 6 } else { 5 }
}

pub(super) const fn dot_product_air_n_cols_ef(be: bool) -> usize {
    if be { 3 } else { 4 }
}

impl<const BE: bool> Air for DotProductPrecompile<BE> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns_f_air(&self) -> usize {
        dot_product_air_n_cols_f(BE)
    }
    fn n_columns_ef_air(&self) -> usize {
        dot_product_air_n_cols_ef(BE)
    }
    fn degree(&self) -> usize {
        3
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
        let value_a = if BE {
            AB::EF::from(up_f[dot_product_air_col_value_a(BE)].clone()) // TODO embdding overhead
        } else {
            up_ef[dot_product_air_col_value_a(BE)].clone()
        };

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
            index_a.clone(),
            index_b.clone(),
            index_res.clone(),
            len.clone(),
        ));

        builder.assert_bool(flag.clone());

        let product_up = value_b * value_a;
        let not_flag_down = AB::F::ONE - flag_down.clone();
        builder.assert_eq_ef(
            computation.clone(),
            product_up.clone() + computation_down * not_flag_down.clone(),
        );
        builder.assert_zero(not_flag_down.clone() * (len.clone() - (len_down + AB::F::ONE)));
        builder.assert_zero(flag_down * (len - AB::F::ONE));
        let index_a_increment = AB::F::from_usize(if BE { 1 } else { DIMENSION });
        builder.assert_zero(not_flag_down.clone() * (index_a - (index_a_down - index_a_increment)));
        builder.assert_zero(not_flag_down * (index_b - (index_b_down - AB::F::from_usize(DIMENSION))));

        builder.assert_zero_ef((computation - res) * flag);
    }
}
