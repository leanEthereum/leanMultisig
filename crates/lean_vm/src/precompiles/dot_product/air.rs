use crate::{DIMENSION, EF, ExtraDataForBuses, Table, precompiles::dot_product::DotProductPrecompile};
use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder};

/*
(DIMENSION = 5)

| StartFlag | Len | IndexA | IndexB | IndexRes | ValueA        | ValueB      | Res                | Computation                              |
| --------- | --- | ------ | ------ | -------- | ------------- | ----------- | ------------------ | ---------------------------------------- |
| 1         | 4   | 90     | 211    | 74       | m[90..95]     | m[211..216] | m[74..79] = r3     | r3 = m[90..95] x m[211..216] + r2        |
| 0         | 3   | 95     | 216    | 74       | m[95..100]    | m[216..221] | m[74..79]          | r2 = m[95..100] x m[216..221] + r1       |
| 0         | 2   | 100    | 221    | 74       | m[100..105]   | m[221..226] | m[74..79]          | r1 = m[100..105] x m[221..226] + r0      |
| 0         | 1   | 105    | 226    | 74       | m[105..110]   | m[226..231] | m[74..79]          | r0 = m[105..110] x m[226..231]           |
| 1         | 10  | 1008   | 859    | 325      | m[1008..1013] | m[859..864] | m[325..330] = r10' | r10' = m[1008..1013] x m[859..864] + r9' |
| 0         | 9   | 1013   | 864    | 325      | m[1013..1018] | m[864..869] | m[325..330]        | r9' = m[1013..1018] x m[864..869] + r8'  |
| 0         | 8   | 1018   | 869    | 325      | m[1018..1023] | m[869..874] | m[325..330]        | r8' = m[1018..1023] x m[869..874] + r7'  |
| 0         | 7   | 1023   | 874    | 325      | m[1023..1028] | m[874..879] | m[325..330]        | r7' = m[1023..1028] x m[874..879] + r6'  |
| ...       | ... | ...    | ...    | ...      | ...           | ...         | ...                | ...                                      |
*/

// F columns
pub const DOT_PRODUCT_AIR_COL_START_FLAG: usize = 0;
pub const DOT_PRODUCT_AIR_COL_LEN: usize = 1;
pub const DOT_PRODUCT_AIR_COL_INDEX_A: usize = 2;
pub const DOT_PRODUCT_AIR_COL_INDEX_B: usize = 3;
pub const DOT_PRODUCT_AIR_COL_INDEX_RES: usize = 4;
// EF columns
pub const DOT_PRODUCT_AIR_COL_VALUE_A: usize = 0;
pub const DOT_PRODUCT_AIR_COL_VALUE_B: usize = 1;
pub const DOT_PRODUCT_AIR_COL_VALUE_RES: usize = 2;
pub const DOT_PRODUCT_AIR_COL_COMPUTATION: usize = 3;

pub const DOT_PRODUCT_AIR_N_COLUMNS_F: usize = 5;
pub const DOT_PRODUCT_AIR_N_COLUMNS_EF: usize = 4;
pub const DOT_PRODUCT_AIR_N_COLUMNS_TOTAL: usize =
    DOT_PRODUCT_AIR_N_COLUMNS_F + DOT_PRODUCT_AIR_N_COLUMNS_EF;

impl Air for DotProductPrecompile {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns_f(&self) -> usize {
        DOT_PRODUCT_AIR_N_COLUMNS_F
    }
    fn n_columns_ef(&self) -> usize {
        DOT_PRODUCT_AIR_N_COLUMNS_EF
    }
    fn degree(&self) -> usize {
        3
    }
    fn n_constraints(&self) -> usize {
        8
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![
            DOT_PRODUCT_AIR_COL_START_FLAG,
            DOT_PRODUCT_AIR_COL_LEN,
            DOT_PRODUCT_AIR_COL_INDEX_A,
            DOT_PRODUCT_AIR_COL_INDEX_B,
            DOT_PRODUCT_AIR_N_COLUMNS_F + DOT_PRODUCT_AIR_COL_COMPUTATION,
        ]
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up_f = builder.up_f();
        let up_ef = builder.up_ef();
        let down_f = builder.down_f();
        let down_ef = builder.down_ef();

        let start_flag_up = up_f[DOT_PRODUCT_AIR_COL_START_FLAG].clone();
        let len_up = up_f[DOT_PRODUCT_AIR_COL_LEN].clone();
        let index_a_up = up_f[DOT_PRODUCT_AIR_COL_INDEX_A].clone();
        let index_b_up = up_f[DOT_PRODUCT_AIR_COL_INDEX_B].clone();
        let index_res_up = up_f[DOT_PRODUCT_AIR_COL_INDEX_RES].clone();

        let value_a_up = up_ef[DOT_PRODUCT_AIR_COL_VALUE_A].clone();
        let value_b_up = up_ef[DOT_PRODUCT_AIR_COL_VALUE_B].clone();
        let res_up = up_ef[DOT_PRODUCT_AIR_COL_VALUE_RES].clone();
        let computation_up = up_ef[DOT_PRODUCT_AIR_COL_COMPUTATION].clone();

        let start_flag_down = down_f[0].clone();
        let len_down = down_f[1].clone();
        let index_a_down = down_f[2].clone();
        let index_b_down = down_f[3].clone();

        let computation_down = down_ef[0].clone();

        // TODO we could do most of the following computation in the base field

        builder.eval_virtual_column(eval_virtual_col::<AB, EF>(
            extra_data,
            start_flag_up.clone(),
            index_a_up.clone(),
            index_b_up.clone(),
            index_res_up.clone(),
            len_up.clone(),
        ));

        builder.assert_bool(start_flag_down.clone());

        let product_up = value_a_up * value_b_up;
        let not_flag_down = AB::F::ONE - start_flag_down.clone();
        builder.assert_eq_ef(
            computation_up.clone(),
            product_up.clone() * start_flag_down.clone()
                + (product_up + computation_down) * not_flag_down.clone(),
        );
        builder.assert_zero(not_flag_down.clone() * (len_up.clone() - (len_down + AB::F::ONE)));
        builder.assert_zero(start_flag_down * (len_up - AB::F::ONE));
        builder.assert_zero(
            not_flag_down.clone() * (index_a_up - (index_a_down - AB::F::from_usize(DIMENSION))),
        );
        builder.assert_zero(
            not_flag_down * (index_b_up - (index_b_down - AB::F::from_usize(DIMENSION))),
        );

        builder.assert_zero_ef((computation_up - res_up) * start_flag_up);
    }
}

fn eval_virtual_col<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    extra_data: &ExtraDataForBuses<EF>,
    start_flag_up: AB::F,
    index_a: AB::F,
    index_b: AB::F,
    index_res: AB::F,
    len: AB::F,
) -> AB::EF {
    let (bus_challenge, fingerprint_challenge_powers, dot_product_bus_beta) =
        extra_data.transmute_bus_data::<AB::EF>();

    let data = fingerprint_challenge_powers[1].clone() * index_a
        + fingerprint_challenge_powers[2].clone() * index_b
        + fingerprint_challenge_powers[3].clone() * index_res
        + fingerprint_challenge_powers[4].clone() * len;

    ((data + Table::dot_product().embed::<AB::F>()) + bus_challenge) * dot_product_bus_beta
        + start_flag_up
}
