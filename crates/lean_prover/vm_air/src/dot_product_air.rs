use std::{any::TypeId, mem::transmute};

use lean_vm::{DIMENSION, EF, TABLE_INDEX_DOT_PRODUCTS};
use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder};
use std::mem::transmute_copy;

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

#[derive(Debug)]
pub struct DotProductAir<EF> {
    // GKR quotient challenges
    pub global_challenge: EF,
    pub fingerprint_challenge_powers: [EF; 5],
    pub dot_product_bus_beta: EF,
}

impl<EF: ExtensionField<PF<EF>>> Air for DotProductAir<EF> {
    fn n_columns_f() -> usize {
        DOT_PRODUCT_AIR_N_COLUMNS_F
    }
    fn n_columns_ef() -> usize {
        DOT_PRODUCT_AIR_N_COLUMNS_EF
    }
    fn degree() -> usize {
        3
    }
    fn n_constraints() -> usize {
        8
    }
    fn down_column_indexes() -> Vec<usize> {
        vec![
            DOT_PRODUCT_AIR_COL_START_FLAG,
            DOT_PRODUCT_AIR_COL_LEN,
            DOT_PRODUCT_AIR_COL_INDEX_A,
            DOT_PRODUCT_AIR_COL_INDEX_B,
            DOT_PRODUCT_AIR_N_COLUMNS_F + DOT_PRODUCT_AIR_COL_COMPUTATION,
        ]
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB) {
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

        builder.eval_custom(self.eval_custom::<AB>(&[
            start_flag_up.clone(),
            index_a_up.clone(),
            index_b_up.clone(),
            index_res_up.clone(),
            len_up.clone(),
        ]));

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

    fn eval_custom<AB: AirBuilder>(
        &self,
        inputs: &[<AB as AirBuilder>::F],
    ) -> <AB as AirBuilder>::EF {
        let type_id_final_output = TypeId::of::<<AB as AirBuilder>::EF>();
        let type_id_expr = TypeId::of::<<AB as AirBuilder>::F>();
        // let type_id_f = TypeId::of::<PF<EF>>();
        let type_id_ef = TypeId::of::<EF>();
        let type_id_f_packing = TypeId::of::<PFPacking<EF>>();
        let type_id_ef_packing = TypeId::of::<EFPacking<EF>>();

        if type_id_expr == type_id_ef {
            assert_eq!(type_id_final_output, type_id_ef);
            let inputs = unsafe { transmute::<&[<AB as AirBuilder>::F], &[EF]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| c * p);
            unsafe { transmute_copy::<EF, <AB as AirBuilder>::EF>(&res) }
        } else if type_id_expr == type_id_ef_packing {
            assert_eq!(type_id_final_output, type_id_ef_packing);
            let inputs = unsafe { transmute::<&[<AB as AirBuilder>::F], &[EFPacking<EF>]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| p * c);
            unsafe { transmute_copy::<EFPacking<EF>, <AB as AirBuilder>::EF>(&res) }
        } else if type_id_expr == type_id_f_packing {
            assert_eq!(type_id_final_output, type_id_ef_packing);
            let inputs = unsafe { transmute::<&[<AB as AirBuilder>::F], &[PFPacking<EF>]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| EFPacking::<EF>::from(p) * c);
            unsafe { transmute_copy::<EFPacking<EF>, <AB as AirBuilder>::EF>(&res) }
        } else {
            unreachable!()
        }
    }
}

impl<EF: Copy> DotProductAir<EF> {
    fn gkr_virtual_column_eval<
        PointF: PrimeCharacteristicRing + Copy,
        ResultF: Algebra<EF> + Algebra<PointF> + Copy,
    >(
        &self,
        point: &[PointF],
        mul_point_f_and_ef: impl Fn(PointF, EF) -> ResultF,
    ) -> ResultF {
        let start_flag_up = point[0];
        let index_a = point[1];
        let index_b = point[2];
        let index_res = point[3];
        let len = point[4];

        let data = mul_point_f_and_ef(index_a, self.fingerprint_challenge_powers[1])
            + mul_point_f_and_ef(index_b, self.fingerprint_challenge_powers[2])
            + mul_point_f_and_ef(index_res, self.fingerprint_challenge_powers[3])
            + mul_point_f_and_ef(len, self.fingerprint_challenge_powers[4]);

        ((data + PointF::from_usize(TABLE_INDEX_DOT_PRODUCTS)) + self.global_challenge)
            * self.dot_product_bus_beta
            + start_flag_up
    }
}

pub fn dot_product_air_padding_row() -> Vec<EF> {
    // only the shifted columns
    vec![
        EF::ONE,  // StartFlag
        EF::ONE,  // Len
        EF::ZERO, // IndexA
        EF::ZERO, // IndexB
        EF::ZERO, // Computation
    ]
}
