use lean_vm::{DIMENSION, EF, TABLE_INDEX_DOT_PRODUCTS};
use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_uni_stark::SymbolicExpression;
use std::{
    any::TypeId,
    mem::{transmute, transmute_copy},
};

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

pub const DOT_PRODUCT_AIR_COL_START_FLAG: usize = 0;
pub const DOT_PRODUCT_AIR_COL_LEN: usize = 1;
pub const DOT_PRODUCT_AIR_COL_INDEX_A: usize = 2;
pub const DOT_PRODUCT_AIR_COL_INDEX_B: usize = 3;
pub const DOT_PRODUCT_AIR_COL_INDEX_RES: usize = 4;
pub const DOT_PRODUCT_AIR_COL_VALUE_A: usize = 5;
pub const DOT_PRODUCT_AIR_COL_VALUE_B: usize = 6;
pub const DOT_PRODUCT_AIR_COL_VALUE_RES: usize = 7;
pub const DOT_PRODUCT_AIR_COL_COMPUTATION: usize = 8;

pub const DOT_PRODUCT_AIR_N_COLUMNS: usize = 9;

#[derive(Debug)]
pub struct DotProductAir<EF> {
    pub global_challenge: EF,
    pub fingerprint_challenge_powers: [EF; 5],
}

impl<EF> SumcheckComputationForAir for DotProductAir<EF> {}

impl<F, EF: Send + Sync> BaseAir<F> for DotProductAir<EF> {
    fn width(&self) -> usize {
        DOT_PRODUCT_AIR_N_COLUMNS
    }
    fn degree(&self) -> usize {
        3
    }
    fn columns_with_shift(&self) -> Vec<usize> {
        vec![
            DOT_PRODUCT_AIR_COL_START_FLAG,
            DOT_PRODUCT_AIR_COL_LEN,
            DOT_PRODUCT_AIR_COL_INDEX_A,
            DOT_PRODUCT_AIR_COL_INDEX_B,
            DOT_PRODUCT_AIR_COL_COMPUTATION,
        ]
    }
}

impl<AB: AirBuilder, EF: ExtensionField<PF<EF>>> Air<AB> for DotProductAir<EF>
where
    AB::Var: 'static,
    AB::Expr: 'static,
    AB::FinalOutput: 'static,
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = &main[..DOT_PRODUCT_AIR_N_COLUMNS];
        let down = &main[DOT_PRODUCT_AIR_N_COLUMNS..];

        let start_flag_up = up[DOT_PRODUCT_AIR_COL_START_FLAG].clone();
        let len_up = up[DOT_PRODUCT_AIR_COL_LEN].clone();
        let index_a_up = up[DOT_PRODUCT_AIR_COL_INDEX_A].clone();
        let index_b_up = up[DOT_PRODUCT_AIR_COL_INDEX_B].clone();
        let index_res_up = up[DOT_PRODUCT_AIR_COL_INDEX_RES].clone();
        let value_a_up = up[DOT_PRODUCT_AIR_COL_VALUE_A].clone();
        let value_b_up = up[DOT_PRODUCT_AIR_COL_VALUE_B].clone();
        let res_up = up[DOT_PRODUCT_AIR_COL_VALUE_RES].clone();
        let computation_up = up[DOT_PRODUCT_AIR_COL_COMPUTATION].clone();

        let start_flag_down = down[0].clone();
        let len_down = down[1].clone();
        let index_a_down = down[2].clone();
        let index_b_down = down[3].clone();
        let computation_down = down[4].clone();

        // TODO we could do most of the following computation in the base field

        builder.add_custom(<DotProductAir<EF> as Air<AB>>::eval_custom(
            self,
            &[
                start_flag_up.clone().into(),
                len_up.clone().into(),
                index_a_up.clone().into(),
                index_b_up.clone().into(),
                index_res_up.clone().into(),
            ],
        ));

        builder.assert_bool(start_flag_down.clone());

        let product_up = value_a_up * value_b_up;
        let not_flag_down = AB::Expr::ONE - start_flag_down.clone();
        builder.assert_eq(
            computation_up.clone(),
            start_flag_down.clone() * product_up.clone()
                + not_flag_down.clone() * (product_up + computation_down),
        );
        builder.assert_zero(not_flag_down.clone() * (len_up.clone() - (len_down + AB::Expr::ONE)));
        builder.assert_zero(start_flag_down * (len_up - AB::Expr::ONE));
        builder.assert_zero(
            not_flag_down.clone() * (index_a_up - (index_a_down - AB::Expr::from_usize(DIMENSION))),
        );
        builder.assert_zero(
            not_flag_down * (index_b_up - (index_b_down - AB::Expr::from_usize(DIMENSION))),
        );

        builder.assert_zero(start_flag_up * (computation_up - res_up));
    }

    fn eval_custom(&self, inputs: &[<AB as AirBuilder>::Expr]) -> <AB as AirBuilder>::FinalOutput {
        let type_id_final_output = TypeId::of::<<AB as AirBuilder>::FinalOutput>();
        let type_id_expr = TypeId::of::<<AB as AirBuilder>::Expr>();
        // let type_id_f = TypeId::of::<PF<EF>>();
        let type_id_ef = TypeId::of::<EF>();
        let type_id_f_packing = TypeId::of::<PFPacking<EF>>();
        let type_id_ef_packing = TypeId::of::<EFPacking<EF>>();

        if type_id_expr == type_id_ef {
            assert_eq!(type_id_final_output, type_id_ef);
            let inputs = unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[EF]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| c * p);
            unsafe { transmute_copy::<EF, <AB as AirBuilder>::FinalOutput>(&res) }
        } else if type_id_expr == type_id_ef_packing {
            assert_eq!(type_id_final_output, type_id_ef_packing);
            let inputs =
                unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[EFPacking<EF>]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| p * c);
            unsafe { transmute_copy::<EFPacking<EF>, <AB as AirBuilder>::FinalOutput>(&res) }
        } else if type_id_expr == type_id_f_packing {
            assert_eq!(type_id_final_output, type_id_ef_packing);
            let inputs =
                unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[PFPacking<EF>]>(inputs) };
            let res = self.gkr_virtual_column_eval(inputs, |p, c| EFPacking::<EF>::from(p) * c);
            unsafe { transmute_copy::<EFPacking<EF>, <AB as AirBuilder>::FinalOutput>(&res) }
        } else {
            assert_eq!(type_id_expr, TypeId::of::<SymbolicExpression<PF<EF>>>());
            unsafe { transmute_copy(&SymbolicExpression::<PF<EF>>::default()) }
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
        ResultF::from_usize(TABLE_INDEX_DOT_PRODUCTS)
            + (mul_point_f_and_ef(point[2], self.fingerprint_challenge_powers[1])
                + mul_point_f_and_ef(point[3], self.fingerprint_challenge_powers[2])
                + mul_point_f_and_ef(point[4], self.fingerprint_challenge_powers[3])
                + mul_point_f_and_ef(point[1], self.fingerprint_challenge_powers[4]))
                * point[0]
            + self.global_challenge
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
