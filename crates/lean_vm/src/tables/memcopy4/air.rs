use crate::{
    EF, ExtraDataForBuses, eval_virtual_bus_column,
    tables::memcopy4::{
        MEMCOPY4_DOMAIN_SEP, MEMCOPY4_LEN_MULT, MEMCOPY4_STRIDE_OUT, MEMCOPY4_STRIDES, Memcopy4Precompile,
    },
};
use backend::*;

// AIR columns (10)
pub(super) const COL_MC4_ACTIVATION: usize = 0;
pub(super) const COL_START: usize = 1;
pub(super) const COL_STRIDE_IN_FLAG: usize = 2;
pub(super) const COL_LEN: usize = 3;
pub(super) const COL_ADDR_IN: usize = 4;
pub(super) const COL_ADDR_OUT: usize = 5;
/// 4 data columns (the values at addr_in, validated by memory lookup).
pub(super) const COL_DATA: usize = 6;

// Non-AIR column (committed for bus)
pub(super) const COL_MC4_AUX: usize = 10;

impl<const BUS: bool> Air for Memcopy4Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        10
    }
    fn degree_air(&self) -> usize {
        3
    }
    fn n_constraints(&self) -> usize {
        9
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![
            COL_START,          // down[0]
            COL_STRIDE_IN_FLAG, // down[1]
            COL_LEN,            // down[2]
            COL_ADDR_IN,        // down[3]
            COL_ADDR_OUT,       // down[4]
        ]
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up();
        let down = builder.down();

        let activation_flag = up[COL_MC4_ACTIVATION];
        let start = up[COL_START];
        let stride_in_flag = up[COL_STRIDE_IN_FLAG];
        let len = up[COL_LEN];
        let addr_in = up[COL_ADDR_IN];
        let addr_out = up[COL_ADDR_OUT];

        let start_down = down[0];
        let stride_in_flag_down = down[1];
        let len_down = down[2];
        let addr_in_down = down[3];
        let addr_out_down = down[4];

        let aux = stride_in_flag + len * AB::F::from_usize(MEMCOPY4_LEN_MULT) + AB::IF::from_usize(MEMCOPY4_DOMAIN_SEP);

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                activation_flag,
                &[aux, addr_in, addr_out, addr_in],
            ));
        } else {
            builder.declare_values(&[activation_flag]);
            builder.declare_values(&[aux, addr_in, addr_out, addr_in]);
        }

        let not_start_down = -(start_down - AB::F::ONE);

        // 1-4. Boolean flags and activation constraint
        builder.assert_bool(activation_flag);
        builder.assert_zero(activation_flag * (-(start - AB::F::ONE))); // activation → start
        builder.assert_bool(start);
        builder.assert_bool(stride_in_flag);

        // 5. Stride flag constancy within a group
        builder.assert_zero(not_start_down * (stride_in_flag - stride_in_flag_down));

        // 6. Len countdown
        builder.assert_zero(not_start_down * (len - len_down - AB::F::ONE));

        // 7. Last row of group: len = 1 when next row is start
        builder.assert_zero(start_down * (len - AB::F::ONE));

        // 8. addr_in stride: flag=1 → STRIDES[0], flag=0 → STRIDES[1]
        //    Since STRIDES[0]=0: stride = (1 - flag) * STRIDES[1]
        let stride_in = (-(stride_in_flag - AB::F::ONE)) * AB::F::from_usize(MEMCOPY4_STRIDES[1]);
        builder.assert_zero(not_start_down * (addr_in_down - addr_in - stride_in));

        // 9. addr_out stride (hardcoded)
        builder.assert_zero(not_start_down * (addr_out_down - addr_out - AB::F::from_usize(MEMCOPY4_STRIDE_OUT)));
    }
}
