use multilinear_toolkit::prelude::*;

use crate::{EF, F};

#[derive(Debug)]
pub struct PartialRoundComputation<const WIDTH: usize>;

impl<const WIDTH: usize> SumcheckComputation<EF> for PartialRoundComputation<WIDTH>
where
    EF: ExtensionField<PF<EF>>,
{
    type ExtraData = ();

    fn degrees(&self) -> Vec<usize> {
        vec![3]
    }

    #[inline(always)]
    fn eval_base<const STEP: usize>(&self, point: &[PF<EF>], _: &[EF], _: &Self::ExtraData, alpha_powers: &[EF]) -> EF {
        self.my_eval::<EF, PF<EF>>(point, alpha_powers)
    }

    #[inline(always)]
    fn eval_extension<const STEP: usize>(
        &self,
        point: &[EF],
        _: &[EF],
        _: &Self::ExtraData,
        alpha_powers: &[EF],
    ) -> EF {
        self.my_eval::<EF, EF>(point, alpha_powers)
    }

    #[inline(always)]
    fn eval_packed_base<const STEP: usize>(
        &self,
        point: &[FPacking<F>],
        _: &[EFPacking<EF>],
        _: &Self::ExtraData,
        alpha_powers: &[EF],
    ) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EFPacking::<EF>::from(point[0].cube());
        for i in 1..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i];
        }
        res
    }

    #[inline(always)]
    fn eval_packed_extension<const STEP: usize>(
        &self,
        point: &[EFPacking<EF>],
        _: &[EFPacking<EF>],
        _: &Self::ExtraData,
        alpha_powers: &[EF],
    ) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = point[0].cube();
        for i in 1..WIDTH {
            res += point[i] * alpha_powers[i];
        }
        res
    }
}

impl<const WIDTH: usize> PartialRoundComputation<WIDTH>
where
    EF: ExtensionField<PF<EF>>,
{
    #[inline(always)]
    fn my_eval<EF: ExtensionField<PF<EF>> + ExtensionField<NF>, NF: ExtensionField<PF<EF>>>(
        &self,
        point: &[NF],
        alpha_powers: &[EF],
    ) -> EF {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EF::from(point[0].cube());
        for i in 1..WIDTH {
            res += alpha_powers[i] * point[i];
        }
        res
    }
}
