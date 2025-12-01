use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;

use crate::EF;

#[derive(Debug)]
pub struct FullRoundComputation<const WIDTH: usize> {}

impl<const WIDTH: usize> SumcheckComputation<EF> for FullRoundComputation<WIDTH>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
    EF: ExtensionField<PF<EF>>,
{
    type ExtraData = ();

    fn degrees(&self) -> Vec<usize> {
        vec![3]
    }

    #[inline(always)]
    fn eval_base<const STEP: usize>(&self, point: &[PF<EF>], _: &[EF], _: &Self::ExtraData, alpha_powers: &[EF]) -> EF {
        self.my_eval::<PF<EF>>(point, alpha_powers)
    }

    #[inline(always)]
    fn eval_extension<const STEP: usize>(
        &self,
        point: &[EF],
        _: &[EF],
        _: &Self::ExtraData,
        alpha_powers: &[EF],
    ) -> EF {
        self.my_eval::<EF>(point, alpha_powers)
    }

    #[inline(always)]
    fn eval_packed_base<const STEP: usize>(
        &self,
        point: &[PFPacking<EF>],
        _: &[EFPacking<EF>],
        _: &Self::ExtraData,
        alpha_powers: &[EF],
    ) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EFPacking::<EF>::ZERO;
        for i in 0..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i].cube();
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
        let mut res = EFPacking::<EF>::ZERO;
        for i in 0..WIDTH {
            res += point[i].cube() * alpha_powers[i];
        }
        res
    }
}

impl<const WIDTH: usize> FullRoundComputation<WIDTH>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
    EF: ExtensionField<PF<EF>>,
{
    #[inline(always)]
    fn my_eval<NF: ExtensionField<PF<EF>>>(&self, point: &[NF], alpha_powers: &[EF]) -> EF
    where
        EF: ExtensionField<NF>,
    {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EF::ZERO;
        for i in 0..WIDTH {
            res += alpha_powers[i] * point[i].cube();
        }
        res
    }
}
