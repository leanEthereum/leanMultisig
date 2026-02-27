use backend::*;

use crate::EF;

#[derive(Debug)]
pub struct FullRoundComputation<const WIDTH: usize> {}

impl<const WIDTH: usize> SumcheckComputation<EF> for FullRoundComputation<WIDTH>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
    EF: ExtensionField<PF<EF>>,
{
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        3
    }

    #[inline(always)]
    fn eval_base(&self, point: &[PF<EF>], alpha_powers: &Self::ExtraData) -> EF {
        self.my_eval::<PF<EF>>(point, alpha_powers)
    }

    #[inline(always)]
    fn eval_extension(&self, point: &[EF], alpha_powers: &Self::ExtraData) -> EF {
        self.my_eval::<EF>(point, alpha_powers)
    }

    #[inline(always)]
    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &Self::ExtraData) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EFPacking::<EF>::ZERO;
        for i in 0..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i].cube();
        }
        res
    }

    #[inline(always)]
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &Self::ExtraData) -> EFPacking<EF> {
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
