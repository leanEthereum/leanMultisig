use multilinear_toolkit::prelude::*;

use crate::{EF, F};

#[derive(Debug)]
pub struct PartialRoundComputation<const WIDTH: usize>;

impl<const WIDTH: usize> SumcheckComputation<EF> for PartialRoundComputation<WIDTH>
where
    EF: ExtensionField<PF<EF>>,
{
    fn degree(&self) -> usize {
        3
    }

    #[inline(always)]
    fn eval_base(&self, point: &[PF<EF>], alpha_powers: &[EF]) -> EF {
        self.my_eval::<EF, PF<EF>>(point, alpha_powers)
    }

    #[inline(always)]
    fn eval_extension(&self, point: &[EF], alpha_powers: &[EF]) -> EF {
        self.my_eval::<EF, EF>(point, alpha_powers)
    }

    #[inline(always)]
    fn eval_packed_base(&self, point: &[FPacking<F>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EFPacking::<EF>::from(point[0].cube());
        for i in 1..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i];
        }
        res
    }

    #[inline(always)]
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
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
    fn my_eval<EF: ExtensionField<PF<EF>>, NF: ExtensionField<PF<EF>>>(
        &self,
        point: &[NF],
        alpha_powers: &[EF],
    ) -> EF
    where
        EF: ExtensionField<NF>,
    {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EF::from(point[0].cube());
        for i in 1..WIDTH {
            res += alpha_powers[i] * point[i];
        }
        res
    }
}
