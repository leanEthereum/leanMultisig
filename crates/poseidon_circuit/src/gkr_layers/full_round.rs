use multilinear_toolkit::prelude::*;
use p3_field::ExtensionField;
use p3_koala_bear::{KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;

use crate::{EF, F};

#[derive(Debug)]
pub struct FullRoundComputation<const WIDTH: usize> {}

impl<NF: ExtensionField<F>, const WIDTH: usize> SumcheckComputation<NF, EF>
    for FullRoundComputation<WIDTH>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
    EF: ExtensionField<NF>,
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EF::ZERO;
        for i in 0..WIDTH {
            res += alpha_powers[i] * point[i].cube();
        }
        res
    }
}

impl<const WIDTH: usize> SumcheckComputationPacked<EF> for FullRoundComputation<WIDTH>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EFPacking::<EF>::ZERO;
        for i in 0..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i].cube();
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EFPacking::<EF>::ZERO;
        for i in 0..WIDTH {
            res += point[i].cube() * alpha_powers[i];
        }
        res
    }
}
