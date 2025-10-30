use multilinear_toolkit::prelude::*;
use p3_field::ExtensionField;

use crate::{EF, F};

#[derive(Debug)]
pub struct PartialRoundComputation<const WIDTH: usize>;

impl<NF: ExtensionField<F>, const WIDTH: usize> SumcheckComputation<NF, EF>
    for PartialRoundComputation<WIDTH>
where
    EF: ExtensionField<NF>,
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EF::from(point[0].cube());
        for i in 1..WIDTH {
            res += alpha_powers[i] * point[i];
        }
        res
    }
}

impl<const WIDTH: usize> SumcheckComputationPacked<EF> for PartialRoundComputation<WIDTH> {
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_base(&self, point: &[FPacking<F>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = EFPacking::<EF>::from(point[0].cube());
        for i in 1..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i];
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let mut res = point[0].cube();
        for i in 1..WIDTH {
            res += point[i] * alpha_powers[i];
        }
        res
    }
}
