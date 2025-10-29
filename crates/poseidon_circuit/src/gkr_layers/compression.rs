
use multilinear_toolkit::prelude::*;
use p3_field::ExtensionField;

use crate::{EF, F};

#[derive(Debug)]
pub struct CompressionComputation<const WIDTH: usize> {
    pub compressed_output: usize,
}

impl<NF: ExtensionField<F>, const WIDTH: usize> SumcheckComputation<NF, EF>
    for CompressionComputation<WIDTH>
where
    EF: ExtensionField<NF>,
{
    fn degree(&self) -> usize {
        2
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        debug_assert_eq!(point.len(), WIDTH + 1);
        let mut res = EF::ZERO;
        let compressed = point[WIDTH];
        for i in 0..self.compressed_output {
            res += alpha_powers[i] * point[i];
        }
        for i in self.compressed_output..WIDTH {
            res += alpha_powers[i] * point[i] * (EF::ONE - compressed);
        }

        res
    }
}

impl<const WIDTH: usize> SumcheckComputationPacked<EF> for CompressionComputation<WIDTH>
{
    fn degree(&self) -> usize {
        2
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH + 1);
        let mut res = EFPacking::<EF>::ZERO;
        let compressed = point[WIDTH];
        for i in 0..self.compressed_output {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i];
        }
        for i in self.compressed_output..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i])
                * point[i]
                * (PFPacking::<EF>::ONE - compressed);
        }

        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH + 1);
        let mut res = EFPacking::<EF>::ZERO;
        let compressed = point[WIDTH];
        for i in 0..self.compressed_output {
            res += point[i] * alpha_powers[i];
        }
        for i in self.compressed_output..WIDTH {
            res += point[i] * (EFPacking::<EF>::ONE - compressed) * alpha_powers[i];
        }

        res
    }
}
