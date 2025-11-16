use multilinear_toolkit::prelude::*;

use crate::EF;

#[derive(Debug)]
pub struct CompressionComputation<const WIDTH: usize> {
    pub compressed_output: usize,
}

impl<const WIDTH: usize> SumcheckComputation<EF> for CompressionComputation<WIDTH>
where
    EF: ExtensionField<PF<EF>>,
{
    fn degree(&self) -> usize {
        2
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
    
    #[inline(always)]
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

impl<const WIDTH: usize> CompressionComputation<WIDTH> {
    #[inline(always)]
    fn my_eval<EF: ExtensionField<PF<EF>>, NF: ExtensionField<PF<EF>>>(
        &self,
        point: &[NF],
        alpha_powers: &[EF],
    ) -> EF
    where
        EF: ExtensionField<NF>,
    {
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
