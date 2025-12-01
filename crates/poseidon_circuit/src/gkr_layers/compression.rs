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
    type ExtraData = ();

    fn degrees(&self) -> Vec<usize> {
        vec![2]
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
        point: &[PFPacking<EF>],
        _: &[EFPacking<EF>],
        _: &Self::ExtraData,
        alpha_powers: &[EF],
    ) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH + 1);
        let mut res = EFPacking::<EF>::ZERO;
        let compressed = point[WIDTH];
        for i in 0..self.compressed_output {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i];
        }
        for i in self.compressed_output..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i]) * point[i] * (PFPacking::<EF>::ONE - compressed);
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
    fn my_eval<EF: ExtensionField<PF<EF>> + ExtensionField<NF>, NF: ExtensionField<PF<EF>>>(
        &self,
        point: &[NF],
        alpha_powers: &[EF],
    ) -> EF {
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
