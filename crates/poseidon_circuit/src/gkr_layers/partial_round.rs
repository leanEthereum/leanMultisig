use multilinear_toolkit::prelude::*;
use p3_field::ExtensionField;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KoalaBearInternalLayerParameters, KoalaBearParameters,
};
use p3_monty_31::InternalLayerBaseParameters;
use p3_poseidon2::GenericPoseidon2LinearLayers;

use crate::{EF, F};

#[derive(Debug)]
pub struct PartialRoundComputation<const WIDTH: usize> {
    pub constant: F,
}

impl<NF: ExtensionField<F>, const WIDTH: usize> SumcheckComputation<NF, EF>
    for PartialRoundComputation<WIDTH>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
    EF: ExtensionField<NF>,
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        debug_assert_eq!(point.len(), WIDTH);
        let first_cubed = (point[0] + self.constant).cube();
        let mut buff = [NF::ZERO; WIDTH];
        buff[0] = first_cubed;
        buff[1..WIDTH].copy_from_slice(&point[1..WIDTH]);
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        let mut res = EF::ZERO;
        for i in 0..WIDTH {
            res += alpha_powers[i] * buff[i];
        }
        res
    }
}

impl<const WIDTH: usize> SumcheckComputationPacked<EF> for PartialRoundComputation<WIDTH>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_base(&self, point: &[FPacking<F>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let first_cubed = (point[0] + self.constant).cube();
        let mut buff = [PFPacking::<EF>::ZERO; WIDTH];
        buff[0] = first_cubed;
        buff[1..WIDTH].copy_from_slice(&point[1..WIDTH]);
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[j]) * buff[j];
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH);
        let first_cubed = (point[0] + PFPacking::<EF>::from(self.constant)).cube();
        let mut buff = [EFPacking::<EF>::ZERO; WIDTH];
        buff[0] = first_cubed;
        buff[1..WIDTH].copy_from_slice(&point[1..WIDTH]);
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..WIDTH {
            res += buff[j] * alpha_powers[j];
        }
        res
    }
}
