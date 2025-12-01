use std::{array, usize};

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{GenericPoseidon2LinearLayersKoalaBear, KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;
use p3_poseidon2::GenericPoseidon2LinearLayers;

use crate::{EF, F};

#[derive(Debug)]
pub struct BatchPartialRounds<const WIDTH: usize, const N_COMMITED_CUBES: usize> {
    pub constants: [F; N_COMMITED_CUBES],
    pub last_constant: F,
}

impl<const WIDTH: usize, const N_COMMITED_CUBES: usize> SumcheckComputation<EF>
    for BatchPartialRounds<WIDTH, N_COMMITED_CUBES>
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
        point: &[FPacking<F>],
        _: &[EFPacking<EF>],
        _: &Self::ExtraData,
        alpha_powers: &[EF],
    ) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), WIDTH + N_COMMITED_CUBES);
        debug_assert_eq!(alpha_powers.len(), WIDTH + N_COMMITED_CUBES);

        let mut res = EFPacking::<EF>::ZERO;
        let mut buff: [FPacking<F>; WIDTH] = array::from_fn(|j| point[j]);
        for (i, &constant) in self.constants.iter().enumerate() {
            let computed_cube = (buff[0] + constant).cube();
            res += EFPacking::<EF>::from(alpha_powers[WIDTH + i]) * computed_cube;
            buff[0] = point[WIDTH + i]; // commited cube
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        }

        buff[0] = (buff[0] + self.last_constant).cube();
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        for i in 0..WIDTH {
            res += EFPacking::<EF>::from(alpha_powers[i]) * buff[i];
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
        debug_assert_eq!(point.len(), WIDTH + N_COMMITED_CUBES);
        debug_assert_eq!(alpha_powers.len(), WIDTH + N_COMMITED_CUBES);

        let mut res = EFPacking::<EF>::ZERO;
        let mut buff: [EFPacking<EF>; WIDTH] = array::from_fn(|j| point[j]);
        for (i, &constant) in self.constants.iter().enumerate() {
            let computed_cube = (buff[0] + PFPacking::<EF>::from(constant)).cube();
            res += computed_cube * alpha_powers[WIDTH + i];
            buff[0] = point[WIDTH + i]; // commited cube
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        }

        buff[0] = (buff[0] + PFPacking::<EF>::from(self.last_constant)).cube();
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        for i in 0..WIDTH {
            res += buff[i] * alpha_powers[i];
        }
        res
    }
}

impl<const WIDTH: usize, const N_COMMITED_CUBES: usize> BatchPartialRounds<WIDTH, N_COMMITED_CUBES>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
    EF: ExtensionField<PF<EF>>,
{
    #[inline(always)]
    fn my_eval<NF: ExtensionField<PF<EF>>>(&self, point: &[NF], alpha_powers: &[EF]) -> EF
    where
        EF: ExtensionField<NF>,
    {
        debug_assert_eq!(point.len(), WIDTH + N_COMMITED_CUBES);
        debug_assert_eq!(alpha_powers.len(), WIDTH + N_COMMITED_CUBES);

        let mut res = EF::ZERO;
        let mut buff: [NF; WIDTH] = array::from_fn(|j| point[j]);
        for (i, &constant) in self.constants.iter().enumerate() {
            let computed_cube = (buff[0] + constant).cube();
            res += alpha_powers[WIDTH + i] * computed_cube;
            buff[0] = point[WIDTH + i]; // commited cube
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        }

        buff[0] = (buff[0] + self.last_constant).cube();
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        for i in 0..WIDTH {
            res += alpha_powers[i] * buff[i];
        }
        res
    }
}
