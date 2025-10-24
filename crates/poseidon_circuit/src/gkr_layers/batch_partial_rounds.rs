use std::array;

use multilinear_toolkit::prelude::*;
use p3_field::ExtensionField;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KoalaBearInternalLayerParameters, KoalaBearParameters,
};
use p3_monty_31::InternalLayerBaseParameters;
use p3_poseidon2::GenericPoseidon2LinearLayers;

use crate::{EF, F};

#[derive(Debug)]
pub struct BatchPartialRounds<const WIDTH: usize, const N_COMMITED_CUBES: usize> {
    pub constants: [F; N_COMMITED_CUBES],
    pub last_constant: F,
}

impl<NF: ExtensionField<F>, const WIDTH: usize, const N_COMMITED_CUBES: usize>
    SumcheckComputation<NF, EF> for BatchPartialRounds<WIDTH, N_COMMITED_CUBES>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
    EF: ExtensionField<NF>,
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
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

impl<const WIDTH: usize, const N_COMMITED_CUBES: usize> SumcheckComputationPacked<EF>
    for BatchPartialRounds<WIDTH, N_COMMITED_CUBES>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_base(&self, point: &[FPacking<F>], alpha_powers: &[EF]) -> EFPacking<EF> {
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

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
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
