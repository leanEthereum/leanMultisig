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
pub struct FullRoundComputation<const WIDTH: usize, const FIRST: bool> {
    pub constants: [F; WIDTH],
    pub compressed_output: Option<usize>,
}

impl<NF: ExtensionField<F>, const WIDTH: usize, const FIRST: bool> SumcheckComputation<NF, EF>
    for FullRoundComputation<WIDTH, FIRST>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
    EF: ExtensionField<NF>,
{
    fn degree(&self) -> usize {
        3 + self.compressed_output.is_some() as usize
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        debug_assert_eq!(
            point.len(),
            WIDTH
                + if self.compressed_output.is_some() {
                    1
                } else {
                    0
                }
        );
        let mut buff: [NF; WIDTH] = array::from_fn(|j| point[j]);
        if FIRST {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        }
        buff.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + self.constants[j]).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        let mut res = EF::ZERO;
        if let Some(compression_output_width) = self.compressed_output {
            let compressed = point[WIDTH];
            for i in 0..compression_output_width {
                res += alpha_powers[i] * buff[i];
            }
            for i in compression_output_width..WIDTH {
                res += alpha_powers[i] * buff[i] * (EF::ONE - compressed);
            }
        } else {
            for i in 0..WIDTH {
                res += alpha_powers[i] * buff[i];
            }
        }
        res
    }
}

impl<const WIDTH: usize, const FIRST: bool> SumcheckComputationPacked<EF>
    for FullRoundComputation<WIDTH, FIRST>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    fn degree(&self) -> usize {
        3 + self.compressed_output.is_some() as usize
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(
            point.len(),
            WIDTH
                + if self.compressed_output.is_some() {
                    1
                } else {
                    0
                }
        );
        let mut buff: [PFPacking<EF>; WIDTH] = array::from_fn(|j| point[j]);
        if FIRST {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        }
        buff.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + self.constants[j]).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        let mut res = EFPacking::<EF>::ZERO;
        if let Some(compression_output_width) = self.compressed_output {
            let compressed = point[WIDTH];
            for i in 0..compression_output_width {
                res += EFPacking::<EF>::from(alpha_powers[i]) * buff[i];
            }
            for i in compression_output_width..WIDTH {
                res += EFPacking::<EF>::from(alpha_powers[i])
                    * buff[i]
                    * (PFPacking::<EF>::ONE - compressed);
            }
        } else {
            for j in 0..WIDTH {
                res += EFPacking::<EF>::from(alpha_powers[j]) * buff[j];
            }
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(
            point.len(),
            WIDTH
                + if self.compressed_output.is_some() {
                    1
                } else {
                    0
                }
        );
        let mut buff: [EFPacking<EF>; WIDTH] = array::from_fn(|j| point[j]);
        if FIRST {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        }
        buff.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + PFPacking::<EF>::from(self.constants[j])).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        let mut res = EFPacking::<EF>::ZERO;
        if let Some(compression_output_width) = self.compressed_output {
            let compressed = point[WIDTH];
            for i in 0..compression_output_width {
                res += buff[i] * alpha_powers[i];
            }
            for i in compression_output_width..WIDTH {
                res += buff[i] * (EFPacking::<EF>::ONE - compressed) * alpha_powers[i];
            }
        } else {
            for j in 0..WIDTH {
                res += buff[j] * alpha_powers[j];
            }
        }
        res
    }
}
