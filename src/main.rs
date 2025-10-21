#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::array;
use utils::{build_prover_state, transposed_par_iter_mut};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const UNIVARIATE_SKIPS: usize = 3;

fn multilvariate_eval<F: Field, EF: ExtensionField<F>>(poly: &[F], point: &[EF]) -> EF {
    assert_eq!(poly.len(), 1 << (point.len() + UNIVARIATE_SKIPS - 1));
    univariate_selectors::<F>(UNIVARIATE_SKIPS)
        .iter()
        .zip(poly.chunks_exact(1 << (point.len() - 1)))
        .map(|(selector, chunk)| {
            selector.evaluate(point[0]) * chunk.evaluate(&MultilinearPoint(point[1..].to_vec()))
        })
        .sum()
}

pub struct FullRoundComputation {
    pub constants: [F; 16],
    pub matrix: [[F; 16]; 16],
}

impl<NF: ExtensionField<F>, EF: ExtensionField<NF>> SumcheckComputation<NF, EF>
    for FullRoundComputation
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        assert_eq!(point.len(), 16);
        let intermediate: [NF; 16] = array::from_fn(|j| point[j].cube() + self.constants[j]);
        let mut res = EF::ZERO;
        for j in 0..16 {
            let mut temp = NF::ZERO;
            for k in 0..16 {
                temp += intermediate[k] * self.matrix[j][k];
            }
            res += alpha_powers[j] * temp;
        }
        res
    }
}

pub struct FullRoundComputationPacked {
    pub constants: [F; 16],
    pub matrix: [[F; 16]; 16],
}

impl SumcheckComputationPacked<EF> for FullRoundComputationPacked {
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        assert_eq!(point.len(), 16);
        let intermediate: [PFPacking<EF>; 16] =
            array::from_fn(|j| point[j].cube() + self.constants[j]);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            let mut temp = PFPacking::<EF>::ZERO;
            for k in 0..16 {
                temp += intermediate[k] * self.matrix[j][k];
            }
            res += alpha_powers[j] * temp;
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        assert_eq!(point.len(), 16);
        let intermediate: [EFPacking<EF>; 16] =
            array::from_fn(|j| point[j].cube() + self.constants[j]);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            let mut temp = EFPacking::<EF>::ZERO;
            for k in 0..16 {
                temp += intermediate[k] * self.matrix[j][k];
            }
            res += temp * alpha_powers[j];
        }
        res
    }
}

fn main() {
    let mut rng = StdRng::seed_from_u64(0);
    let log_n_poseidons = 13;
    let n_poseidons = 1 << log_n_poseidons;
    let perm_inputs = (0..n_poseidons)
        .map(|_| rng.random())
        .collect::<Vec<[F; 16]>>();

    let input_layers: [_; 16] =
        array::from_fn(|i| perm_inputs.par_iter().map(|x| x[i]).collect::<Vec<F>>());

    let constants: [F; 16] = rng.random();
    let matrix: [[F; 16]; 16] = rng.random();

    let mut output_layers: [_; 16] = array::from_fn(|_| F::zero_vec(n_poseidons));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let intermediate: [F; 16] =
                array::from_fn(|j| input_layers[j][row_index].cube() + constants[j]);
            output_row.into_iter().enumerate().for_each(|(j, output)| {
                let mut res = F::ZERO;
                for k in 0..16 {
                    res += matrix[j][k] * intermediate[k];
                }
                *output = res;
            });
        });

    let claim_point = MultilinearPoint(
        (0..(log_n_poseidons + 1 - UNIVARIATE_SKIPS))
            .map(|_| rng.random())
            .collect::<Vec<EF>>(),
    );

    let output_claims = output_layers
        .par_iter()
        .map(|output_layer| multilvariate_eval(output_layer, &claim_point))
        .collect::<Vec<EF>>();

    let mut prover_state = build_prover_state::<EF>();
    prover_state.add_extension_scalars(&output_claims);
    let batching_scalar = prover_state.sample();
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());
    let batching_scalars_powers = batching_scalar.powers().collect_n(16);
    let batched_output_layer = (0..n_poseidons)
        .into_par_iter()
        .map(|i| {
            dot_product(
                batching_scalars_powers.iter().copied(),
                (0..16).map(|j| output_layers[j][i]),
            )
        })
        .collect::<Vec<EF>>();

    assert_eq!(
        batched_claim,
        multilvariate_eval(&batched_output_layer, &claim_point)
    );

    let (sumcheck_point, sumcheck_inner_evals, sumcheck_final_sum) = sumcheck_prove(
        UNIVARIATE_SKIPS,
        MleGroupRef::Base(input_layers.iter().map(Vec::as_slice).collect()),
        &FullRoundComputation { constants, matrix },
        &FullRoundComputationPacked { constants, matrix },
        &batching_scalars_powers,
        Some((claim_point.0.clone(), None)),
        false,
        &mut prover_state,
        batched_claim,
        None,
    );

    for i in 0..16 {
        assert_eq!(
            sumcheck_inner_evals[i],
            multilvariate_eval(&input_layers[i], &sumcheck_point)
        );
    }
}
