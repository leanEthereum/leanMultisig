// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use fiat_shamir::FSProver;
use field::{ExtensionField, TwoAdicField};
use poly::*;
use tracing::{info_span, instrument};

use crate::*;

#[derive(Debug, Clone)]
pub enum MerkleData<EF: ExtensionField<PF<EF>>> {
    Base(RoundMerkleTree<PF<EF>, PF<EF>>),
    Extension(RoundMerkleTree<PF<EF>, EF>),
}

impl<EF: ExtensionField<PF<EF>>> MerkleData<EF> {
    pub(crate) fn build(
        matrix: DftOutput<EF>,
        full_n_cols: usize,
        effective_n_cols: usize,
    ) -> (Self, [PF<EF>; DIGEST_ELEMS]) {
        match matrix {
            DftOutput::Base(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>, PF<EF>>(m, full_n_cols, effective_n_cols);
                (MerkleData::Base(prover_data), root)
            }
            DftOutput::Extension(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>, EF>(m, full_n_cols, effective_n_cols);
                (MerkleData::Extension(prover_data), root)
            }
        }
    }

    pub(crate) fn open(&self, index: usize) -> (MleOwned<EF>, Vec<[PF<EF>; DIGEST_ELEMS]>) {
        match self {
            MerkleData::Base(prover_data) => {
                let (leaf, proof) = merkle_open::<PF<EF>, PF<EF>>(prover_data, index);
                (MleOwned::Base(leaf), proof)
            }
            MerkleData::Extension(prover_data) => {
                let (leaf, proof) = merkle_open::<PF<EF>, EF>(prover_data, index);
                (MleOwned::Extension(leaf), proof)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Witness<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    pub prover_data: MerkleData<EF>,
    pub ood_points: Vec<EF>,
    pub ood_answers: Vec<EF>,
}

impl<'a, EF> WhirConfig<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    #[instrument(skip_all)]
    pub fn commit(
        &self,
        prover_state: &mut impl FSProver<EF>,
        polynomial: &MleOwned<EF>,
        actual_data_len: usize, // polynomial[actual_data_len..] is zero
    ) -> Witness<EF> {
        let n_blocks = 1usize << self.folding_factor.at_round(0);
        let evals_len = 1usize << self.num_variables;
        let effective_n_cols = actual_data_len.div_ceil(evals_len / n_blocks);
        // DFT matrix width: skip as many zero columns as possible, aligned to packing (SIMD)
        let dft_n_cols = effective_n_cols.next_multiple_of(packing_width::<EF>()).min(n_blocks);

        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &polynomial.by_ref(),
                self.folding_factor.at_round(0),
                self.starting_log_inv_rate,
                dft_n_cols,
            )
        });

        let (prover_data, root) = MerkleData::build(folded_matrix, n_blocks, effective_n_cols);

        prover_state.add_base_scalars(&root);

        let (ood_points, ood_answers) = sample_ood_points::<EF, _>(
            prover_state,
            self.committment_ood_samples,
            self.num_variables,
            |point| polynomial.evaluate(point),
        );

        Witness {
            prover_data,
            ood_points,
            ood_answers,
        }
    }
}
