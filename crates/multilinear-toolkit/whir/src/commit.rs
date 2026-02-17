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
    pub(crate) fn build(matrix: DftOutput<EF>) -> (Self, [PF<EF>; DIGEST_ELEMS]) {
        match matrix {
            DftOutput::Base(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>, PF<EF>>(m);
                (MerkleData::Base(prover_data), root)
            }
            DftOutput::Extension(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>, EF>(m);
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
    pub fn commit(&self, prover_state: &mut impl FSProver<EF>, polynomial: &MleOwned<EF>) -> Witness<EF> {
        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &polynomial.by_ref(),
                self.folding_factor.at_round(0),
                self.starting_log_inv_rate,
            )
        });

        let (prover_data, root) = MerkleData::build(folded_matrix);

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
