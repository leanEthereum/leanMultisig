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
    pub(crate) fn build(matrix: DftOutput<EF>, n_cols: usize) -> (Self, [PF<EF>; DIGEST_ELEMS]) {
        match matrix {
            DftOutput::Base(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>, PF<EF>>(m, n_cols);
                (MerkleData::Base(prover_data), root)
            }
            DftOutput::Extension(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>, EF>(m, n_cols);
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
    /// Number of entries at the start of the committed polynomial that are
    /// non-zero. Trailing entries `[valid_size, 2^num_variables)` are
    /// guaranteed to be zero (padding). When the committed polynomial is
    /// a stacked concatenation of sub-polynomials, this is the total data
    /// size (sum of sub-poly sizes + any inter-sub-poly pads).
    ///
    /// The sumcheck weights we stamp don't need to reach into the padding
    /// since `f ≡ 0` there. Setting this to less than `2^num_variables`
    /// lets `add_new_*_equality` skip fully-padding rayon chunks.
    ///
    /// Equals `1 << num_variables` when the polynomial has no padding.
    pub valid_size: usize,
}

impl<EF> WhirConfig<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    #[instrument(skip_all)]
    pub fn commit(&self, prover_state: &mut impl FSProver<EF>, polynomial: &MleOwned<EF>) -> Witness<EF> {
        let n_blocks = 1usize << self.folding_factor.at_round(0);

        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &polynomial.by_ref(),
                self.folding_factor.at_round(0),
                self.starting_log_inv_rate,
                n_blocks,
            )
        });

        let (prover_data, root) = MerkleData::build(folded_matrix, n_blocks);

        prover_state.add_base_scalars(&root);

        let (ood_points, ood_answers) =
            sample_ood_points::<EF, _>(prover_state, self.commitment_ood_samples, self.num_variables, |point| {
                polynomial.evaluate(point)
            });

        Witness {
            prover_data,
            ood_points,
            ood_answers,
            // Default: assume no padding. Callers (e.g., stacked PCS) may
            // overwrite this with a smaller value after constructing the witness.
            valid_size: 1usize << self.num_variables,
        }
    }
}
