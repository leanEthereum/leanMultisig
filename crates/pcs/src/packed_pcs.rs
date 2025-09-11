use p3_field::{ExtensionField, Field};
use p3_util::log2_strict_usize;
use tracing::instrument;
use utils::{Evaluation, FSProver, FSVerifier, PF};
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::multilinear::MultilinearPoint,
};

use crate::{
    PCS,
    combinatorics::{TreeOfVariables, TreeOfVariablesInner},
};

#[derive(Debug)]
pub struct MultiCommitmentWitness<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>> {
    pub tree: TreeOfVariables,
    pub inner_witness: Pcs::Witness,
    pub packed_polynomial: Vec<F>,
}

pub fn num_packed_vars_for_pols<F: Field>(polynomials: &[&[F]]) -> usize {
    let vars_per_polynomial = polynomials
        .iter()
        .map(|p| log2_strict_usize(p.len()))
        .collect::<Vec<_>>();
    TreeOfVariables::compute_optimal(vars_per_polynomial).total_vars()
}

pub fn num_packed_vars_for_vars(vars_per_polynomial: &[usize]) -> usize {
    TreeOfVariables::compute_optimal(vars_per_polynomial.to_vec()).total_vars()
}

#[instrument(skip_all)]
pub fn packed_pcs_commit<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>>(
    pcs: &Pcs,
    polynomials: &[&[F]],
    dft: &EvalsDft<PF<EF>>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
) -> MultiCommitmentWitness<F, EF, Pcs> {
    let polynomials: Vec<&[F]> = polynomials.to_vec();
    let vars_per_polynomial = polynomials
        .iter()
        .map(|p| log2_strict_usize(p.len()))
        .collect::<Vec<_>>();
    let tree = TreeOfVariables::compute_optimal(vars_per_polynomial);
    let mut packed_polynomial = F::zero_vec(1 << tree.total_vars());
    tree.root.fill_commitment(
        &mut packed_polynomial,
        &polynomials,
        &tree.vars_per_polynomial,
    );
    let inner_witness = pcs.commit(dft, prover_state, &packed_polynomial);
    MultiCommitmentWitness {
        tree,
        inner_witness,
        packed_polynomial,
    }
}

pub fn packed_pcs_global_statements<EF: Field>(
    tree: &TreeOfVariables,
    statements_per_polynomial: &[Vec<Evaluation<EF>>],
) -> Vec<Evaluation<EF>> {
    check_tree(tree, statements_per_polynomial).expect("Invalid tree structure for multi-open");

    tree.root
        .global_statement(&tree.vars_per_polynomial, statements_per_polynomial, &[])
}

#[derive(Debug)]
pub struct ParsedMultiCommitment<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>> {
    pub tree: TreeOfVariables,
    pub inner_parsed_commitment: Pcs::ParsedCommitment,
}

pub fn packed_pcs_parse_commitment<F: Field, EF: ExtensionField<F>, Pcs: PCS<F, EF>>(
    pcs: &Pcs,
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    vars_per_polynomial: Vec<usize>,
) -> Result<ParsedMultiCommitment<F, EF, Pcs>, ProofError> {
    let tree = TreeOfVariables::compute_optimal(vars_per_polynomial);
    let inner_parsed_commitment = pcs.parse_commitment(verifier_state, tree.total_vars())?;
    Ok(ParsedMultiCommitment {
        tree,
        inner_parsed_commitment,
    })
}

fn check_tree<EF: Field>(
    tree: &TreeOfVariables,
    statements_per_polynomial: &[Vec<Evaluation<EF>>],
) -> Result<(), ProofError> {
    assert_eq!(
        statements_per_polynomial.len(),
        tree.vars_per_polynomial.len()
    );
    for (evals, &vars) in statements_per_polynomial
        .iter()
        .zip(&tree.vars_per_polynomial)
    {
        for eval in evals {
            assert_eq!(eval.point.len(), vars);
        }
    }
    Ok(())
}

impl TreeOfVariablesInner {
    fn fill_commitment<F: Field>(
        &self,
        buff: &mut [F],
        polynomials: &[&[F]],
        vars_per_polynomial: &[usize],
    ) {
        match self {
            Self::Polynomial(i) => {
                let len = polynomials[*i].len();
                buff[..len].copy_from_slice(polynomials[*i]);
            }
            Self::Composed { left, right } => {
                let (left_buff, right_buff) = buff.split_at_mut(buff.len() / 2);
                let left_buff = &mut left_buff[..1 << left.total_vars(vars_per_polynomial)];
                let right_buff = &mut right_buff[..1 << right.total_vars(vars_per_polynomial)];
                rayon::join(
                    || left.fill_commitment(left_buff, polynomials, vars_per_polynomial),
                    || right.fill_commitment(right_buff, polynomials, vars_per_polynomial),
                );
            }
        }
    }

    fn global_statement<F: Field, EF: ExtensionField<F>>(
        &self,
        vars_per_polynomial: &[usize],
        statements_per_polynomial: &[Vec<Evaluation<EF>>],
        selectors: &[EF],
    ) -> Vec<Evaluation<EF>> {
        match self {
            Self::Polynomial(i) => {
                let mut res = Vec::new();
                for eval in &statements_per_polynomial[*i] {
                    res.push(Evaluation {
                        point: MultilinearPoint(
                            [selectors.to_vec(), eval.point.0.clone()].concat(),
                        ),
                        value: eval.value,
                    });
                }
                res
            }
            Self::Composed { left, right } => {
                let left_vars = left.total_vars(vars_per_polynomial);
                let right_vars = right.total_vars(vars_per_polynomial);

                let mut left_selectors = selectors.to_vec();
                left_selectors.push(EF::ZERO);
                left_selectors.extend(EF::zero_vec(right_vars.saturating_sub(left_vars)));

                let mut right_selectors = selectors.to_vec();
                right_selectors.push(EF::ONE);
                right_selectors.extend(EF::zero_vec(left_vars.saturating_sub(right_vars)));

                let left_statements = left.global_statement(
                    vars_per_polynomial,
                    statements_per_polynomial,
                    &left_selectors,
                );
                let right_statements = right.global_statement(
                    vars_per_polynomial,
                    statements_per_polynomial,
                    &right_selectors,
                );
                [left_statements, right_statements].concat()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use p3_field::extension::BinomialExtensionField;
    use p3_koala_bear::KoalaBear;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use utils::{
        build_merkle_compress, build_merkle_hash, build_prover_state, build_verifier_state,
    };
    use whir_p3::{
        poly::evals::EvaluationsList,
        whir::config::{FoldingFactor, SecurityAssumption, WhirConfigBuilder},
    };

    use super::*;

    type F = KoalaBear;
    type EF = BinomialExtensionField<F, 4>;

    #[test]
    fn test_check_tree() {
        let pcs = WhirConfigBuilder {
            folding_factor: FoldingFactor::ConstantFromSecondRound(4, 4),
            soundness_type: SecurityAssumption::CapacityBound,
            merkle_hash: build_merkle_hash(),
            merkle_compress: build_merkle_compress(),
            pow_bits: 16,
            max_num_variables_to_send_coeffs: 6,
            rs_domain_initial_reduction_factor: 1,
            security_level: 90,
            starting_log_inv_rate: 1,
            base_field: PhantomData::<F>,
            extension_field: PhantomData::<EF>,
        };

        let mut rng = StdRng::seed_from_u64(0);
        let vars_per_polynomial = [4, 4, 5, 3, 7, 10, 8];
        let mut polynomials = Vec::new();
        let mut statements_per_polynomial = Vec::new();
        for &vars in &vars_per_polynomial {
            let poly = (0..1 << vars).map(|_| rng.random()).collect::<Vec<F>>();
            let n_points = rng.random_range(1..5);
            let mut statements = Vec::new();
            for _ in 0..n_points {
                let point = MultilinearPoint((0..vars).map(|_| rng.random()).collect::<Vec<EF>>());
                let value = poly.evaluate(&point);
                statements.push(Evaluation { point, value });
            }
            polynomials.push(poly);
            statements_per_polynomial.push(statements);
        }

        let mut prover_state = build_prover_state();
        let dft = EvalsDft::<F>::default();

        let polynomials_refs = polynomials.iter().map(|p| p.as_slice()).collect::<Vec<_>>();
        let witness = packed_pcs_commit(&pcs, &polynomials_refs, &dft, &mut prover_state);

        let packed_statements =
            packed_pcs_global_statements(&witness.tree, &statements_per_polynomial);
        pcs.open(
            &dft,
            &mut prover_state,
            &packed_statements,
            witness.inner_witness,
            &witness.packed_polynomial,
        );

        let mut verifier_state = build_verifier_state(&prover_state);

        let parsed_commitment =
            packed_pcs_parse_commitment(&pcs, &mut verifier_state, vars_per_polynomial.to_vec())
                .unwrap();
        let packed_statements =
            packed_pcs_global_statements(&parsed_commitment.tree, &statements_per_polynomial);
        pcs.verify(
            &mut verifier_state,
            &parsed_commitment.inner_parsed_commitment,
            &packed_statements,
        )
        .unwrap();
    }
}
