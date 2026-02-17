// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use std::{fmt::Debug, marker::PhantomData};

use fiat_shamir::{FSVerifier, ProofError, ProofResult, pack_scalars_to_extension};
use field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing, TwoAdicField};
use poly::*;

use crate::*;

#[derive(Debug, Clone)]
pub struct ParsedCommitment<F: Field, EF: ExtensionField<F>> {
    pub num_variables: usize,
    pub root: [PF<EF>; DIGEST_ELEMS],
    pub ood_points: Vec<EF>,
    pub ood_answers: Vec<EF>,
    pub base_field: PhantomData<F>,
}

impl<F: Field, EF: ExtensionField<F>> ParsedCommitment<F, EF> {
    pub fn parse(
        verifier_state: &mut impl FSVerifier<EF>,
        num_variables: usize,
        ood_samples: usize,
    ) -> ProofResult<Self>
    where
        F: TwoAdicField,
        EF: ExtensionField<F> + TwoAdicField,
        EF: ExtensionField<PF<EF>>,
    {
        let root = verifier_state.next_base_scalars_vec(DIGEST_ELEMS)?.try_into().unwrap();
        let mut ood_points = vec![];
        let ood_answers = if ood_samples > 0 {
            ood_points = verifier_state.sample_vec(ood_samples);
            verifier_state.next_extension_scalars_vec(ood_samples)?
        } else {
            Vec::new()
        };
        Ok(Self {
            num_variables,
            root,
            ood_points,
            ood_answers,
            base_field: PhantomData,
        })
    }

    pub fn oods_constraints(&self) -> Vec<SparseStatement<EF>> {
        self.ood_points
            .iter()
            .zip(&self.ood_answers)
            .map(|(&point, &eval)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, self.num_variables),
                    eval,
                )
            })
            .collect()
    }
}

impl<'a, EF> WhirConfig<EF>
where
    EF: TwoAdicField + ExtensionField<PF<EF>>,
{
    pub fn parse_commitment<F: TwoAdicField>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
    ) -> ProofResult<ParsedCommitment<F, EF>>
    where
        EF: ExtensionField<F>,
    {
        ParsedCommitment::<F, EF>::parse(verifier_state, self.num_variables, self.committment_ood_samples)
    }
}

impl<'a, EF> WhirConfig<EF>
where
    EF: TwoAdicField + ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    #[allow(clippy::too_many_lines)]
    pub fn verify<F: TwoAdicField>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        parsed_commitment: &ParsedCommitment<F, EF>,
        statement: Vec<SparseStatement<EF>>,
    ) -> ProofResult<MultilinearPoint<EF>>
    where
        EF: ExtensionField<F>,
        F: ExtensionField<PF<EF>>,
    {
        statement
            .iter()
            .for_each(|c| assert_eq!(c.total_num_variables, parsed_commitment.num_variables));

        // During the rounds we collect constraints, combination randomness, folding randomness
        // and we update the claimed sum of constraint evaluation.
        let mut round_constraints = Vec::new();
        let mut round_folding_randomness = Vec::new();
        let mut claimed_sum = EF::ZERO;
        let mut prev_commitment = parsed_commitment.clone();

        // Combine OODS and statement constraints to claimed_sum
        let constraints: Vec<_> = prev_commitment
            .oods_constraints()
            .into_iter()
            .chain(statement)
            .collect();
        let combination_randomness = self.combine_constraints(verifier_state, &mut claimed_sum, &constraints)?;
        round_constraints.push((combination_randomness, constraints));

        // Initial sumcheck
        let folding_randomness = verify_sumcheck_rounds::<F, EF>(
            verifier_state,
            &mut claimed_sum,
            self.folding_factor.at_round(0),
            self.starting_folding_pow_bits,
        )?;
        round_folding_randomness.push(folding_randomness);

        for round_index in 0..self.n_rounds() {
            // Fetch round parameters from config
            let round_params = &self.round_parameters[round_index];

            // Receive commitment to the folded polynomial (likely encoded at higher expansion)
            let new_commitment =
                ParsedCommitment::<F, EF>::parse(verifier_state, round_params.num_variables, round_params.ood_samples)?;

            // Verify in-domain challenges on the previous commitment.
            let stir_constraints = self.verify_stir_challenges(
                verifier_state,
                round_params,
                &prev_commitment,
                round_folding_randomness.last().unwrap(),
                round_index,
            )?;

            // Add out-of-domain and in-domain constraints to claimed_sum
            let constraints: Vec<SparseStatement<EF>> = new_commitment
                .oods_constraints()
                .into_iter()
                .chain(stir_constraints)
                .collect();

            let combination_randomness = self.combine_constraints(verifier_state, &mut claimed_sum, &constraints)?;
            round_constraints.push((combination_randomness.clone(), constraints));

            let folding_randomness = verify_sumcheck_rounds::<F, EF>(
                verifier_state,
                &mut claimed_sum,
                self.folding_factor.at_round(round_index + 1),
                round_params.folding_pow_bits,
            )?;

            round_folding_randomness.push(folding_randomness);

            // Update round parameters
            prev_commitment = new_commitment;
        }

        // In the final round we receive the full polynomial instead of a commitment.
        let n_final_coeffs = 1 << self.n_vars_of_final_polynomial();
        let final_evaluations = verifier_state.next_extension_scalars_vec(n_final_coeffs)?;

        // Verify in-domain challenges on the previous commitment.
        let stir_constraints = self.verify_stir_challenges(
            verifier_state,
            &self.final_round_config(),
            &prev_commitment,
            round_folding_randomness.last().unwrap(),
            self.n_rounds(),
        )?;

        // Verify stir constraints directly on final polynomial
        stir_constraints
            .iter()
            .all(|c| verify_constraint(c, &final_evaluations))
            .then_some(())
            .ok_or(ProofError::InvalidProof)
            .unwrap();

        let final_sumcheck_randomness =
            verify_sumcheck_rounds::<F, EF>(verifier_state, &mut claimed_sum, self.final_sumcheck_rounds, 0)?;
        round_folding_randomness.push(final_sumcheck_randomness.clone());

        // Compute folding randomness across all rounds.
        let folding_randomness = MultilinearPoint(
            round_folding_randomness
                .into_iter()
                .flat_map(|poly| poly.0.into_iter())
                .collect(),
        );

        let evaluation_of_weights = self.eval_constraints_poly(&round_constraints, folding_randomness.clone());

        // Check the final sumcheck evaluation
        let final_value = final_evaluations.evaluate(&final_sumcheck_randomness);
        if claimed_sum != evaluation_of_weights * final_value {
            panic!();
        }

        Ok(folding_randomness)
    }

    pub(crate) fn combine_constraints(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        claimed_sum: &mut EF,
        constraints: &[SparseStatement<EF>],
    ) -> ProofResult<Vec<EF>> {
        let combination_randomness_gen: EF = verifier_state.sample();
        let mut combination_randomness = vec![EF::ONE];
        for smt in constraints {
            for e in &smt.values {
                let combination_randomness_pow = *combination_randomness.last().unwrap();
                *claimed_sum += combination_randomness_pow * e.value;
                combination_randomness.push(combination_randomness_pow * combination_randomness_gen);
            }
        }
        combination_randomness.pop().unwrap();

        Ok(combination_randomness)
    }

    fn verify_stir_challenges<F: Field>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        params: &RoundConfig<EF>,
        commitment: &ParsedCommitment<F, EF>,
        folding_randomness: &MultilinearPoint<EF>,
        round_index: usize,
    ) -> ProofResult<Vec<SparseStatement<EF>>>
    where
        EF: ExtensionField<F>,
        F: ExtensionField<PF<EF>>,
    {
        let leafs_base_field = round_index == 0;

        verifier_state.check_pow_grinding(params.query_pow_bits)?;

        let stir_challenges_indexes = get_challenge_stir_queries(
            params.domain_size >> params.folding_factor,
            params.num_queries,
            verifier_state,
        );

        // dbg!(&stir_challenges_indexes);
        // dbg!(verifier_state.challenger().state());

        let dimensions = vec![Dimensions {
            height: params.domain_size >> params.folding_factor,
            width: 1 << params.folding_factor,
        }];
        let answers = self.verify_merkle_proof::<F>(
            verifier_state,
            &commitment.root,
            &stir_challenges_indexes,
            &dimensions,
            leafs_base_field,
            round_index,
            0,
        )?;

        // Compute STIR Constraints
        let folds: Vec<_> = answers
            .into_iter()
            .map(|answers| answers.evaluate(folding_randomness))
            .collect();

        let stir_constraints = stir_challenges_indexes
            .iter()
            .map(|&index| params.folded_domain_gen.exp_u64(index as u64))
            .zip(&folds)
            .map(|(point, &value)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(EF::from(point), params.num_variables),
                    value,
                )
            })
            .collect();

        Ok(stir_constraints)
    }

    fn verify_merkle_proof<F: Field>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        root: &[PF<EF>; DIGEST_ELEMS],
        indices: &[usize],
        dimensions: &[Dimensions],
        leafs_base_field: bool,
        round_index: usize,
        var_shift: usize,
    ) -> ProofResult<Vec<Vec<EF>>>
    where
        EF: ExtensionField<F>,
        F: ExtensionField<PF<EF>>,
    {
        // Branch depending on whether the committed leafs are base field or extension field.
        let res = if leafs_base_field {
            // Merkle leaves
            let mut answers = Vec::<Vec<F>>::new();
            let merkle_leaf_size = 1 << (self.folding_factor.at_round(round_index) - var_shift);
            for _ in 0..indices.len() {
                answers.push(pack_scalars_to_extension::<PF<EF>, F>(
                    &verifier_state
                        .receive_hint_base_scalars(merkle_leaf_size * <F as BasedVectorSpace<PF<EF>>>::DIMENSION)?,
                ));
            }

            // Merkle proofs
            let mut merkle_proofs = Vec::new();
            for _ in 0..indices.len() {
                let mut merkle_path = vec![];
                for _ in 0..self.merkle_tree_height(round_index) {
                    let digest: [PF<EF>; DIGEST_ELEMS] = verifier_state
                        .receive_hint_base_scalars(DIGEST_ELEMS)?
                        .try_into()
                        .unwrap();
                    merkle_path.push(digest);
                }
                merkle_proofs.push(merkle_path);
            }

            // For each queried index:
            for (i, &index) in indices.iter().enumerate() {
                // Verify the Merkle opening for the claimed leaf against the Merkle root.
                if !merkle_verify::<PF<EF>, F>(*root, index, dimensions[0], answers[i].clone(), &merkle_proofs[i]) {
                    panic!();
                }
            }

            // Convert the base field values to EF and collect them into a result vector.
            answers
                .into_iter()
                .map(|inner| inner.iter().map(|&f_el| f_el.into()).collect())
                .collect()
        } else {
            // Merkle leaves
            let mut answers = vec![];
            let merkle_leaf_size = if round_index == 0 {
                1 << (self.folding_factor.at_round(round_index) - var_shift)
            } else {
                1 << self.folding_factor.at_round(round_index)
            };
            for _ in 0..indices.len() {
                answers.push(verifier_state.receive_hint_extension_scalars(merkle_leaf_size)?);
            }

            // Merkle proofs
            let mut merkle_proofs = Vec::new();
            for _ in 0..indices.len() {
                let mut merkle_path = vec![];
                for _ in 0..self.merkle_tree_height(round_index) {
                    let digest: [PF<EF>; DIGEST_ELEMS] = verifier_state
                        .receive_hint_base_scalars(DIGEST_ELEMS)?
                        .try_into()
                        .unwrap();
                    merkle_path.push(digest);
                }
                merkle_proofs.push(merkle_path);
            }

            // For each queried index:
            for (i, &index) in indices.iter().enumerate() {
                // Verify the Merkle opening against the extension MMCS.
                if !merkle_verify::<PF<EF>, EF>(*root, index, dimensions[0], answers[i].clone(), &merkle_proofs[i]) {
                    panic!();
                }
            }

            // Return the extension field answers as-is.
            answers
        };

        // Return the verified leaf values.
        Ok(res)
    }

    fn eval_constraints_poly(
        &self,
        constraints: &[(Vec<EF>, Vec<SparseStatement<EF>>)],
        mut point: MultilinearPoint<EF>,
    ) -> EF {
        let mut value = EF::ZERO;

        for (round, (randomness, constraints)) in constraints.iter().enumerate() {
            if round > 0 {
                let k = self.folding_factor.at_round(round - 1);
                point = MultilinearPoint(point[k..].to_vec());
            }
            let mut i = 0;
            for smt in constraints {
                let common_eq = smt.point.eq_poly_outside(&MultilinearPoint(
                    point[point.len() - smt.inner_num_variables()..].to_vec(),
                ));
                for e in &smt.values {
                    let eval = (0..smt.selector_num_variables())
                        .map(|j| {
                            if e.selector & (1 << (smt.selector_num_variables() - 1 - j)) == 0 {
                                EF::ONE - point[j]
                            } else {
                                point[j]
                            }
                        })
                        .product::<EF>()
                        * common_eq;
                    value += eval * randomness[i];
                    i += 1;
                }
            }
            assert_eq!(i, randomness.len());
        }
        value
    }
}

fn verify_constraint<EF: Field>(constraint: &SparseStatement<EF>, poly: &[EF]) -> bool {
    // poly.evaluate(&constraint.point) == constraint.value
    constraint
        .values
        .iter()
        .all(|e| poly.evaluate_sparse(e.selector, &constraint.point) == e.value)
}

/// The full vector of folding randomness values, in reverse round order.
type SumcheckRandomness<F> = MultilinearPoint<F>;

pub(crate) fn verify_sumcheck_rounds<F, EF>(
    verifier_state: &mut impl FSVerifier<EF>,
    claimed_sum: &mut EF,
    rounds: usize,
    pow_bits: usize,
) -> ProofResult<SumcheckRandomness<EF>>
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + ExtensionField<PF<EF>>,
{
    // Preallocate vector to hold the randomness values
    let mut randomness = Vec::with_capacity(rounds);

    for _ in 0..rounds {
        // Extract the 3 evaluations of the quadratic sumcheck polynomial h(X)
        let poly = DensePolynomial::new(verifier_state.next_extension_scalars_vec(3)?);

        // Verify claimed sum is consistent with polynomial
        if poly.evaluate(EF::ZERO) + poly.evaluate(EF::ONE) != *claimed_sum {
            panic!();
        }

        verifier_state.check_pow_grinding(pow_bits)?;

        // Sample the next verifier folding randomness rᵢ
        let rand: EF = verifier_state.sample();

        // Update claimed sum using folding randomness
        *claimed_sum = poly.evaluate(rand);

        // Store this round’s randomness
        randomness.push(rand);
    }

    Ok(MultilinearPoint(randomness))
}
