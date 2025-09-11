use rayon::prelude::*;
use std::{iter::Sum, marker::PhantomData, ops::Add};
use sumcheck::{MleGroupRef, ProductComputation};
use tracing::{info_span, instrument};

use p3_field::dot_product;
use p3_field::{BasedVectorSpace, ExtensionField, Field};
use utils::{Evaluation, FSProver, PF, pack_extension, transmute_slice};
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::evals::eval_eq,
};

use crate::pcs::PCS;

#[derive(Debug)]
pub struct RingSwitching<F, EF, InnerPcs, const EXTENSION_DEGREE: usize> {
    inner_pcs: InnerPcs,
    f: PhantomData<F>,
    ef: PhantomData<EF>,
}

impl<F, EF, InnerPcs, const EXTENSION_DEGREE: usize>
    RingSwitching<F, EF, InnerPcs, EXTENSION_DEGREE>
{
    pub const fn new(inner_pcs: InnerPcs) -> Self {
        Self {
            inner_pcs,
            f: PhantomData,
            ef: PhantomData,
        }
    }
}

impl<
    F: Field,
    EF: ExtensionField<F> + ExtensionField<PF<EF>>,
    InnerPcs: PCS<EF, EF>,
    const EXTENSION_DEGREE: usize,
> PCS<F, EF> for RingSwitching<F, EF, InnerPcs, EXTENSION_DEGREE>
{
    type ParsedCommitment = InnerPcs::ParsedCommitment;
    type Witness = InnerPcs::Witness;

    fn commit(
        &self,
        dft: &EvalsDft<utils::PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        polynomial: &[F],
    ) -> Self::Witness {
        let packed_poly: &[EF] = transmute_slice::<F, EF>(polynomial);
        self.inner_pcs.commit(dft, prover_state, packed_poly)
    }

    fn open(
        &self,
        dft: &EvalsDft<utils::PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        statements: &[Evaluation<EF>],
        witness: Self::Witness,
        polynomial: &[F],
    ) {
        let _span = info_span!("RingSwitching::open").entered();
        assert_eq!(statements.len(), 1);
        let eval = &statements[0];
        assert_eq!(<EF as BasedVectorSpace<F>>::DIMENSION, EXTENSION_DEGREE);
        assert!(EXTENSION_DEGREE.is_power_of_two());
        let kappa = EXTENSION_DEGREE.ilog2() as usize;
        let transmuted_pol = transmute_slice::<F, EF>(polynomial);
        let point = &eval.point;
        let packed_point = &point[..point.len() - kappa];
        let eval_eq_packed_point =
            info_span!("eval_eq of packed_point").in_scope(|| eval_eq(packed_point));

        let s_hat =
            eval_mixed_tensor::<F, EF, EXTENSION_DEGREE>(transmuted_pol, &eval_eq_packed_point);
        prover_state.add_extension_scalars(&s_hat.rows());

        let r_pp = (0..kappa)
            .map(|_| prover_state.sample())
            .collect::<Vec<_>>();

        let lagranged_r_pp: [EF; EXTENSION_DEGREE] = eval_eq(&r_pp).try_into().unwrap();
        let a_pol = piecewise_dot_product_at_field_level::<F, EF, EXTENSION_DEGREE>(
            &eval_eq_packed_point,
            &lagranged_r_pp,
        );

        let s0: EF = dot_product(s_hat.rows::<EF>().into_iter(), lagranged_r_pp.into_iter());

        let (packed_transmuted_pol, packed_a_pol) = info_span!("packing")
            .in_scope(|| (pack_extension(transmuted_pol), pack_extension(&a_pol)));

        let (r_p, _, sc_value) = info_span!("sumcheck").in_scope(|| {
            sumcheck::prove(
                1,
                MleGroupRef::ExtensionPacked(vec![&packed_transmuted_pol, &packed_a_pol]),
                &ProductComputation,
                &ProductComputation,
                &[],
                None,
                false,
                prover_state,
                s0,
                None,
            )
        });

        let packed_value = get_s_prime::<F, EF, EXTENSION_DEGREE>(
            &point.0,
            kappa,
            &r_p,
            &lagranged_r_pp,
            sc_value,
        );

        let packed_eval = Evaluation {
            point: r_p,
            value: packed_value,
        };
        let inner_statements = vec![packed_eval];
        _span.exit();
        self.inner_pcs.open(
            dft,
            prover_state,
            &inner_statements,
            witness,
            transmuted_pol,
        );
    }

    fn parse_commitment(
        &self,
        verifier_state: &mut utils::FSVerifier<EF, impl FSChallenger<EF>>,
        num_variables: usize,
    ) -> Result<Self::ParsedCommitment, ProofError> {
        self.inner_pcs.parse_commitment(
            verifier_state,
            num_variables - EXTENSION_DEGREE.ilog2() as usize,
        )
    }

    fn verify(
        &self,
        verifier_state: &mut utils::FSVerifier<EF, impl FSChallenger<EF>>,
        parsed_commitment: &Self::ParsedCommitment,
        statements: &[utils::Evaluation<EF>],
    ) -> Result<(), ProofError> {
        assert!(EXTENSION_DEGREE.is_power_of_two());
        let kappa = EXTENSION_DEGREE.ilog2() as usize;
        assert_eq!(statements.len(), 1);
        let eval = &statements[0];
        let n_packed_vars = eval.point.len() - kappa;

        let s_hat = TensorAlgebra::<F, EXTENSION_DEGREE>::from_rows(
            &verifier_state
                .next_extension_scalars_vec(EXTENSION_DEGREE)?
                .try_into()
                .unwrap(),
        );

        let lagrange_evals = eval_eq(&eval.point[n_packed_vars..]);
        let columns = s_hat.columns::<EF>();

        if dot_product::<EF, _, _>(columns.into_iter(), lagrange_evals.into_iter()) != eval.value {
            return Err(ProofError::InvalidProof);
        }

        let r_pp = (0..kappa)
            .map(|_| verifier_state.sample())
            .collect::<Vec<_>>();

        let rows = s_hat.rows::<EF>();
        let lagranged_r_pp = eval_eq(&r_pp);
        let s0 = dot_product(rows.into_iter(), lagranged_r_pp.clone().into_iter());
        let (claimed_s0, sc_claim) = sumcheck::verify(verifier_state, n_packed_vars, 2)
            .map_err(|_| ProofError::InvalidProof)?;
        if claimed_s0 != s0 {
            return Err(ProofError::InvalidProof);
        }

        let s_prime = get_s_prime::<F, EF, EXTENSION_DEGREE>(
            &eval.point,
            kappa,
            &sc_claim.point,
            &lagranged_r_pp,
            sc_claim.value,
        );
        let inner_statements = vec![Evaluation {
            point: sc_claim.point,
            value: s_prime,
        }];
        self.inner_pcs
            .verify(verifier_state, parsed_commitment, &inner_statements)
            .map_err(|_| ProofError::InvalidProof)?;

        Ok(())
    }
}

fn get_s_prime<F: Field, EF: ExtensionField<F>, const EXTENSION_DEGREE: usize>(
    point: &[EF],
    kappa: usize,
    sc_point: &[EF],
    lagranged_r_pp: &[EF],
    sc_value: EF,
) -> EF {
    // e := eq(φ0(rκ), . . . , φ0(rℓ−1), φ1(r′0), . . . , φ1(r′ℓ′−1))
    let mut e = TensorAlgebra::<F, EXTENSION_DEGREE>::one();
    for (&r, &r_prime) in point[..point.len() - kappa].iter().zip(sc_point) {
        e = e.scale_columns(r).scale_rows(r_prime)
            + e.scale_columns(EF::ONE - r).scale_rows(EF::ONE - r_prime);
    }

    sc_value / dot_product(e.rows::<EF>().into_iter(), lagranged_r_pp.iter().copied())
}

struct TensorAlgebra<F, const D: usize>([[F; D]; D]);

impl<F: Field, const D: usize> TensorAlgebra<F, D> {
    fn phi_0_times_phi_1<EF: ExtensionField<F>>(p0: &EF, p1: &EF) -> Self {
        let p0_split = p0.as_basis_coefficients_slice();
        let p1_split = p1.as_basis_coefficients_slice();
        let mut data = [[F::ZERO; D]; D];
        for i in 0..D {
            for j in 0..D {
                data[i][j] = p0_split[i] * p1_split[j];
            }
        }
        Self(data)
    }

    fn rows<EF: ExtensionField<F>>(&self) -> [EF; D] {
        let mut result = [EF::ZERO; D];
        for i in 0..D {
            result[i] = EF::from_basis_coefficients_slice(&self.0[i]).unwrap();
        }
        result
    }

    fn columns<EF: ExtensionField<F>>(&self) -> [EF; D] {
        let mut result = [EF::ZERO; D];
        for j in 0..D {
            let mut col = [F::ZERO; D];
            for i in 0..D {
                col[i] = self.0[i][j];
            }
            result[j] = EF::from_basis_coefficients_slice(&col).unwrap();
        }
        result
    }

    fn from_rows<EF: ExtensionField<F>>(rows: &[EF; D]) -> Self {
        let mut data = [[F::ZERO; D]; D];
        for i in 0..D {
            data[i] = rows[i].as_basis_coefficients_slice().try_into().unwrap();
        }
        Self(data)
    }

    fn from_columns<EF: ExtensionField<F>>(columns: &[EF; D]) -> Self {
        let mut data = [[F::ZERO; D]; D];
        for j in 0..D {
            let col = columns[j].as_basis_coefficients_slice();
            for i in 0..D {
                data[i][j] = col[i];
            }
        }
        Self(data)
    }

    const fn one() -> Self {
        let mut res = [[F::ZERO; D]; D];
        res[0][0] = F::ONE;
        Self(res)
    }

    fn scale_columns<EF: ExtensionField<F>>(&self, scalar: EF) -> Self {
        let mut columns = self.columns::<EF>();
        for col in &mut columns {
            *col *= scalar;
        }
        Self::from_columns(&columns)
    }

    fn scale_rows<EF: ExtensionField<F>>(&self, scalar: EF) -> Self {
        let mut rows = self.rows::<EF>();
        for row in &mut rows {
            *row *= scalar;
        }
        Self::from_rows(&rows)
    }
}

impl<F: Field, const D: usize> Sum for TensorAlgebra<F, D> {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let mut result = Self([[F::ZERO; D]; D]);
        for item in iter {
            result = result + item;
        }
        result
    }
}

impl<F: Field, const D: usize> Add for TensorAlgebra<F, D> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let mut result = [[F::ZERO; D]; D];
        for i in 0..D {
            for j in 0..D {
                result[i][j] = self.0[i][j] + other.0[i][j];
            }
        }
        Self(result)
    }
}

#[instrument(skip_all)]
fn eval_mixed_tensor<F: Field, EF: ExtensionField<F>, const D: usize>(
    poly: &[EF],
    eval_eq_packed_point: &[EF],
) -> TensorAlgebra<F, D> {
    // returns φ1(self)(φ0(point[0]), φ0(point[1]), ...)
    assert_eq!(eval_eq_packed_point.len(), poly.len());
    eval_eq_packed_point
        .par_iter()
        .zip(poly)
        .map(|(l, e)| TensorAlgebra::phi_0_times_phi_1(l, e))
        .sum()
}

#[instrument(skip_all)]
pub fn piecewise_dot_product_at_field_level<F: Field, EF: ExtensionField<F>, const D: usize>(
    poly: &[EF],
    scalars: &[EF; D],
) -> Vec<EF> {
    poly.par_iter()
        .map(|e| {
            <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(e)
                .iter()
                .zip(scalars)
                .map(|(&a, &b)| b * a)
                .sum::<EF>()
        })
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod tests {
    use p3_field::extension::BinomialExtensionField;
    use p3_koala_bear::KoalaBear;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use utils::{
        MyMerkleCompress, MyMerkleHash, build_merkle_compress, build_merkle_hash,
        build_prover_state, build_verifier_state, init_tracing,
    };
    use whir_p3::{
        poly::{evals::EvaluationsList, multilinear::MultilinearPoint},
        whir::config::{FoldingFactor, SecurityAssumption, WhirConfigBuilder},
    };

    use super::*;

    const DIMENSION: usize = 8;
    type F = KoalaBear;
    type EF = BinomialExtensionField<F, DIMENSION>;

    #[test]
    fn test_ring_switching() {
        init_tracing();

        let num_variables = 25;
        let mut rng = StdRng::seed_from_u64(0);
        let polynomial = (0..1 << num_variables)
            .map(|_| rng.random())
            .collect::<Vec<F>>();
        let point = MultilinearPoint(
            (0..num_variables)
                .map(|_| rng.random())
                .collect::<Vec<EF>>(),
        );

        let inner_pcs = WhirConfigBuilder {
            max_num_variables_to_send_coeffs: 6,
            security_level: 128,
            pow_bits: 17,
            folding_factor: FoldingFactor::ConstantFromSecondRound(4, 4),
            merkle_hash: build_merkle_hash(),
            merkle_compress: build_merkle_compress(),
            soundness_type: SecurityAssumption::CapacityBound,
            starting_log_inv_rate: 1,
            rs_domain_initial_reduction_factor: 3,
            base_field: PhantomData,
            extension_field: PhantomData,
        };

        let dft = EvalsDft::<F>::new(
            1 << (num_variables + inner_pcs.starting_log_inv_rate
                - inner_pcs.folding_factor.at_round(0)),
        );

        type InnerPcs = WhirConfigBuilder<EF, EF, MyMerkleHash, MyMerkleCompress, 8>;

        let statement = vec![Evaluation {
            point: point.clone(),
            value: polynomial.evaluate(&point),
        }];

        let mut prover_state = build_prover_state();

        let ring_switch_pcs = RingSwitching::<F, EF, InnerPcs, 8>::new(inner_pcs);

        let witness = ring_switch_pcs.commit(&dft, &mut prover_state, &polynomial);

        ring_switch_pcs.open(&dft, &mut prover_state, &statement, witness, &polynomial);

        let mut verifier_state = build_verifier_state(&prover_state);

        let parsed_commitment = ring_switch_pcs
            .parse_commitment(&mut verifier_state, num_variables)
            .unwrap();

        ring_switch_pcs
            .verify(&mut verifier_state, &parsed_commitment, &statement)
            .unwrap();
    }
}
