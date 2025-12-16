use std::{any::TypeId, cmp::Reverse};

use multilinear_toolkit::prelude::*;
use p3_util::log2_ceil_usize;
use tracing::instrument;
use utils::{VarCount, to_big_endian_in_field};
use whir_p3::*;

#[derive(Debug)]
pub struct MultiCommitmentWitness<EF: ExtensionField<PF<EF>>> {
    pub dims: PackedDims,
    pub inner_witness: Witness<EF>,
    pub packed_polynomial: MleOwned<EF>,
}

#[derive(Debug)]
pub struct PackedDims {
    pub indexes_and_vars: Vec<(usize, VarCount)>,
    pub packed_len: usize,
    pub packed_n_vars: VarCount,
}

impl PackedDims {
    pub fn compute(n_vars: &[VarCount]) -> Self {
        let mut indexes_and_vars = n_vars
            .iter()
            .enumerate()
            .map(|(index, &n_vars)| (index, n_vars))
            .collect::<Vec<_>>();
        indexes_and_vars.sort_by_key(|&(_, n_vars)| Reverse(n_vars));
        let packed_len = indexes_and_vars.iter().map(|&(_, n_vars)| 1 << n_vars).sum::<usize>();
        let packed_n_vars = log2_ceil_usize(packed_len);
        Self {
            indexes_and_vars,
            packed_len,
            packed_n_vars,
        }
    }
}

#[instrument(skip_all)]
pub fn packed_pcs_global_statements<EF: Field>(
    dims: &PackedDims,
    statements_per_polynomial: &[Vec<Evaluation<EF>>],
) -> Vec<Evaluation<EF>> {
    let mut all_statements = Vec::new();
    let mut offset = 0;
    for &(poly_index, n_vars) in &dims.indexes_and_vars {
        for statement in &statements_per_polynomial[poly_index] {
            let packed_point = MultilinearPoint(
                [
                    to_big_endian_in_field(offset >> n_vars, dims.packed_n_vars - n_vars),
                    statement.point.0.clone(),
                ]
                .concat(),
            );
            all_statements.push(Evaluation::new(packed_point, statement.value));
        }
        offset += 1 << n_vars;
    }
    all_statements
}

#[instrument(skip_all)]
pub fn packed_pcs_commit<F, EF>(
    whir_config_builder: &WhirConfigBuilder,
    polynomials: &[&[F]],
    prover_state: &mut impl FSProver<EF>,
) -> MultiCommitmentWitness<EF>
where
    F: Field + TwoAdicField + ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + ExtensionField<PF<EF>>,
{
    let dims = PackedDims::compute(
        &polynomials
            .iter()
            .map(|p| log2_strict_usize(p.len()))
            .collect::<Vec<_>>(),
    );
    tracing::info!(
        "Total committed data (full granularity): {} = 2^{:.3} | packed to 2^{}",
        dims.packed_len,
        (dims.packed_len as f64).log2(),
        dims.packed_n_vars
    );
    let mut packed_polynomial = F::zero_vec(1 << dims.packed_n_vars); // TODO avoid this huge cloning of all witness data
    let mut split_indices = dims
        .indexes_and_vars
        .iter()
        .scan(0, |state, &(_, n_vars)| {
            let current = *state;
            *state += 1 << n_vars;
            Some(current)
        })
        .collect::<Vec<_>>();
    split_indices.remove(0);
    split_at_mut_many(&mut packed_polynomial[..dims.packed_len], &split_indices)
        .par_iter_mut()
        .zip(&dims.indexes_and_vars)
        .for_each(|(packed_chunk, &(poly_index, _))| {
            let original_poly = &polynomials[poly_index];
            packed_chunk.copy_from_slice(original_poly);
        });

    let packed_polynomial = if TypeId::of::<F>() == TypeId::of::<PF<EF>>() {
        MleOwned::Base(unsafe { std::mem::transmute::<Vec<F>, Vec<PF<EF>>>(packed_polynomial) })
    } else if TypeId::of::<F>() == TypeId::of::<EF>() {
        MleOwned::ExtensionPacked(pack_extension(&unsafe {
            std::mem::transmute::<Vec<F>, Vec<EF>>(packed_polynomial)
        })) // TODO this is innefficient (this transposes everything...)
    } else {
        panic!("Unsupported field type for packed PCS: {}", std::any::type_name::<F>());
    };

    let inner_witness =
        WhirConfig::new(whir_config_builder, dims.packed_n_vars).commit(prover_state, &packed_polynomial);
    MultiCommitmentWitness {
        inner_witness,
        dims,
        packed_polynomial,
    }
}

pub fn packed_pcs_parse_commitment<
    F: Field + TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + ExtensionField<PF<EF>>,
>(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF>,
    dims: &PackedDims,
) -> Result<ParsedCommitment<F, EF>, ProofError>
where
    PF<EF>: TwoAdicField,
{
    WhirConfig::new(whir_config_builder, dims.packed_n_vars).parse_commitment(verifier_state)
}
