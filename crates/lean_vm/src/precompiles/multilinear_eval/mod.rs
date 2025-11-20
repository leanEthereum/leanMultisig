//! Multilinear polynomial evaluation witness

use crate::core::{EF, F};
use crate::{
    Bus, BusDirection, BusSelector, ColIndex, DIMENSION, ExtensionFieldLookupIntoMemory,
    LookupIntoMemory, Memory, ModularPrecompile, PrecompileExecutionContext, PrecompileTrace,
    RunnerError, Table, VECTOR_LEN, VectorLookupIntoMemory,
};
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::ToUsize;

#[derive(Debug)]
pub struct MultilinearEvalPrecompile;

#[derive(Debug, Clone)]
pub struct WitnessMultilinearEval {
    /// Evaluation point coordinates (one per variable)
    pub point: Vec<EF>,
    /// Computed evaluation result
    pub res: EF,
}

impl WitnessMultilinearEval {
    pub fn n_vars(&self) -> usize {
        self.point.len()
    }
}

pub const MULTILINEAR_EVAL_COL_INDEX_POLY: ColIndex = 0;
pub const MULTILINEAR_EVAL_COL_INDEX_POINT: ColIndex = 1;
pub const MULTILINEAR_EVAL_COL_INDEX_RES: ColIndex = 2;
pub const MULTILINEAR_EVAL_COL_INDEX_N_VARS: ColIndex = 3;


impl ModularPrecompile for MultilinearEvalPrecompile {
    fn name() -> &'static str {
        "multilinear_eval"
    }

    fn identifier() -> Table {
        Table::MultilinearEval
    }

    fn commited_columns() -> &'static [ColIndex] {
        &[]
    }

    fn simple_lookups() -> &'static [LookupIntoMemory] {
        &[]
    }

    fn ext_field_lookups() -> &'static [ExtensionFieldLookupIntoMemory] {
        &[]
    }

    fn vector_lookups() -> &'static [VectorLookupIntoMemory] {
        &[]
    }

    fn buses() -> Vec<Bus> {
        vec![Bus {
            table: Table::MultilinearEval,
            direction: BusDirection::Pull,
            selector: BusSelector::DenseOnes,
            data: vec![
                MULTILINEAR_EVAL_COL_INDEX_POLY,
                MULTILINEAR_EVAL_COL_INDEX_POINT,
                MULTILINEAR_EVAL_COL_INDEX_RES,
                MULTILINEAR_EVAL_COL_INDEX_N_VARS,
            ],
        }]
    }

    #[inline(always)]
    fn execute(
        ptr_coeffs: F,
        ptr_point: F,
        ptr_res: F,
        n_vars: usize,
        memory: &mut Memory,
        trace: &mut PrecompileTrace,
        ctx: PrecompileExecutionContext<'_>,
    ) -> Result<(), RunnerError> {
        let n_coeffs = 1 << n_vars;
        let slice_coeffs = memory.slice(ptr_coeffs.to_usize() << n_vars, n_coeffs)?;

        let log_point_size = log2_ceil_usize(n_vars * DIMENSION);
        let point_slice =
            memory.slice(ptr_point.to_usize() << log_point_size, n_vars * DIMENSION)?;
        for i in n_vars * DIMENSION..(n_vars * DIMENSION).next_power_of_two() {
            memory.set((ptr_point.to_usize() << log_point_size) + i, F::ZERO)?; // padding
        }
        let point = point_slice[..n_vars * DIMENSION]
            .chunks_exact(DIMENSION)
            .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
            .collect::<Vec<_>>();

        let eval = slice_coeffs.evaluate(&MultilinearPoint(point.clone()));
        let mut res_vec = eval.as_basis_coefficients_slice().to_vec();
        res_vec.resize(VECTOR_LEN, F::ZERO);
        memory.set_vector(ptr_res.to_usize(), res_vec.try_into().unwrap())?;

        trace.base[MULTILINEAR_EVAL_COL_INDEX_POLY].push(ptr_coeffs);
        trace.base[MULTILINEAR_EVAL_COL_INDEX_POINT].push(ptr_point);
        trace.base[MULTILINEAR_EVAL_COL_INDEX_RES].push(ptr_res);
        trace.base[MULTILINEAR_EVAL_COL_INDEX_N_VARS].push(F::from_usize(n_vars));
        
        ctx.multilinear_evals_witness
            .push(WitnessMultilinearEval { point, res: eval });

        Ok(())
    }

    fn padding_row() -> Vec<EF> {
        unreachable!()
    }
}

impl Air for MultilinearEvalPrecompile {
    type ExtraData = ();
    fn n_columns_f() -> usize {
        4
    }
    fn n_columns_ef() -> usize {
        0
    }
    fn degree() -> usize {
        unreachable!()
    }
    fn down_column_indexes() -> Vec<usize> {
        unreachable!()
    }
    fn n_constraints() -> usize {
        unreachable!()
    }
    fn eval<AB: p3_air::AirBuilder>(&self, _: &mut AB, _: &Self::ExtraData) {
        unreachable!()
    }
}
