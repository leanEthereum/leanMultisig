//! Multilinear polynomial evaluation witness

use crate::core::{EF, F};
use crate::*;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::ToUsize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl TableT for MultilinearEvalPrecompile {
    fn name(&self) -> &'static str {
        "multilinear_eval"
    }

    fn identifier(&self) -> Table {
        Table::multilinear_eval()
    }

    fn commited_columns_f(&self) -> Vec<ColIndex> {
        unreachable!()
    }

    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        unreachable!()
    }

    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        unreachable!()
    }

    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        unreachable!()
    }

    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        unreachable!()
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: self.identifier(),
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

    fn padding_row_f(&self) -> Vec<PF<EF>> {
        unreachable!()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        unreachable!()
    }

    #[inline(always)]
    fn execute(
        &self,
        ptr_coeffs: F,
        ptr_point: F,
        ptr_res: F,
        n_vars: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        let trace = &mut ctx.precompile_traces[self.identifier().index()];
        let n_coeffs = 1 << n_vars;
        let slice_coeffs = ctx
            .memory
            .slice(ptr_coeffs.to_usize() << n_vars, n_coeffs)?;

        let log_point_size = log2_ceil_usize(n_vars * DIMENSION);
        let point_slice = ctx
            .memory
            .slice(ptr_point.to_usize() << log_point_size, n_vars * DIMENSION)?;
        for i in n_vars * DIMENSION..(n_vars * DIMENSION).next_power_of_two() {
            ctx.memory
                .set((ptr_point.to_usize() << log_point_size) + i, F::ZERO)?; // padding
        }
        let point = point_slice[..n_vars * DIMENSION]
            .chunks_exact(DIMENSION)
            .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
            .collect::<Vec<_>>();

        let eval = slice_coeffs.evaluate(&MultilinearPoint(point.clone()));
        let mut res_vec = eval.as_basis_coefficients_slice().to_vec();
        res_vec.resize(VECTOR_LEN, F::ZERO);
        ctx.memory
            .set_vector(ptr_res.to_usize(), res_vec.try_into().unwrap())?;

        trace.base[MULTILINEAR_EVAL_COL_INDEX_POLY].push(ptr_coeffs);
        trace.base[MULTILINEAR_EVAL_COL_INDEX_POINT].push(ptr_point);
        trace.base[MULTILINEAR_EVAL_COL_INDEX_RES].push(ptr_res);
        trace.base[MULTILINEAR_EVAL_COL_INDEX_N_VARS].push(F::from_usize(n_vars));

        ctx.multilinear_evals_witness
            .push(WitnessMultilinearEval { point, res: eval });

        Ok(())
    }
}

impl Air for MultilinearEvalPrecompile {
    type ExtraData = ();
    fn n_columns_f_air(&self) -> usize {
        4
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        unreachable!()
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        unreachable!()
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        unreachable!()
    }
    fn n_constraints(&self) -> usize {
        unreachable!()
    }
    fn eval<AB: p3_air::AirBuilder>(&self, _: &mut AB, _: &Self::ExtraData) {
        unreachable!()
    }
}
