use std::marker::PhantomData;

use p3_air::AirBuilder;
use p3_field::ExtensionField;
use p3_matrix::dense::DenseMatrix;

use multilinear_toolkit::prelude::*;

/*
Debug purpose
*/

#[derive(Debug)]
pub struct ConstraintCounter<EF> {
    pub num_constraints: usize,
    pub structured: bool,
    pub width_f: usize,
    pub width_ef: usize,
    pub ext_field: PhantomData<EF>,
}

impl<EF: ExtensionField<PF<EF>>> AirBuilder for ConstraintCounter<EF> {
    type F = PF<EF>;
    type Expr = EF;
    type Var = EF;
    type Var2 = EF;
    type M1 = DenseMatrix<EF>;
    type M2 = DenseMatrix<EF>;

    #[inline]
    fn main(&self) -> (Self::M1, Self::M2) {
        (
            DenseMatrix::new(
                EF::zero_vec((1 + self.structured as usize) * self.width_f),
                self.width_f,
            ),
            DenseMatrix::new(
                EF::zero_vec((1 + self.structured as usize) * self.width_ef),
                self.width_ef,
            ),
        )
    }

    #[inline]
    fn assert_zero<I: Into<Self::Expr>>(&mut self, _: I) {
        self.num_constraints += 1;
    }

    fn assert_zero_2(&mut self, _: Self::Var2) {
        self.num_constraints += 1;
    }

    #[inline]
    fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, _: [I; N]) {
        unreachable!()
    }
}
