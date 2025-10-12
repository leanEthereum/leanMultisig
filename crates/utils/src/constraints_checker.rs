use std::marker::PhantomData;

use p3_air::AirBuilder;
use p3_field::ExtensionField;
use p3_matrix::dense::RowMajorMatrixView;

use multilinear_toolkit::prelude::*;

/*
Debug purpose
*/

#[derive(Debug)]
pub struct ConstraintChecker<'a, IF, EF> {
    pub main: (RowMajorMatrixView<'a, IF>, RowMajorMatrixView<'a, EF>),
    pub constraint_index: usize,
    pub errors: Vec<usize>,
    pub field: PhantomData<EF>,
}

impl<'a, EF: ExtensionField<PF<EF>> + ExtensionField<IF>, IF: ExtensionField<PF<EF>>> AirBuilder
    for ConstraintChecker<'a, IF, EF>
{
    type F = PF<EF>;
    type Expr = IF;
    type Var = IF;
    type Var2 = EF;
    type M1 = RowMajorMatrixView<'a, IF>;
    type M2 = RowMajorMatrixView<'a, EF>;

    #[inline]
    fn main(&self) -> (Self::M1, Self::M2) {
        self.main
    }

    #[inline]
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let x: IF = x.into();
        if !x.is_zero() {
            self.errors.push(self.constraint_index);
        }
        self.constraint_index += 1;
    }

    fn assert_zero_2(&mut self, x: Self::Var2) {
        if !x.is_zero() {
            self.errors.push(self.constraint_index);
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, _: [I; N]) {
        unreachable!()
    }
}
