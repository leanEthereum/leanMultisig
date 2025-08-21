use std::marker::PhantomData;

use p3_air::AirBuilder;
use p3_field::ExtensionField;
use p3_matrix::dense::RowMajorMatrixView;

use crate::PF;

/*
Debug purpose
*/

#[derive(Debug)]
pub struct ConstraintChecker<'a, IF, EF> {
    pub main: RowMajorMatrixView<'a, IF>,
    pub constraint_index: usize,
    pub errors: Vec<usize>,
    pub field: PhantomData<EF>,
}

impl<'a, EF: ExtensionField<PF<EF>> + ExtensionField<IF>, IF: ExtensionField<PF<EF>>> AirBuilder
    for ConstraintChecker<'a, IF, EF>
{
    type F = PF<EF>;
    type I = PF<EF>;
    type Expr = IF;
    type Var = IF;
    type M = RowMajorMatrixView<'a, IF>;

    #[inline]
    fn main(&self) -> Self::M {
        self.main
    }

    #[inline]
    fn is_first_row(&self) -> Self::Expr {
        unreachable!()
    }

    #[inline]
    fn is_last_row(&self) -> Self::Expr {
        unreachable!()
    }

    #[inline]
    fn is_transition_window(&self, _: usize) -> Self::Expr {
        unreachable!()
    }

    #[inline]
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let x: IF = x.into();
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
