use std::marker::PhantomData;

use p3_air::AirBuilder;

use multilinear_toolkit::prelude::*;

/*
Debug purpose
*/

#[derive(Debug)]
pub struct ConstraintChecker<'a, IF, EF> {
    pub main: &'a [IF],
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
    type FinalOutput = EF;

    #[inline]
    fn main(&self) -> &[IF] {
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

    fn add_custom(&mut self, value: Self::FinalOutput) {
        let _ = value;
    }
}
