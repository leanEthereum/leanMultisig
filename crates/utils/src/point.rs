use std::fmt::Debug;

use whir_p3::poly::multilinear::MultilinearPoint;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluation<F> {
    pub point: MultilinearPoint<F>,
    pub value: F,
}

impl<F> Into<(MultilinearPoint<F>, F)> for Evaluation<F> {
    fn into(self) -> (MultilinearPoint<F>, F) {
        (self.point, self.value)
    }
}

impl<F> From<(MultilinearPoint<F>, F)> for Evaluation<F> {
    fn from((point, value): (MultilinearPoint<F>, F)) -> Self {
        Self { point, value }
    }
}
