use std::fmt::Debug;

use whir_p3::poly::multilinear::MultilinearPoint;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Evaluation<F> {
    pub point: MultilinearPoint<F>,
    pub value: F,
}

impl<F> From<Evaluation<F>> for (MultilinearPoint<F>, F) {
    fn from(val: Evaluation<F>) -> Self {
        (val.point, val.value)
    }
}

impl<F> From<(MultilinearPoint<F>, F)> for Evaluation<F> {
    fn from((point, value): (MultilinearPoint<F>, F)) -> Self {
        Self { point, value }
    }
}
