use std::ops::{Deref, DerefMut};

use field::*;
use rand::{Rng, distr::StandardUniform};
use serde::{Deserialize, Serialize};

/// A point `(x_1, ..., x_n)` in `F^n` for some field `F`.
///
/// Often, `x_i` are binary. If strictly binary, `BinaryHypercubePoint` is used.
#[derive(Default, Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MultilinearPoint<F>(pub Vec<F>);

impl<F> Deref for MultilinearPoint<F> {
    type Target = Vec<F>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F> DerefMut for MultilinearPoint<F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<F> MultilinearPoint<F>
where
    F: Field,
{
    /// Returns the number of variables (dimension `n`).
    #[inline]
    #[must_use]
    pub fn num_variables(&self) -> usize {
        self.len()
    }

    /// Converts a univariate evaluation point into a multilinear one.
    ///
    /// Uses the bijection:
    /// ```ignore
    /// f(x_1, ..., x_n) <-> g(y) := f(y^(2^(n-1)), ..., y^4, y^2, y)
    /// ```
    /// Meaning:
    /// ```ignore
    /// x_1^i_1 * ... * x_n^i_n <-> y^i
    /// ```
    /// where `(i_1, ..., i_n)` is the **big-endian** binary decomposition of `i`.
    ///
    /// Reversing the order ensures the **big-endian** convention.
    pub fn expand_from_univariate(point: F, num_variables: usize) -> Self {
        let mut res = Vec::with_capacity(num_variables);
        let mut cur = point;

        for _ in 0..num_variables {
            res.push(cur);
            cur = cur.square(); // Compute y^(2^k) at each step
        }

        Self(res)
    }

    /// Computes `eq(c, p)`, where `p` is a general `MultilinearPoint` (not necessarily binary).
    ///
    /// The **equality polynomial** for two vectors is:
    /// ```ignore
    /// eq(s1, s2) = ∏ (s1_i * s2_i + (1 - s1_i) * (1 - s2_i))
    /// ```
    /// which evaluates to `1` if `s1 == s2`, and `0` otherwise.
    ///
    /// This uses the algebraic identity:
    /// ```ignore
    /// s1_i * s2_i + (1 - s1_i) * (1 - s2_i) = 1 + 2 * s1_i * s2_i - s1_i - s2_i
    /// ```
    /// to avoid unnecessary multiplications.
    #[must_use]
    pub fn eq_poly_outside(&self, point: &Self) -> F {
        assert_eq!(self.num_variables(), point.num_variables());

        let mut acc = F::ONE;

        for (&l, &r) in self.iter().zip(&point.0) {
            // l * r + (1 - l) * (1 - r) = 1 + 2 * l * r - l - r
            // +/- much cheaper than multiplication.
            acc *= F::ONE + l * r.double() - l - r;
        }

        acc
    }

    /// Embeds the point into an extension field `EF`.
    #[must_use]
    pub fn embed<EF: ExtensionField<F>>(&self) -> MultilinearPoint<EF> {
        MultilinearPoint(self.0.iter().map(|&x| EF::from(x)).collect())
    }

    pub fn random<R: Rng>(rng: &mut R, num_vars: usize) -> Self
    where
        StandardUniform: rand::distr::Distribution<F>,
    {
        let mut v = Vec::with_capacity(num_vars);
        for _ in 0..num_vars {
            v.push(rng.random());
        }
        Self(v)
    }
}

impl<F> From<Vec<F>> for MultilinearPoint<F> {
    fn from(v: Vec<F>) -> Self {
        Self(v)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Evaluation<F> {
    pub point: MultilinearPoint<F>,
    pub value: F,
}

impl<F: Field> Evaluation<F> {
    pub fn new(point: impl Into<MultilinearPoint<F>>, value: F) -> Self {
        Self {
            point: point.into(),
            value,
        }
    }

    pub fn num_variables(&self) -> usize {
        self.point.num_variables()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct MultiEvaluation<F> {
    pub point: MultilinearPoint<F>,
    pub values: Vec<F>,
}

impl<F: Field> MultiEvaluation<F> {
    pub fn new(point: impl Into<MultilinearPoint<F>>, values: Vec<F>) -> Self {
        Self {
            point: point.into(),
            values,
        }
    }

    pub fn num_variables(&self) -> usize {
        self.point.num_variables()
    }

    pub fn num_values(&self) -> usize {
        self.values.len()
    }

    pub fn split(self) -> Vec<Evaluation<F>> {
        self.values
            .into_iter()
            .map(|value| Evaluation::new(self.point.clone(), value))
            .collect()
    }
}
