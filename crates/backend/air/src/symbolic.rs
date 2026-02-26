// cf https://github.com/Plonky3/Plonky3/blob/main/uni-stark/src/symbolic_builder.rs

use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::rc::Rc;

use field::{Algebra, Field, InjectiveMonomial, PrimeCharacteristicRing};

use crate::{Air, AirBuilder};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SymbolicVariable<F> {
    pub index: usize,
    pub(crate) _phantom: PhantomData<F>,
}

impl<F> SymbolicVariable<F> {
    pub const fn new(index: usize) -> Self {
        Self {
            index,
            _phantom: PhantomData,
        }
    }
}

impl<F: Field, T> Add<T> for SymbolicVariable<F>
where
    T: Into<SymbolicExpression<F>>,
{
    type Output = SymbolicExpression<F>;

    fn add(self, rhs: T) -> Self::Output {
        SymbolicExpression::from(self) + rhs.into()
    }
}

impl<F: Field, T> Sub<T> for SymbolicVariable<F>
where
    T: Into<SymbolicExpression<F>>,
{
    type Output = SymbolicExpression<F>;

    fn sub(self, rhs: T) -> Self::Output {
        SymbolicExpression::from(self) - rhs.into()
    }
}

impl<F: Field, T> Mul<T> for SymbolicVariable<F>
where
    T: Into<SymbolicExpression<F>>,
{
    type Output = SymbolicExpression<F>;

    fn mul(self, rhs: T) -> Self::Output {
        SymbolicExpression::from(self) * rhs.into()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SymbolicOperation {
    Add,
    Sub,
    Mul,
    Neg,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymbolicExpression<F> {
    Variable(SymbolicVariable<F>),
    Constant(F),
    Operation(Rc<(SymbolicOperation, Vec<Self>)>),
}

impl<F: Field> Default for SymbolicExpression<F> {
    fn default() -> Self {
        Self::Constant(F::ZERO)
    }
}

impl<F: Field> From<SymbolicVariable<F>> for SymbolicExpression<F> {
    fn from(var: SymbolicVariable<F>) -> Self {
        Self::Variable(SymbolicVariable::new(var.index))
    }
}

impl<F: Field> From<F> for SymbolicExpression<F> {
    fn from(val: F) -> Self {
        Self::Constant(val)
    }
}

impl<F: Field> PrimeCharacteristicRing for SymbolicExpression<F> {
    type PrimeSubfield = F::PrimeSubfield;

    const ZERO: Self = Self::Constant(F::ZERO);
    const ONE: Self = Self::Constant(F::ONE);
    const TWO: Self = Self::Constant(F::TWO);
    const NEG_ONE: Self = Self::Constant(F::NEG_ONE);
    const INVERSE_OF_TWO: Self = Self::Constant(F::INVERSE_OF_TWO);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        F::from_prime_subfield(f).into()
    }
}

impl<F: Field> Algebra<F> for SymbolicExpression<F> {}
impl<F: Field> Algebra<SymbolicVariable<F>> for SymbolicExpression<F> {}
impl<F: Field + InjectiveMonomial<N>, const N: u64> InjectiveMonomial<N> for SymbolicExpression<F> {}

impl<F: Field, T> Add<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    type Output = Self;

    fn add(self, rhs: T) -> Self {
        match (self, rhs.into()) {
            (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs + rhs),
            (lhs, rhs) => Self::Operation(Rc::new((SymbolicOperation::Add, vec![lhs, rhs]))),
        }
    }
}

impl<F: Field, T> AddAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn add_assign(&mut self, rhs: T) {
        *self = self.clone() + rhs.into();
    }
}

impl<F: Field, T> Sum<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.map(Into::into).reduce(|x, y| x + y).unwrap_or(Self::ZERO)
    }
}

impl<F: Field, T: Into<Self>> Sub<T> for SymbolicExpression<F> {
    type Output = Self;

    fn sub(self, rhs: T) -> Self {
        match (self, rhs.into()) {
            (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs - rhs),
            (lhs, rhs) => Self::Operation(Rc::new((SymbolicOperation::Sub, vec![lhs, rhs]))),
        }
    }
}

impl<F: Field, T> SubAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn sub_assign(&mut self, rhs: T) {
        *self = self.clone() - rhs.into();
    }
}

impl<F: Field> Neg for SymbolicExpression<F> {
    type Output = Self;

    fn neg(self) -> Self {
        match self {
            Self::Constant(c) => Self::Constant(-c),
            expr => Self::Operation(Rc::new((SymbolicOperation::Neg, vec![expr]))),
        }
    }
}

impl<F: Field, T: Into<Self>> Mul<T> for SymbolicExpression<F> {
    type Output = Self;

    fn mul(self, rhs: T) -> Self {
        match (self, rhs.into()) {
            (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs * rhs),
            (lhs, rhs) => Self::Operation(Rc::new((SymbolicOperation::Mul, vec![lhs, rhs]))),
        }
    }
}

impl<F: Field, T> MulAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn mul_assign(&mut self, rhs: T) {
        *self = self.clone() * rhs.into();
    }
}

impl<F: Field, T: Into<Self>> Product<T> for SymbolicExpression<F> {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.map(Into::into).reduce(|x, y| x * y).unwrap_or(Self::ONE)
    }
}

#[derive(Debug)]
struct SymbolicAirBuilder<F: Field> {
    up: Vec<SymbolicExpression<F>>,
    down: Vec<SymbolicExpression<F>>,
    constraints: Vec<SymbolicExpression<F>>,
    bus_flag_value: Option<SymbolicExpression<F>>,
    bus_data_values: Option<Vec<SymbolicExpression<F>>>,
}

impl<F: Field> SymbolicAirBuilder<F> {
    pub fn new(n_columns_up: usize, n_columns_down: usize) -> Self {
        let up = (0..n_columns_up)
            .map(|i| SymbolicExpression::Variable(SymbolicVariable::new(i)))
            .collect();
        let down = (0..n_columns_down)
            .map(|i| SymbolicExpression::Variable(SymbolicVariable::new(n_columns_up + i)))
            .collect();

        Self {
            up,
            down,
            constraints: Vec::new(),
            bus_flag_value: None,
            bus_data_values: None,
        }
    }

    pub fn constraints(&self) -> Vec<SymbolicExpression<F>> {
        self.constraints.clone()
    }
}

impl<F: Field> AirBuilder for SymbolicAirBuilder<F> {
    type F = SymbolicExpression<F>;
    type EF = SymbolicExpression<F>;

    fn up(&self) -> &[Self::F] {
        &self.up
    }

    fn down(&self) -> &[Self::F] {
        &self.down
    }

    fn assert_zero(&mut self, x: Self::F) {
        self.constraints.push(x);
    }

    fn assert_zero_ef(&mut self, x: Self::EF) {
        self.constraints.push(x);
    }

    fn eval_virtual_column(&mut self, _: Self::EF) {
        unimplemented!()
    }

    fn declare_values(&mut self, values: &[Self::F]) {
        if self.bus_flag_value.is_none() {
            assert_eq!(values.len(), 1);
            self.bus_flag_value = Some(values[0].clone());
        } else {
            assert!(self.bus_data_values.is_none());
            self.bus_data_values = Some(values.to_vec());
        }
    }
}

pub fn get_symbolic_constraints_and_bus_data_values<F: Field, A: Air>(
    air: &A,
) -> (
    Vec<SymbolicExpression<F>>,
    SymbolicExpression<F>,
    Vec<SymbolicExpression<F>>,
)
where
    A::ExtraData: Default,
{
    let mut builder = SymbolicAirBuilder::<F>::new(air.n_columns(), air.n_down_columns());
    air.eval(&mut builder, &Default::default());
    (
        builder.constraints(),
        builder.bus_flag_value.unwrap(),
        builder.bus_data_values.unwrap(),
    )
}
