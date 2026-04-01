// cf https://github.com/Plonky3/Plonky3/blob/main/uni-stark/src/symbolic_builder.rs

use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;

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

#[derive(Copy, Clone, Debug)]
pub struct SymbolicNode<F: Copy> {
    pub op: SymbolicOperation,
    pub lhs: SymbolicExpression<F>,
    pub rhs: SymbolicExpression<F>, // dummy (ZERO) for Neg
}

// We use an arena as a trick to allow SymbolicExpression to be Copy
// (ugly trick but fine in practice since SymbolicExpression is only used once at the start of the program)
thread_local! {
    static ARENA: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

fn alloc_node<F: Field>(node: SymbolicNode<F>) -> u32 {
    ARENA.with(|arena| {
        let mut bytes = arena.borrow_mut();
        let node_size = std::mem::size_of::<SymbolicNode<F>>();
        let idx = bytes.len();
        bytes.resize(idx + node_size, 0);
        unsafe {
            std::ptr::write_unaligned(bytes.as_mut_ptr().add(idx) as *mut SymbolicNode<F>, node);
        }
        idx as u32
    })
}

pub fn get_node<F: Field>(idx: u32) -> SymbolicNode<F> {
    ARENA.with(|arena| {
        let bytes = arena.borrow();
        unsafe { std::ptr::read_unaligned(bytes.as_ptr().add(idx as usize) as *const SymbolicNode<F>) }
    })
}

// ---------------------------------------------------------------------------
// Dot-product hints: AIR code registers these to tell the zkDSL generator
// to emit `dot_product_be` / `dot_product_ee` precompile calls.
// ---------------------------------------------------------------------------

/// Hint attached to the Operation arena-index of a symbolic result.
#[derive(Clone, Debug)]
pub enum DotProductHint<F: Copy> {
    BE(DotProductBEHint<F>),
    EE(DotProductEEHint<F>),
}

#[derive(Clone, Debug)]
pub struct DotProductBEHint<F: Copy> {
    pub constants: Vec<F>,
    pub operands: Vec<SymbolicExpression<F>>,
}

#[derive(Clone, Debug)]
pub struct DotProductEEHint<F: Copy> {
    pub a_operands: Vec<SymbolicExpression<F>>,
    pub b_operands: Vec<SymbolicExpression<F>>,
}

thread_local! {
    static DOT_PRODUCT_HINTS: RefCell<HashMap<u32, Box<dyn Any>>> = RefCell::new(HashMap::new());
}

fn clear_dot_product_hints() {
    DOT_PRODUCT_HINTS.with(|h| h.borrow_mut().clear());
}

/// Register a dot-product hint on the arena index of `result`.
pub fn register_dot_product_hint<F: Field>(result: SymbolicExpression<F>, hint: DotProductHint<F>) {
    if let SymbolicExpression::Operation(idx) = result {
        DOT_PRODUCT_HINTS.with(|h| {
            h.borrow_mut().insert(idx, Box::new(hint));
        });
    }
}

/// Query the dot-product hint for an arena index, if any.
pub fn get_dot_product_hint<F: Field>(idx: u32) -> Option<DotProductHint<F>> {
    DOT_PRODUCT_HINTS.with(|h| {
        h.borrow()
            .get(&idx)
            .and_then(|b| b.downcast_ref::<DotProductHint<F>>())
            .cloned()
    })
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SymbolicExpression<F: Copy> {
    Variable(SymbolicVariable<F>),
    Constant(F),
    Operation(u32), // index into thread-local arena
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
            (lhs, rhs) => Self::Operation(alloc_node(SymbolicNode {
                op: SymbolicOperation::Add,
                lhs,
                rhs,
            })),
        }
    }
}

impl<F: Field, T> AddAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn add_assign(&mut self, rhs: T) {
        *self = *self + rhs.into();
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
            (lhs, rhs) => Self::Operation(alloc_node(SymbolicNode {
                op: SymbolicOperation::Sub,
                lhs,
                rhs,
            })),
        }
    }
}

impl<F: Field, T> SubAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn sub_assign(&mut self, rhs: T) {
        *self = *self - rhs.into();
    }
}

impl<F: Field> Neg for SymbolicExpression<F> {
    type Output = Self;

    fn neg(self) -> Self {
        match self {
            Self::Constant(c) => Self::Constant(-c),
            expr => Self::Operation(alloc_node(SymbolicNode {
                op: SymbolicOperation::Neg,
                lhs: expr,
                rhs: Self::ZERO, // dummy
            })),
        }
    }
}

impl<F: Field, T: Into<Self>> Mul<T> for SymbolicExpression<F> {
    type Output = Self;

    fn mul(self, rhs: T) -> Self {
        match (self, rhs.into()) {
            (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs * rhs),
            (lhs, rhs) => Self::Operation(alloc_node(SymbolicNode {
                op: SymbolicOperation::Mul,
                lhs,
                rhs,
            })),
        }
    }
}

impl<F: Field, T> MulAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn mul_assign(&mut self, rhs: T) {
        *self = *self * rhs.into();
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
    type F = F;
    type IF = SymbolicExpression<F>;
    type EF = SymbolicExpression<F>;

    fn up(&self) -> &[Self::IF] {
        &self.up
    }

    fn down(&self) -> &[Self::IF] {
        &self.down
    }

    fn assert_zero(&mut self, x: Self::IF) {
        self.constraints.push(x);
    }

    fn assert_zero_ef(&mut self, x: Self::EF) {
        self.constraints.push(x);
    }

    fn eval_virtual_column(&mut self, _: Self::EF) {
        unimplemented!()
    }

    fn declare_values(&mut self, values: &[Self::IF]) {
        if self.bus_flag_value.is_none() {
            assert_eq!(values.len(), 1);
            self.bus_flag_value = Some(values[0]);
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
    // Clear the arena and hints before building constraints
    ARENA.with(|arena| arena.borrow_mut().clear());
    clear_dot_product_hints();

    let mut builder = SymbolicAirBuilder::<F>::new(air.n_columns(), air.n_down_columns());
    air.eval(&mut builder, &Default::default());
    (
        builder.constraints(),
        builder.bus_flag_value.unwrap(),
        builder.bus_data_values.unwrap(),
    )
}
