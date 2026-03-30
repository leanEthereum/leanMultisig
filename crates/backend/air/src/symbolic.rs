// cf https://github.com/Plonky3/Plonky3/blob/main/uni-stark/src/symbolic_builder.rs

use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::cell::RefCell;
use std::sync::atomic::{AtomicU32, Ordering};

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

/// Opaque handle into the thread-local symbolic arena.
///
/// Handles are scoped to a specific arena (thread) and generation (clear cycle).
/// Using a handle from a different thread or after the arena has been cleared will
/// produce a deterministic error instead of undefined behaviour.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolicNodeRef<F> {
    arena_id: u32,
    generation: u32,
    offset: u32,
    _phantom: PhantomData<fn() -> F>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SymbolicNodeAccessError {
    WrongArena,
    StaleGeneration,
    OutOfBounds,
}

impl core::fmt::Display for SymbolicNodeAccessError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::WrongArena => {
                write!(f, "symbolic node handle belongs to a different thread's arena")
            }
            Self::StaleGeneration => {
                write!(f, "symbolic node handle is stale (arena was cleared)")
            }
            Self::OutOfBounds => write!(f, "symbolic node handle offset is out of bounds"),
        }
    }
}

impl std::error::Error for SymbolicNodeAccessError {}

#[derive(Debug)]
struct ArenaState {
    arena_id: u32,
    generation: u32,
    bytes: Vec<u8>,
}

impl ArenaState {
    fn new() -> Self {
        Self {
            arena_id: NEXT_ARENA_ID.fetch_add(1, Ordering::Relaxed),
            generation: 0,
            bytes: Vec::new(),
        }
    }
}

static NEXT_ARENA_ID: AtomicU32 = AtomicU32::new(1);

// We use an arena as a trick to allow SymbolicExpression to be Copy.
// Handles carry arena_id + generation so that stale or cross-thread use
// is caught deterministically instead of reading garbage bytes.
thread_local! {
    static ARENA: RefCell<ArenaState> = RefCell::new(ArenaState::new());
}

fn clear_arena() {
    ARENA.with(|arena| {
        let mut state = arena.borrow_mut();
        state.generation = state
            .generation
            .checked_add(1)
            .expect("symbolic arena generation overflow");
        state.bytes.clear();
    });
}

fn alloc_node<F: Field>(node: SymbolicNode<F>) -> SymbolicNodeRef<F> {
    ARENA.with(|arena| {
        let mut state = arena.borrow_mut();
        let node_size = std::mem::size_of::<SymbolicNode<F>>();
        let offset = state.bytes.len();
        let offset_u32 = u32::try_from(offset).expect("symbolic arena exceeded u32::MAX bytes");
        let end = offset
            .checked_add(node_size)
            .expect("symbolic arena allocation overflow");
        state.bytes.resize(end, 0);
        // SAFETY: We just resized the buffer to `end` bytes, so `offset..end` is valid.
        unsafe {
            std::ptr::write_unaligned(
                state.bytes.as_mut_ptr().add(offset).cast::<SymbolicNode<F>>(),
                node,
            );
        }
        SymbolicNodeRef {
            arena_id: state.arena_id,
            generation: state.generation,
            offset: offset_u32,
            _phantom: PhantomData,
        }
    })
}

pub fn try_get_node<F: Field>(
    handle: SymbolicNodeRef<F>,
) -> Result<SymbolicNode<F>, SymbolicNodeAccessError> {
    ARENA.with(|arena| {
        let state = arena.borrow();
        if state.arena_id != handle.arena_id {
            return Err(SymbolicNodeAccessError::WrongArena);
        }
        if state.generation != handle.generation {
            return Err(SymbolicNodeAccessError::StaleGeneration);
        }
        let offset = handle.offset as usize;
        let node_size = std::mem::size_of::<SymbolicNode<F>>();
        let end = offset
            .checked_add(node_size)
            .ok_or(SymbolicNodeAccessError::OutOfBounds)?;
        if end > state.bytes.len() {
            return Err(SymbolicNodeAccessError::OutOfBounds);
        }
        // SAFETY: We verified that `offset..end` is within the arena buffer.
        Ok(unsafe {
            std::ptr::read_unaligned(
                state.bytes.as_ptr().add(offset).cast::<SymbolicNode<F>>(),
            )
        })
    })
}

pub fn get_node<F: Field>(handle: SymbolicNodeRef<F>) -> SymbolicNode<F> {
    try_get_node(handle).expect("invalid or stale symbolic node handle")
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SymbolicExpression<F: Copy> {
    Variable(SymbolicVariable<F>),
    Constant(F),
    Operation(SymbolicNodeRef<F>),
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
    clear_arena();

    let mut builder = SymbolicAirBuilder::<F>::new(air.n_columns(), air.n_down_columns());
    air.eval(&mut builder, &Default::default());
    (
        builder.constraints(),
        builder.bus_flag_value.unwrap(),
        builder.bus_data_values.unwrap(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use koala_bear::KoalaBear;

    type F = KoalaBear;

    const _: () = {
        const fn assert_copy<T: Copy>() {}
        assert_copy::<SymbolicExpression<F>>();
        assert_copy::<SymbolicNodeRef<F>>();
    };

    #[test]
    fn roundtrip_alloc_get() {
        clear_arena();
        let a = SymbolicExpression::<F>::Constant(F::ONE);
        let b = SymbolicExpression::<F>::Constant(F::TWO);
        let handle = alloc_node(SymbolicNode {
            op: SymbolicOperation::Add,
            lhs: a,
            rhs: b,
        });
        let node = get_node::<F>(handle);
        assert_eq!(node.op, SymbolicOperation::Add);
        assert_eq!(node.lhs, a);
        assert_eq!(node.rhs, b);
    }

    #[test]
    fn stale_handle_rejected_after_clear() {
        clear_arena();
        let handle = alloc_node(SymbolicNode {
            op: SymbolicOperation::Mul,
            lhs: SymbolicExpression::<F>::ONE,
            rhs: SymbolicExpression::<F>::TWO,
        });
        assert!(try_get_node::<F>(handle).is_ok());
        clear_arena();
        assert!(
            matches!(try_get_node::<F>(handle), Err(SymbolicNodeAccessError::StaleGeneration))
        );
    }

    #[test]
    fn old_handle_cannot_read_new_generation_bytes() {
        clear_arena();
        let old_handle = alloc_node(SymbolicNode {
            op: SymbolicOperation::Add,
            lhs: SymbolicExpression::<F>::ONE,
            rhs: SymbolicExpression::<F>::TWO,
        });
        clear_arena();
        let _new_handle = alloc_node(SymbolicNode {
            op: SymbolicOperation::Sub,
            lhs: SymbolicExpression::<F>::ZERO,
            rhs: SymbolicExpression::<F>::ONE,
        });
        assert!(
            matches!(try_get_node::<F>(old_handle), Err(SymbolicNodeAccessError::StaleGeneration))
        );
    }

    #[test]
    fn wrong_thread_handle_rejected() {
        clear_arena();
        let handle = alloc_node(SymbolicNode {
            op: SymbolicOperation::Neg,
            lhs: SymbolicExpression::<F>::ONE,
            rhs: SymbolicExpression::<F>::ZERO,
        });
        let result = std::thread::spawn(move || try_get_node::<F>(handle))
            .join()
            .unwrap();
        assert!(matches!(result, Err(SymbolicNodeAccessError::WrongArena)));
    }

    #[test]
    fn out_of_bounds_handle_rejected() {
        clear_arena();
        let bogus = SymbolicNodeRef::<F> {
            arena_id: ARENA.with(|a| a.borrow().arena_id),
            generation: ARENA.with(|a| a.borrow().generation),
            offset: 999_999,
            _phantom: PhantomData,
        };
        assert!(matches!(
            try_get_node::<F>(bogus),
            Err(SymbolicNodeAccessError::OutOfBounds)
        ));
    }

    #[test]
    fn offset_truncation_detected() {
        fn checked_offset(len: usize) -> u32 {
            u32::try_from(len).expect("symbolic arena exceeded u32::MAX bytes")
        }
        assert!(std::panic::catch_unwind(|| checked_offset(u32::MAX as usize + 1)).is_err());
    }

    #[test]
    fn arithmetic_produces_valid_handles() {
        clear_arena();
        let var = SymbolicExpression::<F>::Variable(SymbolicVariable::new(0));
        let c = SymbolicExpression::<F>::Constant(F::TWO);
        let sum = var + c;
        if let SymbolicExpression::Operation(handle) = sum {
            let node = get_node::<F>(handle);
            assert_eq!(node.op, SymbolicOperation::Add);
            assert_eq!(node.lhs, var);
            assert_eq!(node.rhs, c);
        } else {
            panic!("expected Operation variant from variable + constant");
        }

        let neg = -var;
        if let SymbolicExpression::Operation(handle) = neg {
            let node = get_node::<F>(handle);
            assert_eq!(node.op, SymbolicOperation::Neg);
            assert_eq!(node.lhs, var);
        } else {
            panic!("expected Operation variant from neg(variable)");
        }
    }
}
