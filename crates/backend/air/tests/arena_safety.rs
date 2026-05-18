// Tests for arena bounds checking in symbolic expression handling.
// Addresses issue #170: unchecked arena index enables out-of-bounds reads.

use field::PrimeCharacteristicRing;
use koala_bear::KoalaBear;
use mt_air::{SymbolicExpression, get_node};

type F = KoalaBear;

#[test]
#[should_panic(expected = "arena out-of-bounds")]
fn get_node_oob_panics_on_empty_arena() {
    // Constructing Operation(0) on an empty arena must panic with a bounds
    // check, not trigger undefined behavior via read_unaligned.
    let _: mt_air::SymbolicNode<F> = get_node(0);
}

#[test]
#[should_panic(expected = "arena out-of-bounds")]
fn get_node_oob_panics_on_large_index() {
    // A fabricated large index must be caught by the bounds check.
    let _: mt_air::SymbolicNode<F> = get_node(u32::MAX);
}

#[test]
fn alloc_and_get_node_roundtrip() {
    // Building a real expression through arithmetic triggers alloc_node
    // internally. The resulting Operation index must be readable.
    let a = SymbolicExpression::<F>::Variable(mt_air::SymbolicVariable::new(0));
    let b = SymbolicExpression::<F>::Variable(mt_air::SymbolicVariable::new(1));
    let sum = a + b;

    if let SymbolicExpression::Operation(idx) = sum {
        let node = get_node::<F>(idx);
        assert_eq!(node.op, mt_air::SymbolicOperation::Add);
    } else {
        panic!("expected Operation variant from variable addition");
    }
}

#[test]
fn nested_expression_indices_are_valid() {
    // Multiple levels of nesting must all produce valid arena indices.
    let a = SymbolicExpression::<F>::Variable(mt_air::SymbolicVariable::new(0));
    let b = SymbolicExpression::<F>::Constant(F::TWO);
    let c = SymbolicExpression::<F>::Variable(mt_air::SymbolicVariable::new(1));

    // (a * b) + c — two alloc_node calls
    let product = a * b;
    let sum = product + c;

    if let SymbolicExpression::Operation(idx) = sum {
        let node = get_node::<F>(idx);
        assert_eq!(node.op, mt_air::SymbolicOperation::Add);
        // The lhs should be the product Operation
        if let SymbolicExpression::Operation(mul_idx) = node.lhs {
            let mul_node = get_node::<F>(mul_idx);
            assert_eq!(mul_node.op, mt_air::SymbolicOperation::Mul);
        } else {
            panic!("expected Operation for nested lhs");
        }
    } else {
        panic!("expected Operation variant from nested expression");
    }
}

#[test]
fn constant_folding_bypasses_arena() {
    // Constant + Constant should fold without arena allocation.
    let a = SymbolicExpression::<F>::Constant(F::ONE);
    let b = SymbolicExpression::<F>::Constant(F::TWO);
    let sum = a + b;

    assert!(matches!(sum, SymbolicExpression::Constant(_)));
}
