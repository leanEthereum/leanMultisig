// Tests for checked arithmetic in memory address computation.
// Addresses issue #176: fp+offset overflow enables wrong memory access.

use backend::PrimeCharacteristicRing;
use lean_vm::{F, MemOrConstant, MemOrFpOrConstant, Memory, RunnerError};

#[test]
fn read_value_overflow_returns_error() {
    // fp + offset that overflows usize must return AddressOverflow, not wrap.
    let mem = Memory::new(vec![F::ONE; 16]);
    let operand = MemOrConstant::MemoryAfterFp { offset: usize::MAX };
    let fp = 1usize;

    let result = operand.read_value(&mem, fp);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), RunnerError::AddressOverflow);
}

#[test]
fn memory_address_overflow_returns_error() {
    let operand = MemOrConstant::MemoryAfterFp { offset: usize::MAX };
    let fp = 1usize;

    let result = operand.memory_address(fp);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), RunnerError::AddressOverflow);
}

#[test]
fn read_value_no_overflow_works() {
    // Normal operation: fp=4, offset=2 → address 6 → reads mem[6].
    let mut data = vec![F::ZERO; 8];
    data[6] = F::from_u32(42);
    let mem = Memory::new(data);
    let operand = MemOrConstant::MemoryAfterFp { offset: 2 };

    let result = operand.read_value(&mem, 4);
    assert_eq!(result.unwrap(), F::from_u32(42));
}

#[test]
fn memory_address_no_overflow_works() {
    let operand = MemOrConstant::MemoryAfterFp { offset: 10 };
    assert_eq!(operand.memory_address(5).unwrap(), 15);
}

#[test]
fn constant_read_ignores_fp() {
    // Constants don't compute addresses, so overflow is irrelevant.
    let mem = Memory::new(vec![F::ZERO; 4]);
    let operand = MemOrConstant::Constant(F::from_u32(99));

    let result = operand.read_value(&mem, usize::MAX);
    assert_eq!(result.unwrap(), F::from_u32(99));
}

#[test]
fn is_value_unknown_with_overflow() {
    // Overflow makes the value "unknown" (returns error → true).
    let mem = Memory::new(vec![F::ONE; 4]);
    let operand = MemOrConstant::MemoryAfterFp { offset: usize::MAX };
    assert!(operand.is_value_unknown(&mem, 1));
}

// --- MemOrFpOrConstant: same overflow pattern ---

#[test]
fn fp_or_constant_memory_read_overflow() {
    let mem = Memory::new(vec![F::ONE; 16]);
    let operand = MemOrFpOrConstant::MemoryAfterFp { offset: usize::MAX };
    assert_eq!(operand.read_value(&mem, 1).unwrap_err(), RunnerError::AddressOverflow);
}

#[test]
fn fp_or_constant_fp_relative_overflow() {
    // FpRelative computes fp + offset as a field element value, not a memory address.
    // Overflow must still be caught before the conversion.
    let mem = Memory::new(vec![F::ONE; 4]);
    let operand = MemOrFpOrConstant::FpRelative { offset: usize::MAX };
    assert_eq!(operand.read_value(&mem, 1).unwrap_err(), RunnerError::AddressOverflow);
}

#[test]
fn fp_or_constant_memory_address_overflow() {
    let operand = MemOrFpOrConstant::MemoryAfterFp { offset: usize::MAX };
    assert_eq!(operand.memory_address(1).unwrap_err(), RunnerError::AddressOverflow);
}

#[test]
fn fp_or_constant_normal_operation() {
    let mut data = vec![F::ZERO; 8];
    data[5] = F::from_u32(77);
    let mem = Memory::new(data);
    let operand = MemOrFpOrConstant::MemoryAfterFp { offset: 2 };
    assert_eq!(operand.read_value(&mem, 3).unwrap(), F::from_u32(77));
    assert_eq!(operand.memory_address(3).unwrap(), 5);
}
