use crate::*;
use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;

#[test]
fn test_basic_memory_operations() {
    let mut memory = Memory::empty();

    // Test setting and getting values
    memory.set(0, F::ONE).unwrap();
    memory.set(5, F::from_usize(42)).unwrap();

    assert_eq!(memory.get(0).unwrap(), F::ONE);
    assert_eq!(memory.get(5).unwrap(), F::from_usize(42));

    // Test undefined memory access
    assert!(matches!(memory.get(1), Err(RunnerError::UndefinedMemory)));
}

#[test]
fn test_memory_already_set_error() {
    let mut memory = Memory::empty();

    memory.set(0, F::ONE).unwrap();
    // Setting same value should work
    memory.set(0, F::ONE).unwrap();

    // Setting different value should fail
    assert!(matches!(
        memory.set(0, F::ZERO),
        Err(RunnerError::MemoryAlreadySet)
    ));
}

#[test]
fn test_extension_field_operations() {
    let mut memory = Memory::empty();

    // Create a simple extension field element with proper dimension
    let mut coeffs = [F::ZERO; DIMENSION];
    coeffs[0] = F::ONE;
    let ef_value = EF::from_basis_coefficients_slice(&coeffs).unwrap();

    memory.set_ef_element(0, ef_value).unwrap();
    let retrieved = memory.get_ef_element(0).unwrap();

    assert_eq!(retrieved, ef_value);

    // Test continuous slice of EF elements
    memory.set_ef_element(DIMENSION, ef_value).unwrap();
    let ef_slice = memory.get_continuous_slice_of_ef_elements(0, 2).unwrap();

    assert_eq!(ef_slice.len(), 2);
    assert_eq!(ef_slice[0], ef_value);
    assert_eq!(ef_slice[1], ef_value);
}
