use std::ops::{Deref, DerefMut};

use p3_field::PrimeField64;

/// A memory cell used by the VM for storing 64-bit field elements with metadata.
///
/// Internally, the cell holds a single `u64` value.
/// The two most significant bits are reserved as flags:
/// - `BIT63` (NONE_MASK): indicates the cell is empty.
/// - `BIT62` (ACCESS_MASK): marks whether the cell has been accessed.
///
/// The remaining 62 bits store the canonical representation of a field element.
///
/// This design favors simplicity and cache efficiency over expressive power.
#[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd, Debug)]
pub(crate) struct MemoryCell(u64);

impl Deref for MemoryCell {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for MemoryCell {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl MemoryCell {
    /// Flag bit indicating the cell is empty (bit 63 set).
    pub(crate) const NONE_MASK: u64 = 1 << 63;
    /// Flag bit indicating the cell was accessed (bit 62 set).
    pub(crate) const ACCESS_MASK: u64 = 1 << 62;
    /// Constant representing an empty cell.
    pub(crate) const NONE: Self = Self(Self::NONE_MASK);

    /// Creates a `MemoryCell` from a field element, using its canonical `u64` representation.
    ///
    /// This clears any flag bits and assumes the value is valid.
    pub(crate) fn from_f<F>(value: F) -> Self
    where
        F: PrimeField64,
    {
        Self(value.as_canonical_u64())
    }

    /// Creates a raw `MemoryCell` from a `u64` value.
    ///
    /// Caller is responsible for ensuring no flag bits are set unless intentional.
    pub(crate) const fn from_u64(value: u64) -> Self {
        Self(value)
    }

    /// Returns true if the cell is marked as empty (`NONE`).
    pub(crate) const fn is_none(self) -> bool {
        self.0 & Self::NONE_MASK == Self::NONE_MASK
    }

    /// Returns true if the cell is not marked as empty.
    pub(crate) const fn is_some(self) -> bool {
        !self.is_none()
    }

    /// Marks the cell as accessed by setting the access flag.
    pub(crate) const fn mark_accessed(&mut self) {
        self.0 |= Self::ACCESS_MASK;
    }

    /// Returns true if the cell is marked as accessed.
    pub(crate) const fn is_accessed(self) -> bool {
        self.0 & Self::ACCESS_MASK == Self::ACCESS_MASK
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;

    type F = BabyBear;

    #[test]
    fn test_from_f_and_accessors() {
        let f = F::from_u64(123);
        let cell = MemoryCell::from_f(f);
        assert_eq!(*cell, 123);
        assert!(cell.is_some());
        assert!(!cell.is_none());
        assert!(!cell.is_accessed());
    }

    #[test]
    fn test_from_u64_and_flags() {
        let raw = 0xFFFF_FFFF;
        let cell = MemoryCell::from_u64(raw);
        assert_eq!(*cell, raw);
        assert!(cell.is_some());
        assert!(!cell.is_none());
    }

    #[test]
    fn test_is_none_and_is_some() {
        let none_cell = MemoryCell::NONE;
        assert!(none_cell.is_none());
        assert!(!none_cell.is_some());

        let some_cell = MemoryCell::from_u64(42);
        assert!(!some_cell.is_none());
        assert!(some_cell.is_some());
    }

    #[test]
    fn test_mark_accessed_and_is_accessed() {
        let mut cell = MemoryCell::from_u64(7);
        assert!(!cell.is_accessed());
        cell.mark_accessed();
        assert!(cell.is_accessed());

        // Ensure value bits are still preserved
        assert_eq!(*cell & 0x3FFF_FFFF_FFFF_FFFF, 7);
    }

    #[test]
    fn test_none_and_access_bits_do_not_conflict() {
        let mut cell = MemoryCell::NONE;
        assert!(cell.is_none());
        assert!(!cell.is_accessed());

        // Mark accessed should not clear the NONE flag
        cell.mark_accessed();
        assert!(cell.is_none());
        assert!(cell.is_accessed());
    }
}
