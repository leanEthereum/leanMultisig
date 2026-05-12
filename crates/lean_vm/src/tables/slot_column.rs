//! A `Vec<F>`-like column buffer that is either owned or backed by a borrowed slot.
//!
//! The slot-backed variant points into one big stacked-PCS polynomial pre-allocated by
//! the prover, so VM execution writes the final stacked layout directly with no
//! per-column memcpy at commit time. The owned variant exists so callers without
//! pre-known sizes (tests, the simple runner entry point) keep working unchanged.
//!
//! `SlotColumn` deliberately has no lifetime parameter — the slot-backed invariant
//! ("backing buffer outlives every `SlotColumn` built from it") is upheld manually,
//! in practice by declaring the buffer before the columns in the same scope.

use crate::F;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

/// Panic marker emitted when a slot-backed `SlotColumn` is asked to grow past its capacity.
/// Used by `lean_prover::prove_execution_hinted` to distinguish "hint under-estimated" panics
/// (recoverable: fall back to dry-run + retry) from genuine prover bugs (propagated).
pub const SLOT_OVERFLOW_PANIC_MARKER: &str = "leanMultisig:slot-column-overflow";

pub enum SlotColumn {
    Owned(Vec<F>),
    /// Backed by an external `&mut [F]` slot.
    ///
    /// SAFETY invariant: `ptr..ptr+cap` is a live, exclusive, properly aligned region
    /// for the lifetime of this `SlotColumn`.
    Slot {
        ptr: NonNull<F>,
        len: usize,
        cap: usize,
    },
}

// SAFETY: behaves like a `Vec<F>` or a `&mut [F]` slot (Send+Sync for `F`).
unsafe impl Send for SlotColumn {}
unsafe impl Sync for SlotColumn {}

impl Default for SlotColumn {
    fn default() -> Self {
        Self::Owned(Vec::new())
    }
}

impl SlotColumn {
    pub fn new() -> Self {
        Self::Owned(Vec::new())
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self::Owned(Vec::with_capacity(cap))
    }

    /// Wrap a borrowed slot. Length starts at 0; capacity equals `slot.len()`.
    ///
    /// # Safety
    /// The buffer backing `slot` must outlive every operation on the returned column.
    #[inline]
    pub unsafe fn from_slot(slot: &mut [F]) -> Self {
        let cap = slot.len();
        let ptr = NonNull::new(slot.as_mut_ptr()).unwrap_or(NonNull::dangling());
        Self::Slot { ptr, len: 0, cap }
    }

    /// Wrap a borrowed slot, treating its first `initial_len` elements as already initialized.
    /// Length starts at `initial_len`; capacity equals `slot.len()`.
    ///
    /// # Safety
    /// The buffer backing `slot` must outlive every operation on the returned column, AND the
    /// caller must have initialized positions `0..initial_len` of `slot`.
    #[inline]
    pub unsafe fn from_slot_with_len(slot: &mut [F], initial_len: usize) -> Self {
        let cap = slot.len();
        assert!(initial_len <= cap);
        let ptr = NonNull::new(slot.as_mut_ptr()).unwrap_or(NonNull::dangling());
        Self::Slot {
            ptr,
            len: initial_len,
            cap,
        }
    }

    #[inline]
    pub fn push(&mut self, val: F) {
        match self {
            Self::Owned(v) => v.push(val),
            Self::Slot { ptr, len, cap } => {
                // `assert!` (not `debug_assert!`) so that under-sized slot hints in the prover's
                // direct-write path can be caught & recovered from via `catch_unwind` in release.
                assert!(*len < *cap, "{SLOT_OVERFLOW_PANIC_MARKER}: push ({len} >= {cap})");
                // SAFETY: bounds checked; ptr+len is within the slot per the invariant.
                unsafe { ptr.as_ptr().add(*len).write(val) };
                *len += 1;
            }
        }
    }

    pub fn extend_from_iter<I: IntoIterator<Item = F>>(&mut self, iter: I) {
        for v in iter {
            self.push(v);
        }
    }

    #[inline]
    pub fn extend_from_slice(&mut self, slice: &[F]) {
        match self {
            Self::Owned(v) => v.extend_from_slice(slice),
            Self::Slot { ptr, len, cap } => {
                let new_len = *len + slice.len();
                assert!(
                    new_len <= *cap,
                    "{SLOT_OVERFLOW_PANIC_MARKER}: extend_from_slice ({new_len} > cap {cap})"
                );
                // SAFETY: bounds checked above; positions [*len, new_len) are within the slot.
                unsafe {
                    std::ptr::copy_nonoverlapping(slice.as_ptr(), ptr.as_ptr().add(*len), slice.len());
                }
                *len = new_len;
            }
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::Owned(v) => v.len(),
            Self::Slot { len, .. } => *len,
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        match self {
            Self::Owned(v) => v.capacity(),
            Self::Slot { cap, .. } => *cap,
        }
    }

    pub fn resize(&mut self, new_len: usize, val: F) {
        match self {
            Self::Owned(v) => v.resize(new_len, val),
            Self::Slot { ptr, len, cap } => {
                assert!(
                    new_len <= *cap,
                    "{SLOT_OVERFLOW_PANIC_MARKER}: resize {new_len} > cap {cap}"
                );
                if new_len > *len {
                    // SAFETY: positions in [*len, new_len) are within the slot.
                    unsafe {
                        for i in *len..new_len {
                            ptr.as_ptr().add(i).write(val);
                        }
                    }
                }
                *len = new_len;
            }
        }
    }

    #[inline]
    pub fn as_slice(&self) -> &[F] {
        match self {
            Self::Owned(v) => v.as_slice(),
            // SAFETY: ptr..ptr+len was initialized and is within the slot.
            Self::Slot { ptr, len, .. } => unsafe { std::slice::from_raw_parts(ptr.as_ptr(), *len) },
        }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [F] {
        match self {
            Self::Owned(v) => v.as_mut_slice(),
            // SAFETY: same as as_slice; `&mut self` gates exclusive access.
            Self::Slot { ptr, len, .. } => unsafe { std::slice::from_raw_parts_mut(ptr.as_ptr(), *len) },
        }
    }
}

impl Deref for SlotColumn {
    type Target = [F];
    #[inline]
    fn deref(&self) -> &[F] {
        self.as_slice()
    }
}

impl DerefMut for SlotColumn {
    #[inline]
    fn deref_mut(&mut self) -> &mut [F] {
        self.as_mut_slice()
    }
}

impl std::borrow::Borrow<[F]> for SlotColumn {
    #[inline]
    fn borrow(&self) -> &[F] {
        self.as_slice()
    }
}

impl std::fmt::Debug for SlotColumn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlotColumn")
            .field("len", &self.len())
            .field("cap", &self.capacity())
            .finish()
    }
}

impl Clone for SlotColumn {
    fn clone(&self) -> Self {
        // Clones always detach to an owned buffer (slot-backed Vec aliasing is unsafe).
        Self::Owned(self.as_slice().to_vec())
    }
}

impl<'a> IntoIterator for &'a SlotColumn {
    type Item = &'a F;
    type IntoIter = std::slice::Iter<'a, F>;
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl IntoIterator for SlotColumn {
    type Item = F;
    type IntoIter = std::vec::IntoIter<F>;
    fn into_iter(self) -> Self::IntoIter {
        // Detach into an owned Vec; only sensible for the Owned variant.
        match self {
            Self::Owned(v) => v.into_iter(),
            Self::Slot { .. } => self.as_slice().to_vec().into_iter(),
        }
    }
}

impl Extend<F> for SlotColumn {
    fn extend<I: IntoIterator<Item = F>>(&mut self, iter: I) {
        for v in iter {
            self.push(v);
        }
    }
}
