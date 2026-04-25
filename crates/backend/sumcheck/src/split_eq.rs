use field::{ExtensionField, PackedFieldExtension};
use poly::*;

pub struct SplitEq<EF: ExtensionField<PF<EF>>> {
    pub eq_lo: Vec<EF>,
    pub eq_hi_packed: Vec<EFPacking<EF>>,
    pub log_packed_hi: u32, // = log2(eq_hi_packed.len()), cached for bit-shift in get_packed
    /// Unpacked remainder for when the packed table is empty or exhausted.
    pub remainder: Vec<EF>,
}

impl<EF: ExtensionField<PF<EF>>> SplitEq<EF> {
    pub fn new(eq_point: &[EF]) -> Self {
        let n = eq_point.len();

        if must_unpack_multilinears::<EF>(n + 1) {
            return Self {
                eq_lo: vec![EF::ONE],
                eq_hi_packed: Vec::new(),
                log_packed_hi: 0,
                remainder: eval_eq(eq_point),
            };
        }

        let hi_vars = (n / 2).max(packing_log_width::<EF>().max(1));
        let mid = n - hi_vars;
        let eq_lo = eval_eq(&eq_point[..mid]);
        let eq_hi_packed = eval_eq_packed(&eq_point[mid..]);
        let log_packed_hi = eq_hi_packed.len().trailing_zeros();
        Self {
            eq_lo,
            eq_hi_packed,
            log_packed_hi,
            remainder: Vec::new(),
        }
    }

    #[inline]
    pub fn is_remainder_mode(&self) -> bool {
        !self.remainder.is_empty() || self.eq_hi_packed.is_empty()
    }

    #[inline]
    pub fn truncate_half(&mut self) {
        if self.eq_lo.len() > 1 {
            self.eq_lo.truncate(self.eq_lo.len() / 2);
        } else if !self.remainder.is_empty() {
            self.remainder.truncate(self.remainder.len() / 2);
        } else if self.eq_hi_packed.len() > 1 {
            let new_len = self.eq_hi_packed.len() / 2;
            self.eq_hi_packed.truncate(new_len);
            self.log_packed_hi = new_len.trailing_zeros();
        } else {
            // eq_hi_packed has 0 or 1 element — unpack to remainder and halve
            let mut unpacked: Vec<EF> = EFPacking::<EF>::to_ext_iter(self.eq_hi_packed.iter().copied()).collect();
            let scale = self.eq_lo[0];
            for v in &mut unpacked {
                *v *= scale;
            }
            self.eq_lo[0] = EF::ONE;
            unpacked.truncate(unpacked.len() / 2);
            self.remainder = unpacked;
            self.eq_hi_packed.clear();
        }
    }

    #[inline]
    pub fn n_lo(&self) -> usize {
        self.eq_lo.len()
    }

    #[inline]
    pub fn packed_hi(&self) -> usize {
        self.eq_hi_packed.len()
    }

    #[inline(always)]
    pub fn get_packed(&self, i: usize) -> EFPacking<EF> {
        assert!(!self.is_remainder_mode(), "get_packed called in remainder mode");
        let packed_hi = self.eq_hi_packed.len();
        if self.eq_lo.len() > 1 {
            EFPacking::<EF>::from(self.eq_lo[i >> self.log_packed_hi]) * self.eq_hi_packed[i & (packed_hi - 1)]
        } else {
            self.eq_hi_packed[i] * self.eq_lo[0]
        }
    }

    #[inline(always)]
    pub fn get_unpacked(&self, i: usize) -> EF {
        if self.is_remainder_mode() {
            if self.remainder.is_empty() {
                EF::ONE
            } else {
                self.remainder[i] * self.eq_lo[0]
            }
        } else {
            let width = packing_width::<EF>();
            let packed_val = self.get_packed(i / width);
            EFPacking::<EF>::to_ext_iter([packed_val]).nth(i % width).unwrap()
        }
    }
}
