//! Public signature-vector wrapper.

use crate::arith::bitmask;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SignatureVector {
    num_vars: u32,
    bitwidth: u32,
    mask: u64,
}

impl SignatureVector {
    #[must_use]
    pub fn new(num_vars: u32, bitwidth: u32) -> Self {
        assert!(num_vars < 64, "SignatureVector length would overflow");
        Self {
            num_vars,
            bitwidth,
            mask: bitmask(bitwidth),
        }
    }

    #[inline]
    #[must_use]
    pub const fn num_vars(self) -> u32 {
        self.num_vars
    }

    #[inline]
    #[must_use]
    pub const fn bitwidth(self) -> u32 {
        self.bitwidth
    }

    #[inline]
    #[must_use]
    pub const fn len(self) -> usize {
        1usize << self.num_vars
    }

    #[inline]
    #[must_use]
    pub const fn is_empty(self) -> bool {
        false
    }

    #[must_use]
    pub fn from_values(self, mut values: Vec<u64>) -> Vec<u64> {
        for value in &mut values {
            *value &= self.mask;
        }
        values
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn metadata_matches_constructor() {
        let sig = SignatureVector::new(3, 8);
        assert_eq!(sig.num_vars(), 3);
        assert_eq!(sig.bitwidth(), 8);
        assert_eq!(sig.len(), 8);
    }

    #[test]
    fn from_values_masks_to_bitwidth() {
        let sig = SignatureVector::new(2, 4);
        assert_eq!(
            sig.from_values(vec![0, 0x0F, 0x10, 0x1F]),
            vec![0, 15, 0, 15]
        );
    }
}
