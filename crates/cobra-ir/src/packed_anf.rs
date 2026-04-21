//! Word-packed bitset for algebraic-normal-form coefficient vectors.
//!
//! little-endian into 64-bit words: bit `i` lives at
//! `words[i / 64] >> (i % 64) & 1`.

/// Fixed-size packed-bit vector.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct PackedAnf {
    words: Vec<u64>,
    size: usize,
}

impl PackedAnf {
    #[must_use]
    pub fn new(n: usize) -> Self {
        let word_count = n.div_ceil(64);
        Self {
            words: vec![0u64; word_count],
            size: n,
        }
    }

    /// initializer-list constructor.
    #[must_use]
    pub fn from_bits<I, T>(bits: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Into<u8>,
    {
        let bits: Vec<u8> = bits.into_iter().map(Into::into).collect();
        let mut anf = Self::new(bits.len());
        for (i, b) in bits.into_iter().enumerate() {
            if b != 0 {
                anf.set(i);
            }
        }
        anf
    }

    #[inline]
    #[must_use]
    pub fn get(&self, i: usize) -> u8 {
        ((self.words[i / 64] >> (i % 64)) & 1) as u8
    }

    #[inline]
    pub fn set(&mut self, i: usize) {
        self.words[i / 64] |= 1u64 << (i % 64);
    }

    #[inline]
    pub fn flip(&mut self, i: usize) {
        self.words[i / 64] ^= 1u64 << (i % 64);
    }

    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.size
    }

    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    #[inline]
    #[must_use]
    pub fn word_count(&self) -> usize {
        self.words.len()
    }

    #[inline]
    #[must_use]
    pub fn word(&self, w: usize) -> u64 {
        self.words[w]
    }

    #[inline]
    pub fn word_mut(&mut self, w: usize) -> &mut u64 {
        &mut self.words[w]
    }

    /// Immutable access to the underlying word slice (useful for SIMD loops).
    #[inline]
    #[must_use]
    pub fn words(&self) -> &[u64] {
        &self.words
    }

    #[inline]
    pub fn words_mut(&mut self) -> &mut [u64] {
        &mut self.words
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_initialized() {
        let a = PackedAnf::new(130);
        assert_eq!(a.len(), 130);
        assert_eq!(a.word_count(), 3); // ceil(130 / 64)
        for i in 0..130 {
            assert_eq!(a.get(i), 0);
        }
    }

    #[test]
    fn set_and_get_across_word_boundary() {
        let mut a = PackedAnf::new(200);
        for &i in &[0usize, 1, 63, 64, 65, 127, 128, 199] {
            a.set(i);
            assert_eq!(a.get(i), 1);
        }
        // Bits not set stay zero.
        assert_eq!(a.get(2), 0);
        assert_eq!(a.get(129), 0);
    }

    #[test]
    fn flip_toggles() {
        let mut a = PackedAnf::new(10);
        a.flip(3);
        assert_eq!(a.get(3), 1);
        a.flip(3);
        assert_eq!(a.get(3), 0);
    }

    #[test]
    fn from_bits_initializer() {
        let a = PackedAnf::from_bits([1u8, 0, 1, 1, 0, 0, 1]);
        assert_eq!(a.len(), 7);
        assert_eq!(a.get(0), 1);
        assert_eq!(a.get(1), 0);
        assert_eq!(a.get(2), 1);
        assert_eq!(a.get(3), 1);
        assert_eq!(a.get(4), 0);
        assert_eq!(a.get(5), 0);
        assert_eq!(a.get(6), 1);
    }

    #[test]
    fn word_mutability() {
        let mut a = PackedAnf::new(128);
        *a.word_mut(1) = 0xF0F0_F0F0_F0F0_F0F0;
        assert_eq!(a.word(1), 0xF0F0_F0F0_F0F0_F0F0);
        assert_eq!(a.get(64), 0);
        assert_eq!(a.get(68), 1);
    }

    #[test]
    fn empty_packed_anf() {
        let a = PackedAnf::new(0);
        assert!(a.is_empty());
        assert_eq!(a.word_count(), 0);
    }
}
