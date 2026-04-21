//! Semantic-class and structural-shape tags produced by the AST

/// High-level semantic bucket an expression falls into.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub enum SemanticClass {
    #[default]
    Linear,
    Semilinear,
    Polynomial,
    NonPolynomial,
}

/// bitwise ops are trivial and fingerprints can stay byte-compatible
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct StructuralFlag(pub u32);

impl StructuralFlag {
    pub const NONE: Self = Self(0);

    pub const HAS_BITWISE: Self = Self(1 << 0);
    pub const HAS_ARITHMETIC: Self = Self(1 << 1);
    pub const HAS_MUL: Self = Self(1 << 2);

    pub const HAS_MULTILINEAR_PRODUCT: Self = Self(1 << 3);
    pub const HAS_SINGLETON_POWER: Self = Self(1 << 4);
    pub const HAS_SINGLETON_POWER_GT2: Self = Self(1 << 5);

    pub const HAS_MIXED_PRODUCT: Self = Self(1 << 6);
    pub const HAS_BITWISE_OVER_ARITH: Self = Self(1 << 7);
    pub const HAS_ARITH_OVER_BITWISE: Self = Self(1 << 8);
    pub const HAS_MULTIVAR_HIGH_POWER: Self = Self(1 << 9);
    pub const HAS_UNKNOWN_SHAPE: Self = Self(1 << 10);

    /// Mask of structural shapes the current pass set cannot handle
    /// end-to-end without structural recovery.
    pub const UNSUPPORTED_MASK: Self = Self(
        Self::HAS_MIXED_PRODUCT.0 | Self::HAS_BITWISE_OVER_ARITH.0 | Self::HAS_UNKNOWN_SHAPE.0,
    );

    #[inline]
    #[must_use]
    pub const fn contains(self, f: Self) -> bool {
        (self.0 & f.0) != 0
    }

    #[inline]
    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }
}

impl std::ops::BitOr for StructuralFlag {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for StructuralFlag {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl std::ops::BitAnd for StructuralFlag {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl std::ops::Not for StructuralFlag {
    type Output = Self;
    fn not(self) -> Self {
        Self(!self.0)
    }
}

/// Classifier output: a semantic bucket plus a structural-shape bitset.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Classification {
    pub semantic: SemanticClass,
    pub flags: StructuralFlag,
}

#[must_use]
pub fn needs_structural_recovery(flags: StructuralFlag) -> bool {
    if flags.contains(StructuralFlag::HAS_UNKNOWN_SHAPE) {
        return true;
    }
    if flags.contains(StructuralFlag::HAS_MIXED_PRODUCT) {
        return true;
    }
    if flags.contains(StructuralFlag::HAS_BITWISE_OVER_ARITH)
        && flags.contains(StructuralFlag::HAS_MUL)
    {
        return true;
    }
    false
}

/// every var-var-product shape — mixed (bitwise × arithmetic),
/// bitwise-over-arith, multilinear (`x*y`), multivar high-power
/// (`x²*y`), and singleton power (`x²`). Any of those benefits from
/// the decomposition family (`ExtractProductCore`,
/// `ExtractPolyCoreD2/3/4`), and routing them through the signature
/// path alone misses recoveries like
/// `(x&y)*(x|y) + (x&~y)*(~x&y) − 41  ⇒  x*y − 41`.
#[must_use]
pub fn is_folded_ast_exploration_candidate(flags: StructuralFlag) -> bool {
    if flags.contains(StructuralFlag::HAS_UNKNOWN_SHAPE) {
        return false;
    }
    flags.contains(StructuralFlag::HAS_MIXED_PRODUCT)
        || flags.contains(StructuralFlag::HAS_BITWISE_OVER_ARITH)
        || flags.contains(StructuralFlag::HAS_MULTILINEAR_PRODUCT)
        || flags.contains(StructuralFlag::HAS_MULTIVAR_HIGH_POWER)
        || flags.contains(StructuralFlag::HAS_SINGLETON_POWER)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_classification_is_linear_no_flags() {
        let c = Classification::default();
        assert_eq!(c.semantic, SemanticClass::Linear);
        assert_eq!(c.flags, StructuralFlag::NONE);
    }

    #[test]
    fn bit_ops_set_and_read() {
        let mut f = StructuralFlag::NONE;
        f |= StructuralFlag::HAS_BITWISE;
        f |= StructuralFlag::HAS_MUL;
        assert!(f.contains(StructuralFlag::HAS_BITWISE));
        assert!(f.contains(StructuralFlag::HAS_MUL));
        assert!(!f.contains(StructuralFlag::HAS_ARITHMETIC));

        let cleared = f & !StructuralFlag::HAS_BITWISE;
        assert!(!cleared.contains(StructuralFlag::HAS_BITWISE));
        assert!(cleared.contains(StructuralFlag::HAS_MUL));
    }

    #[test]
    fn unsupported_mask_covers_expected_shapes() {
        let m = StructuralFlag::UNSUPPORTED_MASK;
        assert!(m.contains(StructuralFlag::HAS_MIXED_PRODUCT));
        assert!(m.contains(StructuralFlag::HAS_BITWISE_OVER_ARITH));
        assert!(m.contains(StructuralFlag::HAS_UNKNOWN_SHAPE));
        assert!(!m.contains(StructuralFlag::HAS_MUL));
    }

    #[test]
    fn needs_structural_recovery_predicates() {
        assert!(needs_structural_recovery(StructuralFlag::HAS_UNKNOWN_SHAPE));
        assert!(needs_structural_recovery(StructuralFlag::HAS_MIXED_PRODUCT));
        assert!(needs_structural_recovery(
            StructuralFlag::HAS_BITWISE_OVER_ARITH | StructuralFlag::HAS_MUL
        ));
        // Bitwise-over-arith WITHOUT MUL is not recoverable-required.
        assert!(!needs_structural_recovery(
            StructuralFlag::HAS_BITWISE_OVER_ARITH
        ));
        assert!(!needs_structural_recovery(StructuralFlag::NONE));
    }

    #[test]
    fn folded_ast_candidate_predicate() {
        assert!(is_folded_ast_exploration_candidate(
            StructuralFlag::HAS_MIXED_PRODUCT
        ));
        assert!(is_folded_ast_exploration_candidate(
            StructuralFlag::HAS_BITWISE_OVER_ARITH
        ));
        assert!(!is_folded_ast_exploration_candidate(
            StructuralFlag::HAS_UNKNOWN_SHAPE
        ));
        assert!(!is_folded_ast_exploration_candidate(
            StructuralFlag::HAS_MIXED_PRODUCT | StructuralFlag::HAS_UNKNOWN_SHAPE
        ));
    }
}
