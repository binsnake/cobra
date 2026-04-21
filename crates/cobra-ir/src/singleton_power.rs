//! Per-variable univariate polynomials in the factorial basis.
//!
//! actual recovery pass lives in `cobra-passes`.

/// One nonzero factorial-basis term: `coeff * x_(degree)` where
/// `x_(k) = x * (x-1) * … * (x-k+1)` is the falling factorial.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnivariateTerm {
    pub degree: u16,
    /// Reduced modulo `2^(bitwidth - twos_in_factorial(degree))`.
    pub coeff: u64,
}

/// Univariate polynomial in factorial basis, normalized:
/// - terms sorted by strictly increasing `degree`
/// - `degree` unique across terms
/// - `1 <= degree < degree_cap(bitwidth)`
/// - `0 < coeff < 2^(bitwidth - twos_in_factorial(degree))`
///
/// Degree 0 is excluded — the constant is held by the enclosing
/// coefficient-splitting data (see the passes crate).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct UnivariateNormalizedPoly {
    pub bitwidth: u32,
    pub terms: Vec<UnivariateTerm>,
}

/// Singleton-power recovery result: one univariate poly per variable.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SingletonPowerResult {
    pub num_vars: u32,
    pub bitwidth: u32,
    /// Length equals `num_vars`. An empty `terms` vector means that variable
    /// has no singleton-power contribution beyond what the bitwise basis
    /// already captures.
    pub per_var: Vec<UnivariateNormalizedPoly>,
}

impl UnivariateNormalizedPoly {
    /// Check normalization invariants. Does not validate coefficient
    /// magnitude — that requires `math_utils::twos_in_factorial`, which
    /// callers can easily add if they want full validation.
    #[must_use]
    pub fn is_sorted_and_unique(&self) -> bool {
        self.terms.windows(2).all(|w| w[0].degree < w[1].degree)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sorted_and_unique_check() {
        let p = UnivariateNormalizedPoly {
            bitwidth: 64,
            terms: vec![
                UnivariateTerm {
                    degree: 1,
                    coeff: 2,
                },
                UnivariateTerm {
                    degree: 3,
                    coeff: 5,
                },
                UnivariateTerm {
                    degree: 4,
                    coeff: 7,
                },
            ],
        };
        assert!(p.is_sorted_and_unique());

        let bad = UnivariateNormalizedPoly {
            bitwidth: 64,
            terms: vec![
                UnivariateTerm {
                    degree: 3,
                    coeff: 1,
                },
                UnivariateTerm {
                    degree: 1,
                    coeff: 1,
                },
            ],
        };
        assert!(!bad.is_sorted_and_unique());

        let dup = UnivariateNormalizedPoly {
            bitwidth: 64,
            terms: vec![
                UnivariateTerm {
                    degree: 2,
                    coeff: 1,
                },
                UnivariateTerm {
                    degree: 2,
                    coeff: 4,
                },
            ],
        };
        assert!(!dup.is_sorted_and_unique());
    }

    #[test]
    fn default_is_empty() {
        let p = UnivariateNormalizedPoly::default();
        assert_eq!(p.bitwidth, 0);
        assert!(p.terms.is_empty());
        assert!(p.is_sorted_and_unique());
    }
}
