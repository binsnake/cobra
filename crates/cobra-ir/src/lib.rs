//! Intermediate representations for the `CoBRA` pipeline.
//!
//! Each IR corresponds to one of the secondary forms used by different
//! pass families. All of them build on top of `cobra-core`'s `Expr`.

#![forbid(unsafe_code)]
// Expr-building helpers return `Box<Expr>` to match the ownership shape
// of `cobra_core::Expr` factories.
#![allow(clippy::unnecessary_box_returns)]

pub mod anf_cleanup;
pub mod anf_transform;
pub mod arithmetic_lowering;
pub mod basis_transform;
pub mod coeff_interpolator;
pub mod coefficient_splitter;
pub mod dynamic_mask;
pub mod masked_atom_reconstructor;
pub mod math_utils;
pub mod mono;
pub mod multivar_poly_recovery;
pub mod packed_anf;
pub mod poly;
pub mod poly_expr_builder;
pub mod poly_normalizer;
pub mod semilinear;
pub mod semilinear_normalizer;
pub mod semilinear_signature;
pub mod singleton_power;
pub mod singleton_power_recovery;
pub mod structure_recovery;
pub mod term_refiner;

pub use crate::anf_cleanup::{anf_expr_cost, build_anf_expr, cleanup_anf, emit_raw_anf, AnfForm};
pub use crate::anf_transform::compute_anf;
pub use crate::arithmetic_lowering::{lower_arithmetic_fragment, LoweringResult};
pub use crate::basis_transform::{to_factorial_basis, to_monomial_basis};
pub use crate::coeff_interpolator::{interpolate_coefficients, interpolate_coefficients_in_place};
pub use crate::coefficient_splitter::{mod_inverse_odd_half, split_coefficients, SplitResult};
pub use crate::dynamic_mask::{
    contains_shr, detect_root_low_bit_mask, is_power_of_two_minus_one, MaskInfo,
};
pub use crate::masked_atom_reconstructor::reconstruct_masked_atoms;
pub use crate::math_utils::{
    build_stirling_first_kind, build_stirling_second_kind, degree_cap, mod_inverse_odd,
    odd_part_factorial, twos_in_factorial,
};
pub use crate::mono::{MonomialKey, MAX_POLY_VARS};
pub use crate::multivar_poly_recovery::{
    probe_grid_check, recover_and_verify_poly, recover_multivar_poly, PolyRecoveryResult,
};
pub use crate::packed_anf::PackedAnf;
pub use crate::poly::{Coeff, CoeffMap, NormalizedPoly, PolyIR};
pub use crate::poly_expr_builder::build_poly_expr;
pub use crate::poly_normalizer::normalize_polynomial;
pub use crate::semilinear::{
    compact_atom_table, compute_atom_truth_table, create_atom, decompose_atom, structural_hash,
    AtomId, AtomInfo, AtomKey, AtomSemanticId, Decomposed, GlobalVarIdx, OperatorFamily,
    PartitionClass, SemilinearIR, WeightedAtom,
};
pub use crate::semilinear_normalizer::normalize_to_semilinear;
pub use crate::semilinear_signature::{evaluate_semilinear_row, is_linear_shortcut};
pub use crate::singleton_power::{SingletonPowerResult, UnivariateNormalizedPoly, UnivariateTerm};
pub use crate::singleton_power_recovery::recover_singleton_powers;
pub use crate::structure_recovery::{coalesce_terms, flatten_complex_atoms, recover_structure};
pub use crate::term_refiner::{
    can_change_coefficient_to, can_change_mask_to, reduce_mask, refine_terms,
};
