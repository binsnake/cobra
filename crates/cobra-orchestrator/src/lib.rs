//! `CoBRA` worklist scheduler.
//!
//! This crate owns the state-machine shape of the simplification
//! pipeline: [`WorkItem`] payloads, the [`StateKind`] discriminator,
//! competition groups, join states, continuations, and the dispatch
//! tables the scheduler consults. Individual pass implementations live
//! in `cobra-passes`; this crate provides the types they produce and
//! consume.
//!
//! The scheduler logic (`select_next_pass`, `compute_fingerprint`,
//! `release_handle`, `run_simplify`, etc.) is added in a follow-up.
//! The data layer exposed here is already sufficient for `cobra-passes`
//! to start building against.

#![forbid(unsafe_code)]

pub mod attempt_cache;
pub mod competition;
pub mod context;
pub mod continuation;
pub mod entry;
pub mod enums;
pub mod fingerprint;
pub mod join;
pub mod main_loop;
pub mod ranker;
pub mod registry;
pub mod scheduler;
pub mod state;
pub mod stubs;
pub mod work_item;
pub mod worklist;

pub use crate::attempt_cache::PassAttemptCache;
pub use crate::competition::{
    acquire_handle, create_group, group_has_verified_candidate, has_verified_candidate,
    release_handle, submit_candidate, CandidateRecord, CompetitionGroup, GroupMap, JoinId,
};
pub use crate::context::{
    determinism_seeds, determinism_seeds_ahash, expr_identity_hash, OrchestratorContext,
    OrchestratorPolicy, OrchestratorTelemetry, RunMetadata,
};
pub use crate::continuation::{
    project_baseline_for_child, BitwiseComposeCont, ContinuationData, FactorRole, GroupId,
    HybridComposeCont, LiftedBinding, LiftedSubstituteCont, LiftedValueKind, OperandRewriteCont,
    OperandRole, ProductCollapseCont, RemainderRecombineCont,
};
pub use crate::entry::{simplify_from_worklist, to_simplify_outcome};
pub use crate::enums::{
    project_extractor_kind, ItemDisposition, PassDecision, PassId, PassTag, Provenance,
    RemainderOrigin, StateKind,
};
pub use crate::fingerprint::{
    build_semilinear_fingerprint_key, compute_fingerprint, hash_combine,
    hash_semilinear_fingerprint_key,
};
pub use crate::join::{
    create_join, replace_by_hash, JoinMap, JoinState, OperandJoinState, ProductJoinState,
};
pub use crate::main_loop::{run_main_loop, LoopResult};
pub use crate::ranker::unsupported_rank_better;
pub use crate::registry::{pass_registry, ApplicabilityFn, PassDescriptor, PassFn};
pub use crate::scheduler::select_next_pass;
pub use crate::state::{
    AstPayload, AstSolveContext, CandidatePayload, CheckedSemilinearPayload,
    CompetitionResolvedPayload, CoreCandidatePayload, LiftedSkeletonPayload,
    NormalizedSemilinearPayload, RemainderStatePayload, RemainderTargetContext,
    RewrittenSemilinearPayload, SemilinearContext, SignatureCoeffStatePayload,
    SignatureStatePayload, SignatureSubproblemContext, StateData,
};
pub use crate::stubs::{EliminationResult, ExtractOp, ExtractorKind, GateKind, ResidualSolverKind};
pub use crate::work_item::{
    ItemMetadata, PassResult, SemilinearFingerprintKey, SemilinearTermKey, StateFeatures,
    StateFingerprint, TransformTerminalSignal, UnsupportedCandidate, WorkItem,
};
pub use crate::worklist::{is_better_priority, Worklist};
pub use cobra_verify::{ExprPath, LeanCertificate, LeanSignatureCertificate, LeanTheorem};
