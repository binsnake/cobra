# Interning / hash-consing + signature memoization — design notes

Status: **exploratory.** Captures the design space and open questions for the
next optimization step after the `perf/obfuscatorx-allocs` wins (Arc-shared
`Expr` children `31fb54e`, signature scratch-pool `96d59c4`). Nothing here is
implemented yet. This doc exists so the **persistent cross-solve** option below
isn't lost across sessions — it is the more interesting long-term idea but also
the riskier one.

## Why we're here

obfuscatorx is allocation-bound, and after the Arc change the dominant remaining
cost is **node construction in the rewrite passes** (~10.5k `≤64B` allocs/solve
on the heaviest case) plus repeated **signature evaluation** of the same
subtrees. Both stem from the same root: the search re-builds and re-evaluates
structurally-identical subexpressions over and over, because obfuscatorx
expressions are extremely repetitive (one factor recurs dozens of times per
case, and successive search candidates share most of their structure).

Interning (hash-consing) makes structurally-equal subtrees become the *same*
node, which:
- collapses duplicate **construction** to an id/refcount copy (kills node allocs),
- makes `Eq`/`Hash` **O(1)** (id compare — the codebase already hacks around this
  with `*const Expr`-keyed caches in `join.rs`, `semilinear_normalizer.rs`),
- enables **O(1) signature memoization** (each unique subtree's signature is
  computed once).

## Cost model (the "could it be slower?" question)

Interning is a bet on repetition:
- **Hit** (node already interned): hash a small fixed tuple `(kind, child_id,
  child_id)` — O(1) because children are already ids, not subtrees — then a table
  probe. Returns existing id; **no heap alloc**.
- **Miss** (genuinely new node): same hash+probe, then insert + allocate.

The thing a hit *avoids* (a heap alloc ~70ns, or for the signature memo a whole
subtree-signature recompute ~µs) is much costlier than the thing a miss *adds*
(hash+probe ~15–25ns). So the **break-even hit-rate is low**: ~25–30% for
construction interning, a few percent for signature memo. Fully-unique trees are
the worst case (pure overhead) but are unrealistic for this workload — even a
nominally-distinct expression shares all its leaves and most sub-patterns. The
measurement below quantifies the actual hit rate before we commit.

## Two cache lifetimes

### A. Per-solve interning (the safe default)
Intern within one `simplify()`, discard the table afterward. Hit rate comes from
each expression's **own internal repetition**, which is large for *every*
obfuscatorx case individually — so it pays off per call and is **independent of
how many expressions we process** (no warm-up needed). Bounded memory, no shared
state, trivially thread-safe (each solve owns its table). Captures the bulk of
the obfuscatorx win. **Start here.**

### B. Persistent cross-solve interning (the interesting-but-risky option — KEEP)
The table lives across many `simplify()` calls. In the real embedded use case
(deobfuscating a binary that repeats the same obfuscation templates across
thousands/millions of MBA expressions), structurally-identical *constructions
recur across expressions*, so a persistent table would hit a lot and each repeat
expression would cost close to nothing. This is the version worth exploring for
production throughput.

Risks and the mitigations we want:
- **Unbounded growth** — the table grows with every unique node ever seen. Needs
  a hard memory bound.
  - *Mitigation (user's idea, keep):* a **usage-sorted / hit-counted** cache that
    evicts the **least-hit** entries when over the bound — i.e. keep the nodes
    that actually recur (the obfuscation templates), discard one-off nodes. An
    LRU or LFU (least-frequently-used) eviction with a fixed capacity. LFU fits
    the "templates recur, noise doesn't" shape better than plain LRU.
- **Lock contention** — a shared mutable table becomes a lock on the hot path,
  exactly under the multi-threaded embedded load we care about.
  - *Mitigation:* shard the table (N independent locked buckets by hash), or a
    lock-free/concurrent map, or per-thread tables with periodic merge.
- **Determinism / id stability** — ids must not leak into anything order- or
  identity-sensitive (fingerprints, attempt-cache keys) in a way that changes
  results between runs. Interning must dedup on the *same* structural key the
  derived `Hash` uses today, and node ids must stay solve-local for any
  result-affecting use.
- **Lifetime / GC** — persistent `Arc`s are kept alive by the table; eviction
  must actually drop them. Refcount-aware eviction (don't evict nodes still
  referenced by a live solve) or generational reset.

Open question to settle with data: is cross-expression structural overlap (the
thing that makes B pay) actually high on real ObfuscatorX binaries? Our 7-sample
dataset can't answer that — it needs a larger corpus from an actual protected
binary. Until then, B is speculative; A is the safe, measured win.

## Implementation challenge (why this is a "deep refactor", not a quick win)

The `Expr::add(a, b)`-style factories are **free functions with no context**.
Interning needs an arena/table threaded through every construction site, or a
thread-local table, or a global (locked) one. Note that clones bypass the
factories (`Arc::new(self.clone())` in `clone_tree`, `Arc::make_mut`), so an
intern-on-construct hook must also cover those paths or accept misses there.

Cheaper intermediate steps that capture part of the win without full factory
plumbing:
- **Per-solve signature memo only** (don't intern the representation): cache
  `subtree-signature` keyed by a Merkle hash stored on/derived for each node.
  Needs an efficient structural key (a Merkle hash cached per node, else hashing
  is itself an O(subtree) walk). Captures the signature-recompute win; does *not*
  cut construction allocs.
- **Within-call DAG memo** keyed by `Arc` pointer identity: free, but only
  catches subtrees already shared via cloning — misses the parser-level
  repetition (the parser builds each repeated factor as a distinct `Arc`). Low
  value alone.

## Measurement (to decide A's payoff and whether B is worth chasing)

See `### Measured redundancy` below — instrument one obfuscatorx solve and count
the signature-eval subtree recompute factor (decisive for the signature-memo
win). Construction-dedup rate is a follow-up measurement (complicated by
clone/make_mut bypassing the factories).

### Measured redundancy (obfuscatorx, 2026-06-08)

Instrumented one solve per case (Merkle-hash walk over every expr passed to
`evaluate_boolean_signature`, keyed on `(structure, len, bitwidth)`), plus a
clean timing pass:

| case | sig hit-rate | recompute | sig-eval % of solve | projected memo-only win |
|-|-|-|-|-|
| 1 (heaviest) | 93.9% | 16.5x | 6.6% | ~6% |
| 3 | 92.4% | 13.1x | 4.6% | ~4% |
| 5 | 89.3% | 9.3x | 5.4% | ~5% |
| 7 | 89.2% | 9.2x | 3.2% | ~3% |

Also: ~90–194 `evaluate_boolean_signature` calls/solve, averaging only ~14
nodes each → the redundancy is **cross-call** (the same small reduced atoms
re-evaluated across the search), not within a single tree. A per-solve
cross-call memo is what captures it; a within-call/`Arc`-pointer memo would not.

**Verdict — signature memoization *alone* is a modest win (~3–6%).** The
redundancy is real and huge, but after the scratch-pool (`96d59c4`) signature
evaluation is only 3–7% of solve time, so eliminating 94% of it moves the total
only a few percent. **Not worth** a persistent cross-solve cache + eviction for
that alone.

**Implication — the real prize is full interning, for *construction*, not
signatures.** A 94% signature-recompute rate means the search keeps re-deriving
the same subtrees, which strongly implies node **construction** (the ~10.5k
`≤64B` allocs/solve — the dominant remaining cost) is similarly redundant.
Interning dedups construction → would cut that dominant cost, with the signature
memo as a near-free side effect once nodes carry stable ids. That is the deep
(factory-plumbing) refactor in "Implementation challenge" above.

### Prototype: actual interning, measured (obfuscatorx, 2026-06-08)

Built a working per-solve interner: factories + `clone_tree` route through a
thread-local `HashMap<(kind, child-ptrs), Arc<Expr>>`, returning the canonical
node on a hit (no alloc). `Arc::make_mut` COW copies are not interned (a lower
bound). Toggle for on/off A-B timing.

**Construction-dedup rate: 84–88%** (case1: 7,113 hits / 968 misses — the search
builds only ~968 structurally-unique nodes but constructs ~8,081). Confirms the
redundancy hypothesis.

**Correctness: clean.** Full suite **781/781 real tests pass** with interning on
(incl. the 234-test `generated_lean_replay` and all integration suites); the only
failure is the Win-#1 structural test asserting `clone_tree` returns a fresh
pointer (now correctly the canonical one). The `*const Expr` pointer-keyed caches
(`join.rs`, `semilinear_normalizer.rs`) did **not** break — interning is sound
*because* Win #1 routes every mutation through `Arc::make_mut` (COW). Parity
sweep over 5,007 cases with interning on: **unsafe=0, byte-identical parity**
(mba_flatten 2067/3000, unchanged).

**Live evidence for the persistent-cache eviction requirement:** that sweep does
*not* reset the table per case, so it ran the **persistent** variant (Section B)
with no eviction — and mba_flatten went **88s → 145s (+65%)** as the table grew
unbounded across 3,000 cases (slower probes + memory pressure). Persistent
interning without a bound is a *de-optimization*; the LFU/usage-sorted eviction
is mandatory, not optional.

**Wall-time: NEUTRAL — the prize isn't there.** On-vs-off delta per case ranged
−2.6% … +4.5%, all inside the ±3% Windows noise floor; interning-on (case1
9.93ms) is no faster (slightly slower) than the committed baseline (9.3ms). Why
an 88% dedup buys nothing:
- Node allocation is only ~6% of the solve after Wins #1–#2; interning replaces
  each saved `Arc::new` (~70ns) with a hash+table-probe of similar cost.
- Deduped nodes that are later mutated just move the allocation to the
  `make_mut` COW site.
- The dominant cost is the **search work itself** (the orchestrator exploring
  candidates), which interning does not reduce.

**Verdict: full interning is NOT worth the deep refactor for this workload.** The
dedup rate is high but it's measuring the wrong thing — allocation stopped being
the bottleneck after Wins #1–#2. A production interner (faster hasher, no
`RefCell`) might net low-single-digit % on the heaviest cases, not the 20–40% the
dedup rate superficially suggests.

**What this does *not* rule out / when to revisit:**
- **Persistent cross-solve interning (Section B)** for the *memory*/throughput
  angle under real multi-expression load — it wouldn't speed a single solve but
  could cut peak RSS and allocator pressure across millions of expressions. Still
  speculative; needs a real-binary corpus + the LFU-eviction design above.
- **Id-based `Eq`/`Hash`/fingerprinting** — the prototype deduped *construction*
  but left the orchestrator's structural `Eq`/`Hash` as-is. If profiling shows
  Expr hashing/comparison (fingerprints, attempt-cache, competition) is hot,
  switching those to O(1) interned-id comparison is a *separate* lever this
  prototype didn't measure — and the only remaining place interning could pay
  off. Measure that hotness before pursuing.
- The real next frontier is **the search work**, not allocation — reducing
  candidates explored / passes run, which is algorithmic, not representational.

