# CoBRA Rust/C++ parity and performance harness

This directory runs the Rust and C++ libraries **in process** over the same
manifest. Each runner parses, evaluates the Boolean signature, simplifies, and
renders every case repeatedly, then emits one JSON object per case. Process
startup, manifest I/O, JSON serialization, output normalization, and cost
bookkeeping are outside the four measured stages. The semantic fingerprints
described below are also computed outside the timing windows.

The C++ runner is an out-of-tree consumer. CMake builds `cobra-core` from the
checkout passed as `COBRA_CPP_SOURCE` and compiles the upstream expression
parser into the runner; it does not create or modify files in that checkout.

## Quick smoke run on Windows

Use a Visual Studio 2022 Developer PowerShell from the Rust repository root.
The commands below use the dependency prefix already present beside the local
C++ checkout:

```powershell
cargo build --release --features parity-tools --bin cobra-parity-rust

cmake -S tools/parity/cpp -B target/parity/cpp `
  -G "Visual Studio 17 2022" -A x64 `
  -DCOBRA_CPP_SOURCE=D:/binsnake/CoBRA-cpp `
  -DCMAKE_PREFIX_PATH=D:/binsnake/CoBRA-cpp/build-deps/install
cmake --build target/parity/cpp --config Release --target cobra-parity-cpp

New-Item -ItemType Directory -Force target/parity/results | Out-Null
target/release/cobra-parity-rust.exe `
  --manifest tools/parity/smoke.tsv `
  --output target/parity/results/rust.jsonl `
  --warmup 1 --repetitions 5
target/parity/cpp/Release/cobra-parity-cpp.exe `
  --manifest tools/parity/smoke.tsv `
  --output target/parity/results/cpp.jsonl `
  --warmup 1 --repetitions 5

python tools/parity/compare.py `
  target/parity/results/rust.jsonl `
  target/parity/results/cpp.jsonl `
  --semantic-parity `
  --show-cases `
  --json-summary target/parity/results/comparison.json
```

With Ninja or another single-config generator, the C++ executable is normally
`target/parity/cpp/cobra-parity-cpp.exe`; omit `--config Release` only if the
generator and `CMAKE_BUILD_TYPE=Release` already select an optimized build.
Use a different checkout without editing this project by changing only
`-DCOBRA_CPP_SOURCE=...`.

## Performance run

Generate the deterministic extended manifest, then use more warmups and
repetitions:

```powershell
python tools/parity/generate_manifest.py `
  --suite performance `
  --output target/parity/performance.tsv

target/release/cobra-parity-rust.exe `
  --manifest target/parity/performance.tsv `
  --output target/parity/results/rust-performance.jsonl `
  --warmup 3 --repetitions 30
target/parity/cpp/Release/cobra-parity-cpp.exe `
  --manifest target/parity/performance.tsv `
  --output target/parity/results/cpp-performance.jsonl `
  --warmup 3 --repetitions 30

python tools/parity/compare.py `
  target/parity/results/rust-performance.jsonl `
  target/parity/results/cpp-performance.jsonl `
  --semantic-parity `
  --show-cases
```

For a wider feature-parity corpus, append deterministic, evenly spaced samples
from one or more checked-in datasets:

```powershell
python tools/parity/generate_manifest.py `
  --suite regression `
  --dataset datasets/gamba/syntia.txt `
  --dataset datasets/simba/pldi_linear.txt `
  --dataset-limit 5 `
  --output target/parity/regression.tsv
```

## Full-corpus run

`run_full_corpus.ps1` recursively includes every `.txt` file below `datasets`,
passes `--dataset-limit 0`, and omits the built-in cases. By default it uses
one measured traversal per case, no per-case warmup, and both engine orders.
This is intentional: repeating every case 30 times would make the complete
corpus run impractically long. Increase `-Repetitions` only when that cost is
acceptable.

The script writes each run under `target/parity/full-corpus/<run-id>`. It
captures runner stdout/stderr, wall-clock durations, raw JSONL records,
per-engine semantic/runner failures, semantic comparison summaries, strict
cross-engine mismatches, and machine/revision metadata in `run.json`. The
comparison is streamed one JSONL pair at a time so large rendered expressions
do not require both complete result files to fit in memory.

Prepare and validate the command without generating a manifest or launching a
runner:

```powershell
tools/parity/run_full_corpus.ps1 -ValidateOnly
```

Launch the default two-order run:

```powershell
tools/parity/run_full_corpus.ps1
```

Use `-Build` to rebuild both existing parity-runner build trees first. The
build time is not included in runner wall-clock durations. `-Orders RustFirst`
or `-Orders CppFirst` can be used for a single order, and `-RunId` selects a
stable output directory name.

Dataset rows use their first top-level tab- or comma-separated expression.
The source line number is part of every generated case ID, so a sampled
manifest can be traced back to the checked-in corpus.

For less noisy numbers, use Release builds, keep both runs on the same machine
and power plan, close competing CPU-heavy work, and run the two engine orders
both ways. The comparator reports medians and a geometric mean of per-case
Rust/C++ ratios; a ratio greater than 1 means Rust took longer.

## Manifest format

The manifest is UTF-8 TSV. Blank lines and lines whose first non-whitespace
character is `#` are ignored. Every case has exactly four fields:

```text
case_id<TAB>bitwidth<TAB>max_vars<TAB>expression
```

Case IDs must be unique. Expressions cannot contain tabs or newlines.
`bitwidth` must be in `1..=64`. The same per-case `max_vars` value is passed to
both simplifiers. `generate_manifest.py` can reproduce the checked-in smoke
manifest:

```powershell
python tools/parity/generate_manifest.py --suite smoke --output tools/parity/smoke.tsv
```

The harness deliberately calls each language's `ParseToAst`/`parse_to_ast`
core API directly. It does not include C++ CLI-only preprocessing such as
`FoldConstantBitwise`; this keeps the measured stages aligned and tests the
libraries rather than the front-end executables.

## Result schema

Both runners accept:

```text
--manifest PATH [--output PATH|-] [--warmup N] [--repetitions N]
```

`--output -` (or no `--output`) writes JSONL to stdout. Warmup iterations run
the entire four-stage pipeline and are discarded. Every measured repetition
also starts from parsing, so no AST or simplifier state is reused between
samples.

For targeted C++ profiling, configure the out-of-tree runner with
`-DCOBRA_PARITY_ENABLE_SIG_STATS=ON`. Its JSONL records then populate
`simplify_signature_stats` with per-repetition signature call, point, node,
and elapsed-time counters. With the option off, those extra arrays contain
zeros and impose no upstream counter overhead. `COBRA_PARITY_ENABLE_TRACE`
similarly forwards the upstream pipeline trace option.

Each `cobra-parity-v2` JSON object contains:

- case inputs, engine, warmup, and repetition counts;
- outcome, rendered output, input/output expression costs, diagnostic reason,
  classification, variable counts, and proof/verification metadata;
- the lengths and 64-bit FNV-1a hashes of both the input and output Boolean
  signatures;
- fixed-algorithm, full-width probe metadata, input/output result-stream
  hashes, a sampled-equivalence flag, and a mismatch count;
- a `deterministic` flag, which is false if any non-timing result changed
  between repetitions;
- arrays of nanosecond samples for `parse`, `signature`, `simplify`, and
  `render`.

The stages are intentionally narrow:

- `parse`: expression string to AST and sorted variable list;
- `signature`: exhaustive Boolean signature evaluation;
- `simplify`: options/evaluator setup plus the library simplifier call;
- `render`: the renderer call only.

Both runners leave the optional evaluator unset and pass the parsed AST to
`Simplify`. The current Rust and C++ APIs therefore both auto-build their
evaluator from that AST inside the measured simplify stage.

AST cloning/remapping for original variable names and cost calculation are
untimed bookkeeping. Output-signature evaluation and full-width fingerprinting
are untimed too. Parse, simplifier, or runner post-processing failures still
produce a case record; unreached stage timings are zero. This keeps a bad
candidate or remapping invariant visible as a per-case parity failure instead
of truncating the rest of a corpus run.

### Semantic fingerprint algorithm

`splitmix64-v1` is deliberately small and implemented literally in both
runners:

1. Use exactly 256 probe vectors. Mask every variable value to the case
   bitwidth.
2. Probe 0 is the all-zero vector and probe 1 is the all-mask vector.
3. Initialize the 64-bit wrapping SplitMix64 state to
   `0x243f6a8885a308d3 ^ (bitwidth << 32) ^ num_vars`. For probes 2 through
   255, advance SplitMix64 once per variable in variable-index order and use
   the masked result.
4. Evaluate both the parsed input AST and the output AST at every vector.
   FNV-1a hashes each stream of 64-bit results in little-endian byte order,
   starting from `0xcbf29ce484222325` and multiplying by
   `0x00000100000001b3`.

The output AST is first remapped back into the parsed input variable space, so
both sides consume identical vectors even after variable elimination.
`full_width_probe_equivalent` is true only when all 256 result pairs match;
`full_width_probe_mismatch_count` records the exact number that did not.

These probes are deterministic regression evidence, not a mathematical proof
of full-width equivalence. The Boolean signature is exhaustive over `{0,1}`
for the case variable count, while the 256 full-width samples exercise points
outside that domain.

## Comparison policy

By default, exact mode exits nonzero for missing cases, nondeterministic
results, internal semantic-check failures, or cross-language differences in
expression inputs, outcome, input/output signatures, full-width probe
fingerprints, costs, or rendered output. Diagnostics, classification,
variable-elimination counts, and proof metadata are reported separately
because the two public APIs do not currently expose identical proof-level
types. Add `--strict-metadata` when those fields are expected to match exactly.

`--semantic-parity` is the spelling-independent parity mode. It strictly
requires matching case inputs and outcomes, matching input/output Boolean
signature hashes, and matching full-width probe algorithms, counts, hashes,
equivalence flags, and mismatch counts. It also independently requires each
runner's output Boolean signature to equal its own input signature and all 256
of its full-width probes to match. Rendered spelling, input/output cost
metadata, and API diagnostics remain informational. This is the preferred mode
for feature-parity checks when two equivalent canonical forms render
differently.

Canonical renderings can differ while remaining equivalent. During
investigation, `--allow-output-difference` makes only the output string
informational; signature, outcome, and costs remain strict. This option should
not be used for a final claim of exact output parity. It is redundant in
`--semantic-parity` mode.
