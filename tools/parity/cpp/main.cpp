#include "ExprParser.h"
#include "cobra/core/Evaluator.h"
#include "cobra/core/ExprCost.h"
#include "cobra/core/ExprUtils.h"
#include "cobra/core/SignatureEval.h"
#include "cobra/core/SignatureEvalStats.h"
#include "cobra/core/Simplifier.h"

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace {

constexpr std::string_view kSchema = "cobra-parity-v2";
constexpr std::string_view kFullWidthProbeAlgorithm = "splitmix64-v1";
constexpr size_t kFullWidthProbeCount = 256;
constexpr uint64_t kFullWidthProbeSeed = UINT64_C(0x243f6a8885a308d3);
constexpr uint64_t kFnv1aOffsetBasis = UINT64_C(0xcbf29ce484222325);
constexpr uint64_t kFnv1aPrime = UINT64_C(0x00000100000001b3);

struct Args {
  std::filesystem::path manifest;
  std::optional<std::filesystem::path> output;
  size_t warmup = 1;
  size_t repetitions = 5;
};

struct Case {
  std::string id;
  uint32_t bitwidth = 64;
  uint32_t max_vars = 16;
  std::string expression;
};

struct Cost {
  uint32_t weighted_size = 0;
  uint32_t nonlinear_mul_count = 0;
  uint32_t max_depth = 0;

  bool operator==(const Cost &) const = default;
};

struct Snapshot {
  std::string outcome;
  bool verified = false;
  std::string proof_level;
  std::string semantic_class;
  uint32_t structural_flags = 0;
  std::string reason_category;
  std::string reason_domain;
  uint16_t reason_subcode = 0;
  size_t vars_count = 0;
  size_t real_vars_count = 0;
  size_t signature_len = 0;
  std::string signature_hash;
  size_t output_signature_len = 0;
  std::string output_signature_hash;
  std::string full_width_probe_algorithm;
  size_t full_width_probe_count = 0;
  std::string input_full_width_hash;
  std::string output_full_width_hash;
  bool full_width_probe_equivalent = false;
  size_t full_width_probe_mismatch_count = 0;
  std::optional<Cost> input_cost;
  std::optional<Cost> output_cost;
  std::string output;
  std::string error;

  bool operator==(const Snapshot &) const = default;
};

struct StageTimes {
  uint64_t parse_ns = 0;
  uint64_t signature_ns = 0;
  uint64_t simplify_ns = 0;
  uint64_t render_ns = 0;
};

struct TimedRun {
  Snapshot snapshot;
  StageTimes times;
  cobra::SigEvalStats simplify_sig_stats;
};

struct FullWidthFingerprint {
  std::string input_hash;
  std::string output_hash;
  bool equivalent = false;
  size_t mismatch_count = 0;
};

struct CaseRecord {
  Snapshot snapshot;
  bool deterministic = true;
  std::vector<uint64_t> parse_ns;
  std::vector<uint64_t> signature_ns;
  std::vector<uint64_t> simplify_ns;
  std::vector<uint64_t> render_ns;
  std::vector<uint64_t> sig_calls;
  std::vector<uint64_t> sig_expr_calls;
  std::vector<uint64_t> sig_eval_calls;
  std::vector<uint64_t> sig_points;
  std::vector<uint64_t> sig_nodes;
  std::vector<uint64_t> sig_time_ns;
};

std::string Usage() {
  return "Usage: cobra-parity-cpp --manifest <path> [--output <path|->] "
         "[--warmup <n>] [--repetitions <n>]";
}

size_t ParseSize(std::string_view flag, const char *value) {
  if (value == nullptr) {
    throw std::runtime_error(std::string(flag) + " requires a value");
  }
  size_t consumed = 0;
  const std::string text(value);
  const auto parsed = std::stoull(text, &consumed, 10);
  if (consumed != text.size() || parsed > std::numeric_limits<size_t>::max()) {
    throw std::runtime_error(std::string(flag) +
                             " must be a non-negative integer");
  }
  return static_cast<size_t>(parsed);
}

Args ParseArgs(int argc, char **argv) {
  Args args;
  bool has_manifest = false;
  for (int i = 1; i < argc; ++i) {
    const std::string_view arg(argv[i]);
    if (arg == "--manifest") {
      if (++i >= argc) {
        throw std::runtime_error("--manifest requires a path");
      }
      args.manifest = argv[i];
      has_manifest = true;
    } else if (arg == "--output") {
      if (++i >= argc) {
        throw std::runtime_error("--output requires a path or '-'");
      }
      if (std::string_view(argv[i]) == "-") {
        args.output.reset();
      } else {
        args.output = std::filesystem::path(argv[i]);
      }
    } else if (arg == "--warmup") {
      args.warmup = ParseSize("--warmup", (++i < argc) ? argv[i] : nullptr);
    } else if (arg == "--repetitions") {
      args.repetitions =
          ParseSize("--repetitions", (++i < argc) ? argv[i] : nullptr);
    } else if (arg == "--help" || arg == "-h") {
      std::cout << Usage() << '\n';
      std::exit(0);
    } else {
      throw std::runtime_error("unknown option '" + std::string(arg) + "'\n" +
                               Usage());
    }
  }
  if (!has_manifest) {
    throw std::runtime_error("--manifest is required\n" + Usage());
  }
  if (args.repetitions == 0) {
    throw std::runtime_error("--repetitions must be at least 1");
  }
  return args;
}

uint32_t ParseU32(std::string_view text, std::string_view field,
                  size_t line_number) {
  size_t consumed = 0;
  const std::string raw(text);
  const auto parsed = std::stoull(raw, &consumed, 10);
  if (consumed != raw.size() || parsed > std::numeric_limits<uint32_t>::max()) {
    throw std::runtime_error("manifest line " + std::to_string(line_number) +
                             " has invalid " + std::string(field) + " '" + raw +
                             "'");
  }
  return static_cast<uint32_t>(parsed);
}

std::vector<std::string_view> SplitManifestLine(const std::string &line) {
  std::vector<std::string_view> fields;
  size_t start = 0;
  for (size_t i = 0; i < line.size() && fields.size() < 3; ++i) {
    if (line[i] == '\t') {
      fields.emplace_back(line.data() + start, i - start);
      start = i + 1;
    }
  }
  fields.emplace_back(line.data() + start, line.size() - start);
  return fields;
}

std::vector<Case> ReadManifest(const std::filesystem::path &path) {
  std::ifstream input(path);
  if (!input) {
    throw std::runtime_error("failed to open manifest '" + path.string() + "'");
  }

  std::vector<Case> cases;
  std::string line;
  size_t line_number = 0;
  while (std::getline(input, line)) {
    ++line_number;
    if (!line.empty() && line.back() == '\r') {
      line.pop_back();
    }
    const auto first = line.find_first_not_of(" \t");
    if (first == std::string::npos || line[first] == '#') {
      continue;
    }

    const auto fields = SplitManifestLine(line);
    if (fields.size() != 4) {
      throw std::runtime_error("manifest line " + std::to_string(line_number) +
                               " must contain four tab-separated fields");
    }
    if (fields[0].empty()) {
      throw std::runtime_error("manifest line " + std::to_string(line_number) +
                               " has an empty case id");
    }
    for (const auto &existing : cases) {
      if (existing.id == fields[0]) {
        throw std::runtime_error(
            "manifest line " + std::to_string(line_number) +
            " repeats case id '" + std::string(fields[0]) + "'");
      }
    }

    const uint32_t bitwidth = ParseU32(fields[1], "bitwidth", line_number);
    if (bitwidth == 0 || bitwidth > 64) {
      throw std::runtime_error("manifest line " + std::to_string(line_number) +
                               " bitwidth must be in 1..=64");
    }
    const uint32_t max_vars = ParseU32(fields[2], "max_vars", line_number);
    if (fields[3].empty()) {
      throw std::runtime_error("manifest line " + std::to_string(line_number) +
                               " has an empty expression");
    }

    cases.push_back(Case{
        .id = std::string(fields[0]),
        .bitwidth = bitwidth,
        .max_vars = max_vars,
        .expression = std::string(fields[3]),
    });
  }
  if (cases.empty()) {
    throw std::runtime_error("manifest contains no cases");
  }
  return cases;
}

template <typename ClockDuration> uint64_t DurationNs(ClockDuration duration) {
  const auto count =
      std::chrono::duration_cast<std::chrono::nanoseconds>(duration).count();
  if (count <= 0) {
    return 0;
  }
  return static_cast<uint64_t>(count);
}

std::string HexHash(uint64_t hash) {
  std::ostringstream output;
  output << std::hex << std::setfill('0') << std::setw(16) << hash;
  return output.str();
}

void UpdateFnv1aU64(uint64_t &hash, uint64_t value) {
  for (unsigned int shift = 0; shift < 64; shift += 8) {
    const auto byte = static_cast<uint8_t>((value >> shift) & UINT64_C(0xff));
    hash ^= byte;
    hash *= kFnv1aPrime;
  }
}

std::string Fnv1aU64s(const std::vector<uint64_t> &values) {
  uint64_t hash = kFnv1aOffsetBasis;
  for (uint64_t value : values) {
    for (unsigned int shift = 0; shift < 64; shift += 8) {
      const auto byte = static_cast<uint8_t>((value >> shift) & UINT64_C(0xff));
      hash ^= byte;
      hash *= kFnv1aPrime;
    }
  }
  return HexHash(hash);
}

uint64_t Splitmix64(uint64_t &state) {
  state += UINT64_C(0x9e3779b97f4a7c15);
  uint64_t value = state;
  value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
  return value ^ (value >> 31);
}

FullWidthFingerprint FullWidthFingerprints(const cobra::Expr &input,
                                           const cobra::Expr &output,
                                           uint32_t num_vars,
                                           uint32_t bitwidth) {
  const uint64_t mask = bitwidth == 64 ? std::numeric_limits<uint64_t>::max()
                                       : (UINT64_C(1) << bitwidth) - 1;
  const auto input_program = cobra::CompileExpr(input, bitwidth);
  const auto output_program = cobra::CompileExpr(output, bitwidth);
  std::vector<uint64_t> input_stack;
  input_stack.reserve(input_program.stack_size);
  std::vector<uint64_t> output_stack;
  output_stack.reserve(output_program.stack_size);
  std::vector<uint64_t> inputs(num_vars);
  uint64_t rng_state = kFullWidthProbeSeed ^
                       (static_cast<uint64_t>(bitwidth) << 32) ^
                       static_cast<uint64_t>(num_vars);
  uint64_t input_hash = kFnv1aOffsetBasis;
  uint64_t output_hash = kFnv1aOffsetBasis;
  size_t mismatch_count = 0;

  for (size_t probe_index = 0; probe_index < kFullWidthProbeCount;
       ++probe_index) {
    if (probe_index == 0) {
      std::fill(inputs.begin(), inputs.end(), 0);
    } else if (probe_index == 1) {
      std::fill(inputs.begin(), inputs.end(), mask);
    } else {
      for (auto &value : inputs) {
        value = Splitmix64(rng_state) & mask;
      }
    }

    const uint64_t input_value =
        cobra::EvalCompiledExpr(input_program, inputs, input_stack);
    const uint64_t output_value =
        cobra::EvalCompiledExpr(output_program, inputs, output_stack);
    UpdateFnv1aU64(input_hash, input_value);
    UpdateFnv1aU64(output_hash, output_value);
    mismatch_count += static_cast<size_t>(input_value != output_value);
  }

  return FullWidthFingerprint{
      .input_hash = HexHash(input_hash),
      .output_hash = HexHash(output_hash),
      .equivalent = mismatch_count == 0,
      .mismatch_count = mismatch_count,
  };
}

Cost ToCost(const cobra::ExprCost &cost) {
  return Cost{
      .weighted_size = cost.weighted_size,
      .nonlinear_mul_count = cost.nonlinear_mul_count,
      .max_depth = cost.max_depth,
  };
}

const char *OutcomeName(cobra::SimplifyOutcome::Kind kind) {
  switch (kind) {
  case cobra::SimplifyOutcome::Kind::kSimplified:
    return "simplified";
  case cobra::SimplifyOutcome::Kind::kUnchangedUnsupported:
    return "unchanged_unsupported";
  case cobra::SimplifyOutcome::Kind::kError:
    return "error";
  }
  return "error";
}

const char *SemanticClassName(cobra::SemanticClass semantic) {
  switch (semantic) {
  case cobra::SemanticClass::kLinear:
    return "Linear";
  case cobra::SemanticClass::kSemilinear:
    return "Semilinear";
  case cobra::SemanticClass::kPolynomial:
    return "Polynomial";
  case cobra::SemanticClass::kNonPolynomial:
    return "NonPolynomial";
  }
  return "Unknown";
}

const char *ReasonCategoryName(cobra::ReasonCategory category) {
  switch (category) {
  case cobra::ReasonCategory::kNone:
    return "None";
  case cobra::ReasonCategory::kGuardFailed:
    return "GuardFailed";
  case cobra::ReasonCategory::kInapplicable:
    return "Inapplicable";
  case cobra::ReasonCategory::kRepresentationGap:
    return "RepresentationGap";
  case cobra::ReasonCategory::kNoSolution:
    return "NoSolution";
  case cobra::ReasonCategory::kSearchExhausted:
    return "SearchExhausted";
  case cobra::ReasonCategory::kVerifyFailed:
    return "VerifyFailed";
  case cobra::ReasonCategory::kResourceLimit:
    return "ResourceLimit";
  case cobra::ReasonCategory::kCostRejected:
    return "CostRejected";
  case cobra::ReasonCategory::kInternalInvariant:
    return "InternalInvariant";
  }
  return "Unknown";
}

const char *ReasonDomainName(cobra::ReasonDomain domain) {
  switch (domain) {
  case cobra::ReasonDomain::kOrchestrator:
    return "Orchestrator";
  case cobra::ReasonDomain::kSemilinear:
    return "Semilinear";
  case cobra::ReasonDomain::kSignature:
    return "Signature";
  case cobra::ReasonDomain::kStructuralTransform:
    return "StructuralTransform";
  case cobra::ReasonDomain::kDecomposition:
    return "Decomposition";
  case cobra::ReasonDomain::kTemplateDecomposer:
    return "TemplateDecomposer";
  case cobra::ReasonDomain::kWeightedPolyFit:
    return "WeightedPolyFit";
  case cobra::ReasonDomain::kMultivarPoly:
    return "MultivarPoly";
  case cobra::ReasonDomain::kPolynomialRecovery:
    return "PolynomialRecovery";
  case cobra::ReasonDomain::kBitwiseDecomposer:
    return "BitwiseDecomposer";
  case cobra::ReasonDomain::kHybridDecomposer:
    return "HybridDecomposer";
  case cobra::ReasonDomain::kGhostResidual:
    return "GhostResidual";
  case cobra::ReasonDomain::kOperandSimplifier:
    return "OperandSimplifier";
  case cobra::ReasonDomain::kLifting:
    return "Lifting";
  case cobra::ReasonDomain::kVerifier:
    return "Verifier";
  }
  return "Unknown";
}

Snapshot FailedSnapshot(std::string_view stage, std::string message) {
  Snapshot snapshot;
  snapshot.outcome = std::string(stage) + "_error";
  snapshot.reason_category = "None";
  snapshot.reason_domain = "Orchestrator";
  snapshot.error = std::move(message);
  return snapshot;
}

TimedRun RunOnce(const Case &test_case) {
  using Clock = std::chrono::steady_clock;

  StageTimes times;
  const auto parse_started = Clock::now();
  auto parsed_result =
      cobra::ParseToAst(test_case.expression, test_case.bitwidth);
  times.parse_ns = DurationNs(Clock::now() - parse_started);
  if (!parsed_result.has_value()) {
    return TimedRun{
        .snapshot = FailedSnapshot("parse", parsed_result.error().message),
        .times = times,
    };
  }
  auto parsed = std::move(parsed_result.value());
  const Cost input_cost = ToCost(cobra::ComputeCost(*parsed.expr).cost);

  const auto signature_started = Clock::now();
  auto signature = cobra::EvaluateBooleanSignature(
      *parsed.expr, static_cast<uint32_t>(parsed.vars.size()),
      test_case.bitwidth);
  times.signature_ns = DurationNs(Clock::now() - signature_started);
  const std::string signature_hash = Fnv1aU64s(signature);

  cobra::SigStatsReset();
  const auto simplify_started = Clock::now();
  cobra::Options options{
      .bitwidth = test_case.bitwidth,
      .max_vars = test_case.max_vars,
  };
  auto simplify_result =
      cobra::Simplify(signature, parsed.vars, parsed.expr.get(), options);
  times.simplify_ns = DurationNs(Clock::now() - simplify_started);
  const auto simplify_sig_stats = cobra::SigStatsSnapshot();
  if (!simplify_result.has_value()) {
    auto snapshot = FailedSnapshot("simplify", simplify_result.error().message);
    snapshot.vars_count = parsed.vars.size();
    snapshot.signature_len = signature.size();
    snapshot.signature_hash = signature_hash;
    snapshot.input_cost = input_cost;
    return TimedRun{
        .snapshot = std::move(snapshot),
        .times = times,
        .simplify_sig_stats = simplify_sig_stats,
    };
  }
  auto outcome = std::move(simplify_result.value());

  std::unique_ptr<cobra::Expr> display_expr;
  if (outcome.kind == cobra::SimplifyOutcome::Kind::kSimplified &&
      outcome.expr) {
    display_expr = cobra::CloneExpr(*outcome.expr);
    if (!outcome.real_vars.empty() &&
        outcome.real_vars.size() < parsed.vars.size()) {
      const auto index_map =
          cobra::BuildVarSupport(parsed.vars, outcome.real_vars);
      cobra::RemapVarIndices(*display_expr, index_map);
    }
  } else {
    display_expr = cobra::CloneExpr(*parsed.expr);
  }

  const auto render_started = Clock::now();
  std::string output =
      cobra::Render(*display_expr, parsed.vars, test_case.bitwidth);
  times.render_ns = DurationNs(Clock::now() - render_started);
  const Cost output_cost = ToCost(cobra::ComputeCost(*display_expr).cost);
  const auto output_signature = cobra::EvaluateBooleanSignature(
      *display_expr, static_cast<uint32_t>(parsed.vars.size()),
      test_case.bitwidth);
  const std::string output_signature_hash = Fnv1aU64s(output_signature);
  const auto full_width = FullWidthFingerprints(
      *parsed.expr, *display_expr, static_cast<uint32_t>(parsed.vars.size()),
      test_case.bitwidth);

  std::string reason_category = "None";
  std::string reason_domain = "Orchestrator";
  uint16_t reason_subcode = 0;
  if (outcome.diag.reason_code.has_value()) {
    reason_category = ReasonCategoryName(outcome.diag.reason_code->category);
    reason_domain = ReasonDomainName(outcome.diag.reason_code->domain);
    reason_subcode = outcome.diag.reason_code->subcode;
  }

  return TimedRun{
      .snapshot =
          Snapshot{
              .outcome = OutcomeName(outcome.kind),
              .verified = outcome.verified,
              .proof_level = outcome.verified ? "LegacyVerified" : "Unverified",
              .semantic_class =
                  SemanticClassName(outcome.diag.classification.semantic),
              .structural_flags =
                  static_cast<uint32_t>(outcome.diag.classification.flags),
              .reason_category = std::move(reason_category),
              .reason_domain = std::move(reason_domain),
              .reason_subcode = reason_subcode,
              .vars_count = parsed.vars.size(),
              .real_vars_count = outcome.real_vars.size(),
              .signature_len = signature.size(),
              .signature_hash = signature_hash,
              .output_signature_len = output_signature.size(),
              .output_signature_hash = output_signature_hash,
              .full_width_probe_algorithm =
                  std::string(kFullWidthProbeAlgorithm),
              .full_width_probe_count = kFullWidthProbeCount,
              .input_full_width_hash = full_width.input_hash,
              .output_full_width_hash = full_width.output_hash,
              .full_width_probe_equivalent = full_width.equivalent,
              .full_width_probe_mismatch_count = full_width.mismatch_count,
              .input_cost = input_cost,
              .output_cost = output_cost,
              .output = std::move(output),
              .error = outcome.diag.reason,
          },
      .times = times,
      .simplify_sig_stats = simplify_sig_stats,
  };
}

TimedRun RunOnceSafe(const Case &test_case) {
  try {
    return RunOnce(test_case);
  } catch (const std::exception &error) {
    return TimedRun{
        .snapshot = FailedSnapshot("runner", error.what()),
        .times = {},
    };
  }
}

CaseRecord RunCase(const Case &test_case, size_t warmup, size_t repetitions) {
  for (size_t i = 0; i < warmup; ++i) {
    static_cast<void>(RunOnceSafe(test_case));
  }

  CaseRecord record;
  record.parse_ns.reserve(repetitions);
  record.signature_ns.reserve(repetitions);
  record.simplify_ns.reserve(repetitions);
  record.render_ns.reserve(repetitions);
  record.sig_calls.reserve(repetitions);
  record.sig_expr_calls.reserve(repetitions);
  record.sig_eval_calls.reserve(repetitions);
  record.sig_points.reserve(repetitions);
  record.sig_nodes.reserve(repetitions);
  record.sig_time_ns.reserve(repetitions);
  std::optional<Snapshot> first;

  for (size_t i = 0; i < repetitions; ++i) {
    auto run = RunOnceSafe(test_case);
    if (first.has_value()) {
      record.deterministic = record.deterministic && (*first == run.snapshot);
    } else {
      first = run.snapshot;
    }
    record.parse_ns.push_back(run.times.parse_ns);
    record.signature_ns.push_back(run.times.signature_ns);
    record.simplify_ns.push_back(run.times.simplify_ns);
    record.render_ns.push_back(run.times.render_ns);
    record.sig_calls.push_back(run.simplify_sig_stats.calls);
    record.sig_expr_calls.push_back(run.simplify_sig_stats.expr_calls);
    record.sig_eval_calls.push_back(run.simplify_sig_stats.eval_calls);
    record.sig_points.push_back(run.simplify_sig_stats.total_points);
    record.sig_nodes.push_back(run.simplify_sig_stats.total_nodes);
    record.sig_time_ns.push_back(
        static_cast<uint64_t>(run.simplify_sig_stats.total_us * 1000.0));
  }
  record.snapshot = std::move(*first);
  return record;
}

std::string JsonEscape(std::string_view value) {
  std::ostringstream escaped;
  for (const unsigned char character : value) {
    switch (character) {
    case '"':
      escaped << "\\\"";
      break;
    case '\\':
      escaped << "\\\\";
      break;
    case '\b':
      escaped << "\\b";
      break;
    case '\f':
      escaped << "\\f";
      break;
    case '\n':
      escaped << "\\n";
      break;
    case '\r':
      escaped << "\\r";
      break;
    case '\t':
      escaped << "\\t";
      break;
    default:
      if (character < 0x20) {
        escaped << "\\u" << std::hex << std::setfill('0') << std::setw(4)
                << static_cast<unsigned int>(character) << std::dec;
      } else {
        escaped << static_cast<char>(character);
      }
    }
  }
  return escaped.str();
}

void StringField(std::ostream &output, std::string_view key,
                 std::string_view value) {
  output << '"' << JsonEscape(key) << "\":\"" << JsonEscape(value) << '"';
}

void WriteCost(std::ostream &output, const std::optional<Cost> &cost) {
  if (!cost.has_value()) {
    output << "null";
    return;
  }
  output << "{\"weighted_size\":" << cost->weighted_size
         << ",\"nonlinear_mul_count\":" << cost->nonlinear_mul_count
         << ",\"max_depth\":" << cost->max_depth << '}';
}

void WriteArray(std::ostream &output, const std::vector<uint64_t> &values) {
  output << '[';
  for (size_t i = 0; i < values.size(); ++i) {
    if (i != 0) {
      output << ',';
    }
    output << values[i];
  }
  output << ']';
}

void WriteRecord(std::ostream &output, const Case &test_case, size_t warmup,
                 size_t repetitions, const CaseRecord &record) {
  const auto &snapshot = record.snapshot;
  output << '{';
  StringField(output, "schema", kSchema);
  output << ',';
  StringField(output, "engine", "cpp");
  output << ',';
  StringField(output, "case_id", test_case.id);
  output << ',';
  StringField(output, "expression", test_case.expression);
  output << ",\"bitwidth\":" << test_case.bitwidth
         << ",\"max_vars\":" << test_case.max_vars << ",\"warmup\":" << warmup
         << ",\"repetitions\":" << repetitions << ',';
  StringField(output, "outcome", snapshot.outcome);
  output << ",\"verified\":" << (snapshot.verified ? "true" : "false")
         << ",\"deterministic\":" << (record.deterministic ? "true" : "false")
         << ',';
  StringField(output, "proof_level", snapshot.proof_level);
  output << ',';
  StringField(output, "semantic_class", snapshot.semantic_class);
  output << ",\"structural_flags\":" << snapshot.structural_flags
         << ",\"vars_count\":" << snapshot.vars_count
         << ",\"real_vars_count\":" << snapshot.real_vars_count
         << ",\"signature_len\":" << snapshot.signature_len << ',';
  StringField(output, "signature_hash", snapshot.signature_hash);
  output << ",\"output_signature_len\":" << snapshot.output_signature_len
         << ',';
  StringField(output, "output_signature_hash", snapshot.output_signature_hash);
  output << ',';
  StringField(output, "full_width_probe_algorithm",
              snapshot.full_width_probe_algorithm);
  output << ",\"full_width_probe_count\":" << snapshot.full_width_probe_count
         << ',';
  StringField(output, "input_full_width_hash", snapshot.input_full_width_hash);
  output << ',';
  StringField(output, "output_full_width_hash",
              snapshot.output_full_width_hash);
  output << ",\"full_width_probe_equivalent\":"
         << (snapshot.full_width_probe_equivalent ? "true" : "false")
         << ",\"full_width_probe_mismatch_count\":"
         << snapshot.full_width_probe_mismatch_count;
  output << ",\"reason\":{";
  StringField(output, "category", snapshot.reason_category);
  output << ',';
  StringField(output, "domain", snapshot.reason_domain);
  output << ",\"subcode\":" << snapshot.reason_subcode << '}';
  output << ",\"input_cost\":";
  WriteCost(output, snapshot.input_cost);
  output << ",\"output_cost\":";
  WriteCost(output, snapshot.output_cost);
  output << ',';
  StringField(output, "output", snapshot.output);
  output << ',';
  StringField(output, "error", snapshot.error);
  output << ",\"timings_ns\":{\"parse\":";
  WriteArray(output, record.parse_ns);
  output << ",\"signature\":";
  WriteArray(output, record.signature_ns);
  output << ",\"simplify\":";
  WriteArray(output, record.simplify_ns);
  output << ",\"render\":";
  WriteArray(output, record.render_ns);
  output << "},\"simplify_signature_stats\":{\"calls\":";
  WriteArray(output, record.sig_calls);
  output << ",\"expr_calls\":";
  WriteArray(output, record.sig_expr_calls);
  output << ",\"eval_calls\":";
  WriteArray(output, record.sig_eval_calls);
  output << ",\"points\":";
  WriteArray(output, record.sig_points);
  output << ",\"nodes\":";
  WriteArray(output, record.sig_nodes);
  output << ",\"time_ns\":";
  WriteArray(output, record.sig_time_ns);
  output << "}}\n";
}

int Run(const Args &args) {
  const auto cases = ReadManifest(args.manifest);
  std::ofstream file;
  std::ostream *output = &std::cout;
  if (args.output.has_value()) {
    file.open(*args.output, std::ios::out | std::ios::trunc);
    if (!file) {
      throw std::runtime_error("failed to create output '" +
                               args.output->string() + "'");
    }
    output = &file;
  }

  for (const auto &test_case : cases) {
    const auto record = RunCase(test_case, args.warmup, args.repetitions);
    WriteRecord(*output, test_case, args.warmup, args.repetitions, record);
  }
  output->flush();
  if (!*output) {
    throw std::runtime_error("failed to write results");
  }
  return 0;
}

} // namespace

int main(int argc, char **argv) {
  try {
    return Run(ParseArgs(argc, argv));
  } catch (const std::exception &error) {
    std::cerr << error.what() << '\n';
    return 2;
  }
}
