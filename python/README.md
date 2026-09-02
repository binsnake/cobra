# cobra-mba

Python bindings for [CoBRA](https://github.com/binsnake/cobra), a Rust
simplifier for mixed Boolean-arithmetic (MBA) expressions.

```python
import cobra_mba

result = cobra_mba.simplify("(x ^ y) + 2 * (x & y)")
print(result)                 # x + y
print(result.proof_level)     # ProofLevel.LEAN_CERTIFIED
```

Wheels carry the compiled simplifier, so there is nothing else to install.
The package name is `cobra-mba` because `cobra` on PyPI belongs to an
unrelated project; the import name is `cobra_mba`.

## Install

```
pip install cobra-mba
```

Wheels are published for CPython 3.10 and newer on Linux (x86-64 and
aarch64), macOS, and Windows x64. Any other platform builds from the source
distribution and needs a Rust toolchain.

## Expressions

`Expr` pairs an expression tree with the variable names its indices refer to,
so trees built separately can still be combined.

```python
from cobra_mba import Expr

e = Expr.parse("(x ^ y) + 2 * (x & y)")
e.variables            # ['x', 'y']
e.evaluate(x=3, y=5)   # 8
e.kind                 # Kind.ADD
str(e.children[0])     # 'x ^ y'
```

Operators build the same trees the parser does:

```python
x, y = Expr.var("x"), Expr.var("y")
(x ^ y) + 2 * (x & y) == Expr.parse("(x ^ y) + 2 * (x & y)")   # True
```

Variables are sorted lexicographically, matching the parser, so
`Expr.var("b") + Expr.var("a")` renders with `a` first.

Expressions are immutable, hashable, comparable, and picklable. `to_dict` and
`Expr.from_dict` give a plain-data form suitable for JSON.

## Results

`simplify` returns the whole outcome rather than just an expression:

```python
result = cobra_mba.simplify("x * x * x", bitwidth=32)
result.kind            # OutcomeKind.UNCHANGED_UNSUPPORTED
result.diagnostic.reason
result.telemetry.total_expansions
```

A pipeline error is a value, not an exception, so its diagnostic can be
inspected. Call `result.raise_for_error()` when an exception is the more
convenient shape. Bad input still raises: `ParseError`,
`InvalidArgumentError`, and `TooManyVariablesError` all subclass both
`CobraError` and `ValueError`.

## Certificates and soundness

By default a simplification is discarded unless a replayable Lean certificate
covers its exact output. This is the soundness gate: full-width checking is
finite probing, and a candidate can differ from the original at one point no
probe reaches.

```python
cobra_mba.simplify(expr_text, require_lean_certificate=False)
```

Turning the gate off accepts probe-only assurance. It raises the
simplification rate a great deal and is reasonable when inputs are not
adversarial.

## Doing a lot at once

`simplify_many` hands the whole batch over in one call and spreads it across
every core with the interpreter lock released:

```python
from cobra_mba import simplify_many

results = simplify_many(expressions, require_lean_certificate=False)
```

Results come back in input order. Pass `on_error="none"` to get `None` in place
of an item that failed to parse, so one bad line does not cost the batch, and
`workers=` to fix the thread count. Measured on six cores, it runs about four
times faster than calling `simplify` in a loop.

`evaluate_many` evaluates one expression at many points in a single call:

```python
expr = Expr.parse("(x ^ y) + 2 * (x & y)")
expr.evaluate_many({"x": [1, 2, 3], "y": [10, 20, 30]})
```

Columns may be sequences of integers, or bytes holding one little-endian
64-bit value per point. The bytes form is the fast one, and `raw=True` returns
results in the same shape, which is what NumPy reads and writes directly:

```python
import numpy as np

xs = np.array(..., dtype=np.uint64)
ys = np.array(..., dtype=np.uint64)
raw = expr.evaluate_many({"x": xs.tobytes(), "y": ys.tobytes()}, raw=True)
out = np.frombuffer(raw, dtype="<u8")
```

Measured on 50 000 points, against a Python loop over `evaluate`:

| How the points are passed | Relative speed |
|-|-|
| One point at a time | 1.0x |
| Lists | 7.0x |
| Bytes in | 16.4x |
| Bytes in and out | 25.4x |

There is no zero-copy buffer path. Python only added the buffer protocol to its
stable ABI in 3.11, and these wheels target 3.10, so bytes are as close as the
stable ABI gets. See [`examples/`](examples/) for both in use.

## Threads

Every call releases the interpreter lock and runs the pipeline on a worker
thread with a large stack, so a thread pool scales and deeply nested
expressions do not overflow Python's own stack.

```python
from concurrent.futures import ThreadPoolExecutor

with ThreadPoolExecutor(8) as pool:
    results = list(pool.map(cobra_mba.simplify, expressions))
```

## Limits

| Limit | Value |
|-|-|
| Bit width | 1 to 64 |
| Variables | 20 |
| Input size | 1 MiB, 100 000 tokens |
| Parsed depth | 512 |

Mixed-width trees, built with `zext`, `sext`, `trunc`, and `concat`, are
supported by the expression layer. The text parser cannot express casts, and
constants take the expression's global bit width rather than a local one, so
a mixed-width tree that also mixes constant widths will not validate.

## License

Apache-2.0. CoBRA was originally developed by Kyle Elliott and Trail of Bits.
