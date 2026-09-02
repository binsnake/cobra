# Examples

Four scripts. Two run anywhere and are exercised by the test suite; two are
templates for a reverse-engineering tool and cannot be.

## Runnable

**`simplify_corpus.py`** simplifies a whole dataset in one call and checks each
result against its input over sampled points.

```bash
python simplify_corpus.py ../../datasets/univariate64.txt --limit 200
```

Pass `--certified-only` to keep the Lean certificate gate on and watch what it
costs. On the bundled corpora it takes the simplification rate to roughly zero,
which is the documented trade-off: the gate is what separates a replayable
proof from probe-only assurance.

**`bulk_evaluate.py`** evaluates one expression at many points and compares the
ways of feeding it, then uses bulk evaluation for what it is most useful for:
checking that a simplified expression agrees with the one it came from.

```bash
python bulk_evaluate.py --points 200000
```

Measured on six cores, 50 000 points:

| How the points are passed | Relative speed |
|-|-|
| One point at a time through `evaluate` | 1.0x |
| `evaluate_many` with lists | 7.0x |
| `evaluate_many` with bytes in | 16.4x |
| `evaluate_many` with bytes in and out | 25.4x |

The bytes form is one little-endian 64-bit value per point, which is exactly
what `numpy_array.tobytes()` produces and what `numpy.frombuffer(result,
dtype="<u8")` reads back.

## Tool integration

**`idapython_simplify.py`** walks the ctree of the current function, translates
every arithmetic and bitwise subtree into the simplifier's syntax, and reports
the ones that come back shorter.

**`binaryninja_simplify.py`** does the same over a function's HLIL, and also
runs headlessly against a file.

Both need `cobra_mba` installed into the interpreter the tool runs, which is
usually not the one on your PATH:

```bash
"%IDADIR%\python3\python.exe" -m pip install cobra-mba
```

Neither has been run against a live installation. The simplifier calls are the
same ones the runnable examples use, but treat the Hex-Rays and Binary Ninja
details as a starting point rather than as tested code.

Both turn the certificate gate off, because with it on almost nothing in real
obfuscated code simplifies. That accepts probe-only assurance: a candidate can
differ from the original at a point no probe reached. Read a result as a strong
lead, and verify anything you are about to act on, with `--verify` on
`cobra-cli` built with Z3 or by checking the two forms over your own inputs.
