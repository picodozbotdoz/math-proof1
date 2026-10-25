# Bench/ — kernel benchmarks from the Lehmer scaling study ⚠️ NOT theorems

**This directory is not part of the proof library.** Nothing here is imported
by `MathProof.lean`, built by the default target, or run in CI.  These are the
measurement artifacts of
[research/lehmer-mod-scaling-study.md](../research/lehmer-mod-scaling-study.md)
(iteration 5): they exist to record *how* the packed-bignum scheme was
benchmarked and to let anyone reproduce the numbers.  They prove no new
mathematics — the `decide`s assert computations against **data-generated
certificate lists** (`tools/gen_packed_bench.py`); soundness transport is the
follow-up iteration described in the study, §6.

## How to run (and what it costs)

Build explicitly with the `Bench` library (defined in `lakefile.toml`, absent
from `defaultTargets`), e.g. via the Modal check script:

```bash
/home/doz/dozenv/bin/modal run lean_check.py --target Bench.Packed.BBenchPackedBal
```

All measurements below: 2 CPU / 32 GiB-request Modal container, Lean
`v4.36.0-rc1` (see the study for curves and methodology).

### `Bench/Packed/` — these PASS, kernel-verified

| module | checks | result | cost |
|---|---|---|---|
| `Bench.Packed.BBenchPacked` | packed v1 (linear pack): `1024 + 4096 + 16384` nonvanishing | ✔ all three | 174 s kernel, **41 GiB peak** |
| `Bench.Packed.BBenchPackedBal` | packed v2 (balanced): `16384 + 65536` nonvanishing | ✔ both | 662 s kernel, **60 GiB peak — needs > 64 GiB RAM** |
| `Bench.Packed.BBenchPack` | isolated pack probe: linear vs balanced at 16384 | ✔ | 43 s, 6.4 GiB |

`BBenchPackedBal` is the feasibility evidence for the 65536 bound: it is the
file that must be re-run (never imported!) whenever the packed scheme changes.
Each file already sets the required `maxHeartbeats`/`maxRecDepth`.

### `Bench/Failing/` — these FAIL **by design**; do not "fix" them

They are the measured *failure points* cited by the study; a build failure is
their expected outcome, not a bug.

| module | probes | dies with (by design) |
|---|---|---|
| `Bench.Failing.BBenchScale` | unforced list arithmetic @ 768 | `(kernel) deterministic timeout` after > 363 s at > 39.5 GiB |
| `Bench.Failing.BBenchList` | strict-forced list arithmetic @ 1024 | `(kernel) deterministic timeout` after > 305 s at > 34.6 GiB |
| `Bench.Failing.BBenchBurn` | retention law at constant live set | `(kernel) deep recursion` — and its RSS ramp (≈ linear in steps) is the point |

## Rules

1. **Never import these modules into `MathProof.lean`** — `BBenchPackedBal`
   alone would put an ~11-minute, 60 GiB kernel decide into every full build.
2. Keep them out of CI (already the case: CI builds explicit `MathProof.*`
   targets only).
3. The two `BBenchPacked*` files are generated — edit
   [`tools/gen_packed_bench.py`](../tools/gen_packed_bench.py) and regenerate
   (`python3 tools/gen_packed_bench.py`), don't hand-edit the literals.  A
   wrong certificate makes the `decide` fail, never pass.
