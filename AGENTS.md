# AGENTS.md — MathProof

Autonomous research workspace for the **Langlands program / modular forms**: each
iteration of the research loop picks an open problem and contributes *formally
verified* mathematics in Lean 4 + Mathlib. The standard of proof is strict: no
`sorry`, no `native_decide`, no external CAS — computations must be verified by
Lean's kernel alone (`decide`).

## Build

Toolchain and Mathlib are pinned (`lean-toolchain`, `lakefile.toml`: Lean
`v4.36.0-rc1`, Mathlib `v4.36.0-rc1`).

```bash
lake build                          # everything (Mathlib cache: ~7 GB disk)
lake build MathProof.Tau.Lehmer     # build a single module
```

Heavy kernel computations are slow: `MathProof.Tau.Lehmer` takes ~2 CPU-minutes
of kernel time. Prefer building individual modules while iterating.

## Layout

- `MathProof/Tau/Basic.lean` — `Ramanujan.tau`: algebraic definition of τ
  (coefficients of `Δ = q ∏ (1 − q^m)^24`), truncation stability, hand-rolled
  kernel-friendly `List ℤ` arithmetic (`pmul`, `psub`, `pow24`, …), verified
  values `tau_one` … `tau_twenty_one`.
- `MathProof/Tau/Lehmer.lean` — Lehmer's conjecture: `tau_ne_zero_of_le_256`
  (kernel-verified nonvanishing for `n ≤ 256`).
- `MathProof/Tau/LehmerMod.lean` — work in progress (untracked): same list
  arithmetic mod `P = 999999937`, raising the verified bound to 512.
- `MathProof/Tau/Bridge.lean` — the analytic bridge: `(qExpansion 1 Δ).coeff n = τ n`
  for Mathlib's analytic discriminant `Δ`.
- `MathProof/ModularForms/Weight12.lean` — Ramanujan's weight-12 identity
  `691 • E₁₂ = 441 • E₄³ + 250 • E₆²` via the Sturm bound; exports
  `E12_qExpansion_coeff` and Bernoulli evaluations `B₄, B₆, B₁₂`.
- `MathProof/ModularForms/Congruence691.lean` — `tau_modEq_sigma`:
  `τ n ≡ σ₁₁ n [ZMOD 691]`.
- `MathProof.lean` — root import file. **Every new module must be added here.**
- `docs/research-log.md` — the research loop log. Each iteration is recorded
  here (problem, contributions, next steps); update it (and `README.md`)
  when completing an iteration.
- `langlands-site/index.html` — standalone single-file educational web page
  (GL₂ Langlands by example). Self-contained by design: no network requests,
  no CDN. Preview with `python3 -m http.server` from that directory.

## Conventions and gotchas

- Everything τ-related lives in `namespace Ramanujan`; files `open Polynomial`.
- **Kernel-reducibility is the central engineering constraint.** The hand-rolled
  list arithmetic must be defined structurally: a naive definition can silently
  compile to well-founded recursion (`Acc.rec`), which the kernel cannot reduce,
  breaking every `decide`. Keep list functions structurally recursive; verify
  `decide` still works after touching them.
- Lakefile options: `relaxedAutoImplicit = false`, `linter.mathlibStandardSet = true`,
  Mathlib-style copyright headers disabled. No `autoImplicit` tricks.
- `decide` / `norm_num [bernoulli]` time out on Mathlib's well-founded Bernoulli
  definition — `Weight12.lean` chains the defining recurrence instead; reuse it.
- Mod-P computations (`LehmerMod.lean`) keep every intermediate below `2^60` by
  reducing `% P` after each operation; soundness is proved by transporting into
  `ZMod P` (mirror `L2P` as `L2PMod`). A nonzero residue mod a prime certifies
  the integer coefficient is nonzero — no magnitude bound needed.
- CI (`.github/workflows/lean_action_ci.yml`) runs `lean-action` + docgen on
  every push; keep `lake build` clean before committing.
