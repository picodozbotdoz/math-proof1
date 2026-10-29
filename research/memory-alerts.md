# Memory alerts

Policy (AGENTS.md, "Memory alerts"): every Lean build whose `lake` tree
reaches **64 GiB** RSS is investigated.  `tools/modal_run.sh` appends each
`[memory-alert]` here as an **OPEN** entry; the investigation runs
`LEAN_CHECK_PROFILE=<Module> tools/modal_run.sh`, records the top
declarations (`[profile]` lines) and the cause, and marks the entry
**CLOSED** with the fix or the reason the cost is inherent.

Entries are newest last.

## Backlog (measured before the policy) — OPEN

Builds that crossed 64 GiB before the tooling existed; numbers from
`research/research-log.md` and `research/iteration18-review.md`.

| module | peak RSS (measured) | known so far |
|---|---|---|
| `MaedaGalois5IdE4` | 202 GiB | first guess (elaboration of `*_eval` / `theta_e4`) was wrong — it is the kernel `decide`; see below |
| `MaedaGalois5IdE6` | 172 GiB | as above |
| `MaedaGalois5IdE5` | 137 GiB | as above |
| `LehmerPow32` | 143.8 GiB | one kernel `decide` over 65,535 recursion chains (AGENTS.md) |
| `LehmerPacked` (65536 bound) | ~63 GiB | just under the threshold; kernel decide heap |

- investigation (2026-10-29), **CLOSED for the `MaedaGalois5Id*` rows** —
  `research/poly5-memory-study/README.md`.  Cause: the kernel `decide`
  certificates (`e3dec` +18.5 of 24.5 GiB in `IdBase`; bridge lemmas ≈ 0);
  kernel memory ≈ 27 GiB per million `Poly5` list operations in one
  declaration (fits e2…e6 and δ² within 21–32).  E4 is worst because its
  left side is 15 brute-force products.  Fix (prototyped, measured): left
  side by the e_k recurrence + LHS/RHS checked against one literal in
  separate declarations — E4 202 → 19.0 GiB (2343 → 221 s), E6 172 →
  63.2 GiB (2207 → 1414 s; ≈ 35 GiB expected after one more RHS split).
  **Rolled out 2026-10-29** (chain regenerated and rebuilt): IdBase 8.1,
  IdE4 13.5, IdE5 22.0, IdE6 34.7, Identities 17.6 GiB — every module below
  the threshold.
- `LehmerPow32` / `LehmerPacked`: not yet investigated (same tooling).
