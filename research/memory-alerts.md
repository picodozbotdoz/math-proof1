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
| `MaedaGalois5IdE4` | 202 GiB | 2,545-term certificate, yet more memory than `IdE6` (10,780 terms, 172 GiB): the decide is likely not the driver — suspect the `*_eval` / `theta_e4` elaboration (`simp` + `ring` over Horner text).  Improvements doc P1-3. |
| `MaedaGalois5IdE6` | 172 GiB | as above |
| `MaedaGalois5IdE5` | 137 GiB | as above |
| `LehmerPow32` | 143.8 GiB | one kernel `decide` over 65,535 recursion chains (AGENTS.md) |
| `LehmerPacked` (65536 bound) | ~63 GiB | just under the threshold; kernel decide heap |

- investigation: _pending — profile `MathProof.ModularForms.MaedaGalois5IdE4`
  first (≈ 40 min, ≈ 200 GiB; needs the owner's OK for the Modal spend)._
