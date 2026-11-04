# Iteration 24 — working notes

Theme (iteration23-review §6.1–6.3 → §7.2): **close the Hecke index** —
`[𝕋 : ℤ[T₂]] = I_k` as a lattice index, `D = I_k` at dims 3–4,
`𝕋 = ℤ[T₂] ⟺ I_k = 1`, and the dims-5–10 probe of which `T_m` carry the
rest of `I_k`.

## INIT (2026-11-04)

- Trunk `dev/iteration24-hecke-index` from `dev/zai` 229e326 (master ec9a2f0
  + the stuck-worker-protocol commit; everything of Iteration 23 included).
- **Recon (pin freshness): no `v4.36.0` stable yet** (rc2 latest; stable =
  v4.35.0). Commits rc1→master in our areas are refactors (`IsApply` for
  `Module.Basis`/`Module.End` = rename churn), no blueprint-blocking lemma.
  **Decision: stay at `v4.36.0-rc1`** (mathlib-version-strategy: bump only at
  a boundary to the newest stable; waiting for `v4.36.0` stable).
- **CI push-tier measurement (iteration23-review rec 1)**: first master push
  under the selective CI (ec9a2f0, 2026-11-03 03:29, Lean-touching, new push
  tier) = **2.0 min, success** (old regime: 51 min docs push, 77 min
  ancestor-edit push). Weekly full tier not yet observed (first fire
  Mon 2026-11-09 03:00 UTC). No action — far under the 15 min watch line.
- Inbox at session start: empty (no `STEER-*` pending).
