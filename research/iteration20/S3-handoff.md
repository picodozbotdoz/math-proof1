# Iteration 20 — S3 handoff (for the next AI session)

Written 2026-10-31 at the S2/S3 boundary, per operator instruction ("after S2
complete, take a break before continuing to S3").  Everything needed to resume
S3 is in this file; the plan is `research/iteration20-plan.md` (S1/S2/S3 checked).

## Where things stand

Branch `dev/iteration20-maeda-dim6-10`, master untouched, heavy chain
untouched.  Commits in order:

| commit | content |
|---|---|
| `bdc4941` | plan + census data consolidated into `research/iteration20/` (probe re-runs byte-identically) |
| `57656b0` | `CharpolyDimN.lean` — **BUT this commit has the superseded Fin-indexed shape** |
| this commit | `CharpolyDimN.lean` **ℕ-indexed restructure** (required by the generator; compiles clean locally, 0 err/warn, NOT yet Modal-re-verified), `tools/gen_maedan.py`, WIP `MaedaDim6Weights.lean` (does **not** compile yet), this handoff |

Stage status: **S0/S1/S2/S3 done — S4 (dims 7–10) is next.**  The dim-6 file
(`MaedaDim6Weights.lean`, 8174 lines) is fully verified: local 0 err/0 warn,
`--only 6 --check` byte-identical, Modal `--file` green **with zero style
warnings** (6.6 GiB peak, 130 s), `tauceti_audit.sh` clean, and the ℕ-indexed
`CharpolyDimN` is Modal-verified.  The five error classes below are RESOLVED —
the resolutions and the new gotchas they surfaced are in §"S3 outcome" at the
bottom; read that section before S4.

TauCeti Coding rules and math-proof1 lesson learnt can be found in `external-doc/TAU-CETI_Coding_Rules.md`

## Re-entry procedure (exact commands)

```bash
cd /home/doz/claude-workdir/math-proof1_2
git checkout dev/iteration20-maeda-dim6-10          # if not already there
lake build MathProof.ModularForms.CharpolyDimN      # MANDATORY (gotcha 15)
python3 -I tools/gen_maedan.py --only 6             # regenerate byte-identically
timeout 2400 lake env lean MathProof/ModularForms/MaedaDim6Weights.lean 2>&1 | grep error | head
```

Iterate by fixing **`tools/gen_maedan.py` and regenerating** — never hand-edit
`MaedaDim6Weights.lean` (byte-identical rule; `python3 -I tools/gen_maedan.py
--only 6 --check` verifies).  When green locally:

```bash
tools/modal_run.sh --file MathProof/ModularForms/MaedaDim6Weights.lean   # linters on; fix show→change if flagged
tools/tauceti_audit.sh                                                   # no set_option/#eval/meta in light modules
python3 -I tools/gen_maedan.py --only 7   # then 8, 9, 10 (S4), one file at a time
```

**Step 0 for S3**: Modal-re-verify the ℕ-indexed `CharpolyDimN`
(`tools/modal_run.sh --file MathProof/ModularForms/CharpolyDimN.lean`) — only
the superseded Fin-version was Modal-verified.

## The pipeline design (do not relitigate)

* `charpoly_dimN` (CharpolyDimN.lean) has **ℕ-indexed hypotheses**:
  `f : ℕ → CuspForm 𝒮ℒ k`, `hzero/hone/hA/hX` guarded by `i < n`.  The first
  Fin-indexed version forced `fin_cases`-coercion atoms that `omega` cannot
  see through (gotcha 3); the ℕ-version compiled first-try.  The emitted
  `fb : ℕ → CuspForm` is a match with literal arms `| 0 => f1 … | _ => 0`
  (catch-all never read for `i < n`).
* `N = 2n+1`; **`seqPLc i a b N` has length N** (coefficients `0..N-1`) — the
  emitted lists are `series[:N]`.  q-lemmas cover `m ∈ [1, 2n]`, t-lemmas
  `m ∈ [1, n]`.  (Values verified against `#eval seqPLc …` — an earlier
  off-by-one produced `decide`-false, fixed.)
* Tables are named **`Atab`/`Xtab`** — bare `X` collides with `Polynomial.X`.
  `p_literal` ascribes `(X : ℤ[X])` everywhere.
* Per weight the file emits: basis defs + `c/Lc/L/q/t` lemmas → `fb/Atab/Xtab`
  → `finrank_eq` (dimension_level_one template) → the four discharges →
  `M/MT/scalar_sub_M` + `P` + per-point `det_t`/`ev_t` → `hevals` →
  `charpoly_T2` → Rabin block (`fr/hmap/hmon'/hnd/hF/h1/h2_q/h2/fr2/h1_2`) →
  `maeda`.  The Python side asserts the recomputed T₂-matrix/charpoly agree
  with the census JSON (which regresses against the proved k=24/48).
* Discharges use `interval_cases i` (plain ℕ bound from the guard) +
  `interval_cases m` + per-case `rw [c_j, seqP_getD (N := N) (by norm_num),
  L_j]; norm_num [List.getD_cons_succ, List.getD_cons_zero]`.

## Lean gotchas discovered this session (pin v4.36.0-rc1) — the gold

1. **omega does NOT see `Finset.mem_range` hypotheses** — derive the fact
   explicitly (`Finset.mem_range.mp hx` / `mem_range_succ`), never `by omega`
   against membership.
2. **omega does not reduce fin_cases cast-chains or Fin-literal values**
   (`↑↑((fun i => i) ⟨0, ⋯⟩)` is an opaque atom) — normalize per case with
   `show`/`have hiv : … := rfl`, or avoid Fin in hypothesis positions
   (→ the ℕ-restructure).
3. **`rw` does not match `Nat.succ m` (from `induction`) against `m + 1`** —
   kabstract stops at the non-reducible `HAdd`.  Fix with `show`-goal
   normalization or `simp only` (which normalizes).
4. **`rw [hpt]` can fail where `simp only [hpt]` works** on sum-goals (same
   quirk class); prefer `simp only` for hypothesis-shaped rewrites under binders.
5. **`interval_cases` auto-closes cases where a hypothesis becomes literally
   false** — emit bullets ONLY for surviving cases (e.g. drop the `m = 0`
   bullet when `h1 : 1 ≤ m` is in scope; drop `jj ≤ i₀` bullets under
   `hij : i₀ < jj`).  Misaligned bullets surface as "No goals to be solved".
6. **`interval_cases` needs a plain ℕ bound hypothesis** — derive it first
   (`have hib : i < n := by omega`), never rely on chained hypotheses or
   Fin-coercions.
7. **`fin_cases` on an unbounded ℕ variable fails** — derive the bound first.
8. **Contradiction idiom**: `(by omega : False).elim` works;
   `absurd (by omega : False) (by trivial)` does NOT (`trivial` can't prove
   `¬False`).
9. **`rw [def, dite_eq_left hx]` fails on un-beta-reduced applications** — use
   `simp only [def, dite_eq_left hx]`.
10. `add_sub_cancel_left` (not `_right`) cancels `(S + T) - S`.
11. **Module-doc goes AFTER imports** (Lean 4 rejects imports after `/-! … -/`).
12. **`107.Prime` is a lexer error** ("unexpected identifier after decimal
    point") — write `Fact (Nat.Prime 107)`.
13. List-wrapping in generated lists must keep trailing commas on continued
    lines.
14. Modal linters run on `--file` builds: `show` that changes the goal must be
    `change` (fixed in CharpolyDimN already).
15. **`lake env lean <file>` needs the imported modules' oleans** — run
    `lake build MathProof.ModularForms.CharpolyDimN` after any edit to it, or
    the generated file compiles against a stale interface (this bit once:
    the ℕ-version vs the committed Fin-olean).
16. `charpoly_of_eval_eq` lives in `namespace CharpolyEngine` — qualify it.

## S3 outcome (2026-10-31, same session — resolutions of the 66 errors)

All five classes below are FIXED in `tools/gen_maedan.py` (the fixes, not the
diagnoses, are what S4 inherits).  New gotchas discovered while fixing:

17. **`interval_cases` does NOT auto-close primality/divisibility literals**
    (only linear contradictions): the h2 dispatch needs **n+1 explicit
    bullets** for q = 0..n — `exact h2_{q}` for q ∈ primeDivisors n;
    `exact absurd hq (by decide)` for composite q (0, 1, 4, 6 when n = 6);
    `exact absurd hq2 (by decide)` for prime q with q ∤ n (q = 5 when n = 6 —
    refuting via `hq` would be decide-false since `Nat.Prime 5` holds).
18. **hmap cannot go through `norm_num`'s cast normalization**: every path
    collapses `↑(ofNat-literal)` to a ZMod numeral *before* the mod-reduction
    fires, and Mathlib has no ZMod-numeral reducer.  Working pipeline (per
    weight): `simp only [P, toPoly_nil, toPoly_cons, fr, map_C, map_X,
    map_add, map_mul, map_pow, Int.coe_castRingHom, ← Polynomial.C_neg]`
    (note: `← C_neg` at the ℤ[X] level makes negative coefficients
    `C (-c)`, so `map_neg`/`← Int.cast_neg` are never needed), then a `rw`
    chain of per-coefficient `show ((c : ℤ) : ZMod ℓ) = (c mod ℓ : ZMod ℓ)
    from by decide +kernel` (kernel-decidable, trivial cost), then `ring_nf`.
19. **P's leading term must be emitted as `C (1) * X ^ n`** (not bare
    `X ^ n`): after mapping, both hmap sides then carry the identical atom
    `C ↑1`, which `ring_nf` matches — it cannot equate `C ↑1` with the bare
    numeral 1.
20. **hmon'/hnd need the Horner zero-tail folded**: `simp only
    [toPoly_nil, toPoly_cons, fr, mul_zero, add_zero]` before `monicity!` /
    `compute_degree!` (the `X * 0` tail otherwise registers naïve degree n+1).
21. **`simp only [toPoly]` makes no progress** (the def is noncomputable —
    no usable equation lemmas): use the `rfl`-lemmas `toPoly_nil` /
    `toPoly_cons`.
22. **Cumulative heartbeats killed the 36-entry bridge inside one
    `charpoly_T2`** (whnf timeout at entry ~25): the entries are now separate
    `theorem entry_{c}_{a}` declarations (fresh budget each — the `r5c*`
    pattern), discharged in the main proof by `change …; exact entry_{c}_{a}`.
    Rows c ≥ 2 additionally need `Finset.sum_range_succ, Finset.sum_range_zero`
    in the entry's simp set (the range-sum under a binder doesn't split by
    itself); the c = 0 row omits `sum_range_succ` (unused-arg linter).
23. **`maeda` needs `haveI`** (plain `have` doesn't register the `Fact`
    instance) and the full argument order `P_monic hmap hmon' hnd (by
    norm_num) hF h1 h2` (`hF` was missing).
24. **`lake env lean` runs NO style linters** — the Mathlib set
    (linter.style.longLine / .show) only fires under `lake build` / Modal
    `--file`.  Requirements the generator now enforces: every line ≤ 100
    *characters* (ℤ is 3 bytes — measure chars, not bytes); tactic `show` →
    `change`; `ring` → `ring_nf` (plain `ring` closes hmap but emits a
    "Try this: ring_nf" info on every weight).
25. **hevals is `∀ i : Fin (n+1)`** (the engine wants n+1 evaluation points)
    while the `Matrix.scalar` inside stays `Fin n` — the original `Fin n`
    quantifier left the 7th bullet goalless.

## After dim 6 is green (S3 → S4 → S5 → S6)

* S3 acceptance: `lake env lean` clean (0 err/warn), `--only 6 --check`
  byte-identical, Modal green, `tauceti_audit.sh` clean, then commit.

## After dim 6 is green (S3 → S4 → S5 → S6)

* S3 acceptance: `lake env lean` clean (0 err/warn), `--only 6 --check`
  byte-identical, Modal green, `tauceti_audit.sh` clean, then commit.
* S4: `python3 -I tools/gen_maedan.py --only {7,8,9,10}` one at a time; the
  generator already handles all dims (N = 2n+1 scales; dim-10 has 200-digit
  charpoly literals — spot-check `lake env lean` locally per file, then
  Modal).  Watch the biggest Rabin decide (k=120, ℓ=293, ~28k ZMod-muls) for
  kernel time; split certificates rather than raising any option.
* S5: register all six modules in `MathProof.lean`, `lakefile.toml`
  (defaultTargets), CI list; run `MathProof/AxCheckDecide.lean` on Modal —
  target `propext`-only for every new decide; `tools/tauceti_audit.sh`.
* S6: research log entry, README results table, AGENTS.md layout lines,
  merge to master.
* Cost sanity: dim-6 file is 8174 lines / 6 weights (Modal 130 s, 6.6 GiB); CI ≈ a few min/file.
  The dim-10 decides are the only kernel-time risk.

## Invariants

* No heavy-chain contact: nothing under `MaedaGalois5Defs`' ancestor set is
  edited; `CharpolyDimN`/generated files import `MaedaLevelOne` but are
  imported by nothing heavy.
* No `set_option`, no `#eval`/meta/unsafe in the light modules (TauCeti);
  all certificates are `decide +kernel`.
* Never hand-edit generated files; the generator is the single source.
* Commit only the generator + generated files together, `--check` first.
