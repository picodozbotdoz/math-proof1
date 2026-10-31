# Iteration 20 — S3 handoff (for the next AI session)

Written 2026-10-31 at the S2/S3 boundary, per operator instruction ("after S2
complete, take a break before continuing to S3").  Everything needed to resume
S3 is in this file; the plan is `research/iteration20-plan.md` (S1/S2 checked).

## Where things stand

Branch `dev/iteration20-maeda-dim6-10`, master untouched, heavy chain
untouched.  Commits in order:

| commit | content |
|---|---|
| `bdc4941` | plan + census data consolidated into `research/iteration20/` (probe re-runs byte-identically) |
| `57656b0` | `CharpolyDimN.lean` — **BUT this commit has the superseded Fin-indexed shape** |
| this commit | `CharpolyDimN.lean` **ℕ-indexed restructure** (required by the generator; compiles clean locally, 0 err/warn, NOT yet Modal-re-verified), `tools/gen_maedan.py`, WIP `MaedaDim6Weights.lean` (does **not** compile yet), this handoff |

Stage status: **S0/S1/S2 done — S3 not started** (the generated dim-6 file
fails with ~66 errors whose causes are all identified, below).

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

## Current dim-6 error state (66 errors, all causes identified)

Error classes in `MaedaDim6Weights.lean` (line numbers of the current
uncommitted-then-committed WIP; regenerate before trusting them):

1. **hevals (~985, "No goals")**: the per-case `show`-normalization bullets
   (added for the fin_cases cast-chains) — inspect alignment; some cases may
   close by `show` alone (rfl) leaving "No goals" for the `rw`-bullet — merge
   the show into the rw-bullet or drop bullets that are already closed.
2. **charpoly_T2 (~994)**: `charpoly_of_eval_eq` unknown — emit
   `CharpolyEngine.charpoly_of_eval_eq`.
3. **Entry bridge (~1110-1142)**: `simp only [coordN, coordsAux, Atab, Xtab]`
   + `norm_num [Matrix.map_apply, M, List.getD…]` — "maximum recursion depth"
   on some entries, "simp made no progress" on others.  Candidates, in order:
   (a) split the simp-only into staged unrollings (`coordN, coordsAux` first,
   then `Atab, Xtab`), (b) `norm_num` with the full lemma list instead of the
   preceding simp-only, (c) if depth still trips, emit per-entry helper lemmas
   `coordN Atab (fun m => Xtab a m) c = literal` proved by staged unrolling
   (module boundaries are free; nothing decides on coordN).  The `show`
   targets are already fully literal, so the entry goal is elementary.
4. **Rabin block (~1153)**: `Fact (107.Prime)` → `Fact (Nat.Prime 107)`.
5. **h2 dispatch (~6831 for k=76, same class at k=72)**: `interval_cases q`
   yields 7 cases (q ≤ 6 from `hqb`); the emitted 3 bullets are wrong.  Emit
   **7 explicit bullets**: for `q ∈ primeDivisors n` → `exact h2_{q}`; else →
   `exact absurd hq (by norm_num)` — **refute via `hq : Nat.Prime q`, NOT
   `hq2`** (q = 6 divides 6; q = 0/1/4 fail primality, and `Nat.Prime` is
   decidable by `norm_num`/`decide` on literals).
6. Everything before ~967 (the basis, q/t-lemmas, discharges, M/P/dets/evals
   up to the hevals shows) **compiles** — do not restructure those.

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
* Cost sanity: dim-6 file ≈ 6.9k lines / 6 weights; CI ≈ a few min/file.
  The dim-10 decides are the only kernel-time risk.

## Invariants

* No heavy-chain contact: nothing under `MaedaGalois5Defs`' ancestor set is
  edited; `CharpolyDimN`/generated files import `MaedaLevelOne` but are
  imported by nothing heavy.
* No `set_option`, no `#eval`/meta/unsafe in the light modules (TauCeti);
  all certificates are `decide +kernel`.
* Never hand-edit generated files; the generator is the single source.
* Commit only the generator + generated files together, `--check` first.
