# Mathlib version strategy (decided 2026-11-01)

Question (operator): we pin Mathlib while TauCeti floats a newer commit —
what should our version strategy be, given the local-checkout / Modal-cache /
multi-agent workflow, and that newer Mathlib may carry lemmas we need?

## Facts (measured 2026-11-01)

| artifact | version |
|---|---|
| our pin (lakefile + lean-toolchain) | `v4.36.0-rc1` (Lean and Mathlib in lockstep) |
| latest Mathlib **stable** tag | `v4.35.0` — **no `v4.36.0` stable yet**; `v4.36.0-rc2` is out |
| TauCeti | toolchain `v4.36.0-rc1` (**same as ours**), Mathlib pinned to a *commit* (`2cabef97…`) ahead of the rc1 snapshot |
| our encore checkout (`~/zcode-workdir/encore-mathlib`) | Mathlib master @ `312e0b7a` (2026-10-29) — the prospective-search mirror |
| our local `.lake/packages/mathlib` | the pin, with oleans (~7.3 GB, hardlinked into worktrees) |
| Modal image | baked at the manifest's exact revisions + full Mathlib olean cache (shared layer cache across `lean_check.py`/`lean_build.py`) |

So we are on the *newest cycle's rc1* — not lagging releases; we lag only
master commits and the rc2 point release.

## The strategy: pin per iteration, bump at iteration boundaries

**Stay pinned — never float.**  Everything in this workflow keys on the pin:
kernel-decide reproducibility (the 200 s kernel budget and heartbeat budgets
are version-sensitive, and our heaviest certificates sit near them), the
Modal warm image (baked at exact revisions), the volume's rolling build cache
(lake hash traces include the dependency revisions), CI reproducibility, and
the multi-agent waves (every worktree hardlinks the same `.lake`; every
blueprint cites "verified at this pin").  Floating (TauCeti-style commit
pins) is right for a study project with bors CI; for us it would fragment
caches across agents and resurrect the wrong-ref grep failure class.

**Bump exactly once per iteration, at the boundary** (after wave close, before
the next blueprints) — plus two off-cycle triggers:
1. a blueprint-blocking lemma exists only in newer Mathlib (found in recon,
   below), or
2. a measured bug/regression at our pin.
Never mid-iteration: each active worktree would re-fetch ~7 GB, every
measured number goes stale, and in-flight branches diverge on imports.

**Target selection**: newest *stable* tag available at the boundary
(today that means waiting for `v4.36.0` stable; rc1→rc2 only if recon shows
a fix we specifically need — rc→stable of the same cycle is the cheapest
meaningful upgrade).  Lag budget: stay within one release cycle of latest
stable so each bump stays small.

## The bump procedure (checklist; make `tools/bump_mathlib.sh` when first used)

1. `lake update` to the target tag + matching `lean-toolchain` bump; commit
   the pin change **alone** (revert-able in one commit).
2. Local: `lake exe cache get` (~7 GB), light build green for what fits RAM,
   `tools/tauceti_audit.sh`.
3. Modal: rebuild the shared image — both `lean_check.py` and
   `lean_build.py`, kept definition-identical (AGENTS.md rule); ~15 min,
   one-time.
4. First `modal run` after the bump rebuilds the whole project into the
   volume cache (~1–2 h light library; the heavy `MaedaGalois5` chain adds
   ~33 min if its results are needed — schedule bumps *after* a heavy-chain
   verification, never before).
5. Re-run the audit suite: `AxCheckDecide` (expect the same counts),
   `MaedaGaloisFullAxCheck`, and watch the 16 GiB memory alert (Lean
   versions shift memory profiles).
6. Record before/after per module: build time, peak RSS, biggest decide
   timings.  Kernel speedups can move things *across* the 200 s budget line
   in either direction — this measurement is a feature, not bookkeeping
   (e.g. a faster kernel could un-stick the `zpgcd` deep-recursion limit
   that forced the Bézout detour, or make dim-11 viable).

Expected total cost per bump: ~2–3 h mostly unattended.  Once per iteration
this is noise; mid-iteration it would be paid per worktree.

## The recon step (every iteration, before authoring blueprints)

`git -C ~/zcode-workdir/encore-mathlib/repo/mathlib4 log v4.36.0-rc1..master
-- <areas>` for the areas we live in: `FieldTheory/Finite`,
`RingTheory/Frobenius`, `RingTheory/Polynomial`, `GroupTheory/GroupAction/`
(Jordan!), `LinearAlgebra/Matrix/Charpoly`, `Tactic/NormDet`/`norm_num`,
`Analysis/SpecialFunctions/ModularForm`.  Maintain a **Mathlib wishlist** in
`research/` (seed it with: primitive-Jordan/Wielandt 13.9; level-one Hecke
operators T_m; q-expansion injectivity variants; `exponentiation.threshold`
 configurability; faster ZMod polynomial arithmetic) and check every item
against pin and master.  This converts "Mathlib lacks X" from an assumption
into a checked fact — the exact failure mode that cost us the golden-lemma
detour in Iteration 21 (`IsArithFrobAt` existed, under an unguessable name,
the whole time).

Discipline for the two checkouts (unchanged, now explicit):
`.lake/packages/mathlib` is the **only** API truth for proof-writing;
the encore master checkout is **prospective only** — anything found there is
"verify at pin", usable the moment a bump lands.  TauCeti stays a
standards-reference, never an API source (its floating commit is exactly why).

## Why not chase master for the lemmas we need?

Tempting (a needed lemma is a `lake update` away), but: master moves daily
(no olean cache on the CDN → full Mathlib from source, hours, on every
worktree and in the Modal image); API churn under us mid-wave; and the recon
step gets us 90 % of the benefit (knowing what exists, planning around it,
bumping deliberately at the boundary).  If a single lemma truly blocks a
blueprint, the sanctioned escape is the off-cycle trigger — bump once,
deliberately, to the tag containing it, paying the checklist cost with eyes
open.

## First action

At the Iteration-22 boundary: check for `v4.36.0` stable; if cut, run the
checklist to it (rc1→stable, minimal churn, likely kernel fixes since rc1);
if not, run recon against rc2 + master and decide whether rc2 earns its
checklist or we wait for stable.
