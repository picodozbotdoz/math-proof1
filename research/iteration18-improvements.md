# Iteration 18 — review summary and improvement proposal

Source: `research/iteration18-review.md` (Parts I–IV, §1–34) and the repo as
of branch `review/iteration-18` (`5adfcb0`).  This document is a proposal only:
no code was changed, no build was run.  Numbers marked **(measured)** come from
the review or `research/research-log.md`; numbers marked **(est.)** are my
estimates.

---

## 1. Summary

### The seven lessons that matter most

1. **`ring` has a hard wall, so plan large identities as kernel certificates from
   the start** (§1, §2, §20).  `ring` handles about 250 expanded terms /
   degree 8 (≈2.5 GB, measured).  The e₄–e₆ and discriminant identities died
   at 46–323 GiB.  What worked: structural sparse polynomials (`Poly5`),
   Horner-form chains, `decide +kernel`, and `PEval` hom lemmas to transport
   the result.
2. **The kernel has its own contracts: structural recursion, tail-recursive
   `Bool` checks, and a small left operand** (§9, §2, §27).  Three things
   break kernel evaluation:
   - Non-structural recursion compiles to `Acc.rec` and silently stops it.
   - `List`'s `DecidableEq` uses one native stack frame per element, so `pBeq`
     plus `eq_of_pBeq` is needed past a few thousand terms.
   - The stack for `pMul p q` grows with `len p` (2,445-term left factor
     failed, 218 passed).
3. **Classify an error before raising a limit** (§27).
   - Kernel "deep recursion" → restructure the data.
   - Elaborator recursion → `maxRecDepth`; it can masquerade as
     `failed to synthesize HPow …`.
   - Heartbeats → a per-declaration budget.
   - "decide proved … is false" → a math or generator bug.  This one cost a
     4,225 s build (measured).
4. **Keep two worlds and one bridge for computability** (§10, §28).
   `Polynomial`, `ModularForm` and anything built from them are
   noncomputable.  Each certificate therefore has three parts:
   - an explicit noncomputable object (`R : ℤ[X]`);
   - a computable mirror (`Rmod` over `ZMod ℓ`, decided by `decide +kernel`);
   - a `simp` bridge lemma linking the two.
5. **Most lost round trips were API drift, not missing math** (§11, §17, §29).
   The causes were renames (`not_mem`→`notMem`), namespace moves and binder
   changes.  The pinned Mathlib is checked out locally at the manifest
   revision, so `grep` it before every Modal run: grepping takes seconds, a
   Modal run takes 3–17 minutes.
6. **Small goals and one heavy identity per module** (§2.6, §20, §33).  Many
   small `ring`/`decide` goals beat one big one.  Module boundaries free
   elaboration memory.  With the rolling cache, a staged chain is resumable:
   fixing E6 reused E4/E5, about 65 min per round (measured).  This only
   works if the generator emits unchanged modules byte-identically.
7. **Python-first, generator lint, batched fixes** (§2.3, §6, §23, §24).
   Verify the math in Python, lint the generated Lean (parens, commas,
   comment depth, `set_option`/docstring order), and fix every understood
   error per round.  Ten criterion rounds at 8–17 min each (measured) were
   bounded by error maps, not compute.

### Contradictions between parts — which claim to follow

| stale claim | correct claim | evidence |
|---|---|---|
| §5: no `Fin.prod_univ_six`; use the castSucc chain (§18) | `Fin.prod_univ_six` exists | §26; `MaedaGalois5.lean` `resolvent_eval_theta` |
| §5, §17: hand-roll `index ≠ 0` and `N = ⊤` | `Subgroup.index_ne_zero_of_finite`, `Subgroup.eq_top_of_card_eq` | §26, §29 |
| §19: `set_option a in set_option b in decl` does not parse | It parses; the docstring placement was the error | §26; `MaedaGalois5IdE6.theta_e6` |
| §3: drive `if` with `rw [if_pos h]` | `simp only [h, ↓reduceIte]` (`if_pos` deprecated, §11) | §26; `Poly5.lean` |
| §2: splicer `tools/split_gal5.py` | Deleted; `gen_poly5.py` emits the chain | §26 |
| §24: cache keyed by git HEAD, saved on success | One rolling tarball, saved after every run | §26, §33 |
| §2.6, §25.4: `MaedaGalois5` / `MaedaGalois5Weights` are light and in CI | **Heavy**: they import `MaedaGalois5Identities`; not in `defaultTargets`/CI (CLAUDE.md is correct) | `MaedaGalois5.lean` line 1; `lakefile.toml` |
| §20: the ∏-form "never elaborated"; prove eval-form per root with `fin_cases j; … ring` | What landed **is** the ∏ form (`Fin.prod_univ_six` + `sextic_vieta`), with each coefficient closed by `linear_combination theta_eK x` against the certified identities.  The blow-up was the monolithic `ring`, not the ∏ shape. | `resolvent_eval_theta` (§30) |
| §4: plain `decide`'s "result is not independently kernel-checked" | Every `decide` proof term is checked by the kernel when the declaration is added.  `+kernel` skips the *elaborator's* evaluation, which is what makes it fast or feasible.  **(Correction by this document; not in §26.)** | Lean 4 `decide` semantics |

New readers should treat Part IV §26 plus this table as the errata.

---

## 2. Improvement proposals

### P0 — blocks or endangers the next iteration

**P0-1. Make the build instructions match the Modal account that actually works.**
- *What*: AGENTS.md (§Build) and CLAUDE.md (axiom-audit command) still say to
  run `/home/doz/dozenv/bin/modal`, but that workspace is disabled.
  The only working path is `/tmp/ringlab/xyz_check.sh`
  plus `xyz_stage.sh`, and `/tmp` does not survive a reboot.
  - Move both scripts into the repo (e.g. `tools/modal_run.sh`,
    `tools/stage_chain.sh`), parameterized by `MODAL_BIN` and the mirror
    directory.
  - Document them in AGENTS.md as the canonical runner.
- *Why*: §33 (account migration).  Without the scripts, the next session
  rediscovers the rsync, chown and sudo mirror.
- *Effort*: S; no Modal build.
- *Done when*: a fresh clone contains the runner, AGENTS.md names it, and
  `tools/modal_run.sh --target MathProof.ModularForms.Poly5` succeeds.
- *Owner decision*: **yes**.  Which account is canonical (doz after top-up, or
  xyz), and whether xyz paths may appear in a committed file.

**P0-2. Protect the only built copy of the heavy chain.**
- *What*: today the ~1.9 h chain build (sum of the measured stage times
  461 + 209 + 2343 + 1498 + 2207 + 170 s) exists only inside the single rolling
  `/cache/buildcache/latest.tar.gz` in xyz's `lean-cache`.  Two runs overlap
  in a last-writer-wins way: both restore the same tarball and the later save
  replaces the earlier one, so one run's freshly built modules can be lost.
  1. Copy the tarball once to a second *file* in the same volume
     (`buildcache/iter18-chain.tar.gz`).  This is not a new Modal resource.
  2. Teach `lean_check.py` to fall back to it when `latest` is missing.
  3. Document "never run two heavy stages concurrently" in AGENTS.md.
- *Why*: §33.  Losing the tarball costs an estimated 2 h and peaks of
  202 GiB (measured E4).
- *Effort*: S; no rebuild.
- *Done when*: the snapshot exists, and the fallback restore is shown in one
  `lean_check` log line.
- *Owner decision*: confirm writing a second file to the existing volume.  I
  read the policy as allowing it; flagging anyway.

**P0-3. Request the memory the heavy stages actually use.**
- *What*: E4, E5 and E6 peaked at 202, 137 and 172 GiB **(measured)** against
  a 128 GiB request (`LEAN_CHECK_MEMORY_MIB=131072`).  It worked only because
  Modal's limit is soft.  Record per-stage memory in the committed stage
  runner (P0-1): ≥ 208 GiB for E4/E6 **(est., measured peak + margin)**, or
  accept and document the soft-limit risk.
- *Why*: §24, §33; AGENTS.md telemetry caveat.  An OOM-kill late in a stage
  wastes the whole stage (up to 39 min measured).
- *Effort*: S; it only matters at the next chain rebuild.
- *Done when*: the stage table in AGENTS.md lists the request and the
  measured peak per stage.
- *Owner decision*: **yes**.  Larger requests cost more credits per run.

**P0-4. Close the proof-standard audit gap for Iteration 18.** — **DONE 2026-10-29**: the twelve residue certificates now depend on no axioms (`HornerCert`); the project-wide audit (`AxCheckDecide`) found 116 older violations, see `research/research-log.md`.
- *What*: only the six `maeda_galois*` theorems have `#print axioms`.  The
  computational certificates have none: `e1dec … e6dec`, `ddec`, `noRootR`,
  `nonsquare`.  CLAUDE.md requires computational theorems to depend on
  `propext` only, and `MathProof/AxCheck.lean` has no Maeda entries.
  - Add a tiny heavy module, `MathProof/ModularForms/MaedaGalois5AxCheck.lean`,
    that imports `MaedaGalois5Weights` and prints axioms for every
    certificate.
  - Don't edit the `Id*` files: that would force a chain rebuild.
- *Why*: CLAUDE.md proof standard; §27 certificates.
- *Effort*: S.  It needs only the cached chain (one light-cost run, about
  7 GiB **(est.)**, if the cache is intact).
- *Done when*: the log shows `[propext]` (or nothing) for every `*dec`,
  `noRootR` and `nonsquare`, recorded in the research log.
- *Owner decision*: no.

### P1 — large savings for Iteration 19+ (dim ≥ 6)

**P1-1. Generator pre-flight lint plus a Python-side certificate self-check.**
- *What*: a shared `tools/lint_generated.py`, run by `gen_poly5.py`,
  `gen_galois5.py` and `gen_maeda.py` before writing.  It checks:
  - bracket/paren balance;
  - `/-` vs `-/` depth;
  - comma-joined `rw`/`simp` lists;
  - `set_option … in` / docstring order;
  - single definition per emitter helper;
  - byte-identical regeneration of committed files.

  In addition, each generator evaluates every emitted certificate equation
  (`ddec`-style) at random integer points in Python before emitting it.
- *Why*: the missing `]`, the false `ddec` (Δ vs Δ²) and the stray `ring`
  together cost one 4,225 s Identities build (measured, §27).  The emitter
  class of bugs in §6 and §23 each cost a Modal round trip.
- *Effort*: M; no Modal.
- *Done when*: re-running every generator reports clean, reproduces the
  committed files byte-identically, and a deliberately injected Δ-for-Δ²
  swap is caught locally.
- *Owner decision*: no.

**P1-2. Decouple the `S₅` criterion and instances from the heavy chain.**
- *What*: `MaedaGalois5.lean` imports `MaedaGalois5Identities`, so the
  criterion and Weights are heavy and out of CI, although they build in
  < 1 min at 7 GiB (measured).
  1. In `MaedaGalois5Defs` (light), state the six coefficient identities as
     a `Prop`-valued hypothesis bundle (e.g. `ThetaIdentities`).
  2. Prove `resolvent_eval_theta` and `galActionHom_bijective_of_quintic`
     from that bundle.
  3. Discharge the bundle in a 10-line heavy leaf module.
  4. Move `MaedaGalois5` and `MaedaGalois5Weights` into CI and
     `defaultTargets`.
- *Why*: §24–25, §33.  Every criterion or instance edit currently needs
  Modal plus a valid chain cache.  Six criterion rounds were needed in
  Part IV alone.
- *Effort*: M.  Rebuilding the light modules is cheap.  Defs changes, so the
  chain rebuilds once: about 2 h **(est.)**.  **Batch it with P2-1.**
- *Done when*: `lake build` in CI checks `galActionHom_bijective_of_quintic`
  and all six `maeda_galois*`, with the hypothesis bundle discharged only in
  the heavy leaf.
- *Owner decision*: **yes**, it needs a heavy chain rebuild.

**P1-3. Find out where the chain's memory goes before scaling up.**
- *What*: E4 (2,545 terms) peaked at 202 GiB but E6 (10,780 terms) at
  172 GiB (measured).  So peak memory does not follow certificate size; the
  `*_eval` / `theta_eK` elaboration (`simp` + `ring` over Horner text) is the
  likely driver **(hypothesis)**.
  - Bisect E4 with a stub-file probe: decide only / eval lemmas only /
    theta lemma only.
  - Record each part's peak RSS from `[telemetry]`.
- *Why*: §1, §7, §24.  Memory, not time, is the failure mode, and any
  dim ≥ 6 certificate inherits this cost structure.
- *Effort*: M; three or four medium Modal runs (≤ 200 GiB each, est.).
- *Done when*: a table in `research/` attributes ≥ 80 % of E4's peak to one
  declaration class, with a proposed fix (e.g. `PEval` lemmas proved by
  `rfl`/`decide` on the Horner chain instead of `simp`+`ring`).
- *Owner decision*: **yes**, it spends Modal credits.

**P1-4. Decide Iteration 19's mathematical route before building tooling.**
- *What*: §8 recommends generalizing `Poly5` to `Fin n → ℕ` monomials.  The
  research log, however, says Galois groups beyond `S₅` need the Frobenius
  cycle-type criterion (Dedekind's theorem, not in Mathlib), not resolvent
  identities.  Irreducibility for dims 6–10 needs Rabin certificates and a
  generic `charpoly_dimN` (`research/maeda-scaling-study.md`).
  - Proposed scope for Iteration 19: **irreducibility, dims 6–10**, using a
    generic `charpoly_dimN` plus Rabin.
  - Generalize `Poly5` only when a resolvent-style identity is actually
    needed.
- *Why*: avoids an M–L generalization (P1 cost, est.) that the next
  iteration may not use.
- *Effort*: S (decision plus a one-page plan, `research/iteration19-plan.md`).
- *Done when*: the plan names the route and lists which Iteration 18 tools
  it reuses.
- *Owner decision*: **yes**, the research scope.

**P1-5. One consolidated Mathlib API reference.**
- *What*: merge the four API tables (§5, §11, §17, §29) and the §26 errata
  into `research/mathlib-api-notes.md`, keyed by name, with a "verify by" grep
  line.  Point AGENTS.md at it.
- *Why*: API drift was the largest round-trip sink (§17: "every bullet cost
  a full Modal round trip"; §29).  Today the correct name is spread across
  four parts, some of them stale.
- *Effort*: S; no Modal.
- *Done when*: every entry was grepped in `.lake/packages/mathlib` at the
  pinned revision, and no stale claim from §26 remains.
- *Owner decision*: no.

**P1-6. Carry the kernel rules into AGENTS.md "Conventions and gotchas".**
- *What*: AGENTS.md already notes `pBeq` and the left operand under Poly5.
  Add three general rules:
  - the §27 triage table, in short form;
  - "every `decide` over a noncomputable structure uses the three-piece
    certificate (§28)";
  - "one heavy identity per module, chained; byte-identical regeneration
    (§33)".
- *Why*: AGENTS.md is the single source of truth (CLAUDE.md).  The review
  file is not loaded automatically.
- *Effort*: S.
- *Done when*: the three rules are in AGENTS.md, each linking to the review
  section.
- *Owner decision*: no.

### P2 — hygiene, docs and lint debt

**P2-1. Style-lint debt in the generated `Id*` modules and `MaedaGalois5Defs`.**
- *What*: fix in `tools/gen_poly5.py` (long lines, heartbeat comments) and in
  Defs.
- *Why*: §32, research-log "What remains".  Any Defs edit rebuilds the chain
  (about 2 h, 202 GiB peak, measured).
- *Effort*: S code, **heavy rebuild**.  Batch with P1-2 so one rebuild pays
  for both.
- *Done when*: the chain builds with zero warnings.
- *Owner decision*: **yes**, the rebuild.

**P2-2. Fix the stale Weights docstring.**
- *What*: the module docstring says `R` is "defined as `resolvent5`".  Since
  the redesign it is explicit, with `hRint`.  Fix in `tools/gen_galois5.py`
  and regenerate.
- *Why*: §34.5.
- *Effort*: S.  Weights is cheap today, and free in CI after P1-2.
- *Done when*: the docstring matches the code, and `regenerate` → `git diff`
  shows only the docstring.
- *Owner decision*: no.

**P2-3. Mark errata inline in the review.**
- *What*: append "(corrected in §26 / improvements doc)" to each stale bullet
  in Parts I–III (§2, §3, §4, §5, §17, §19, §20, §24, §25.4), so nobody
  follows them in isolation.
- *Why*: see the contradiction table above.
- *Effort*: S.
- *Done when*: every row of that table has an inline pointer.
- *Owner decision*: no.

**P2-4. Preserve the evidence.**
- *What*: build logs and scratch probes live only in `/tmp/ringlab`
  (including `scratch-archive/`) and `/tmp/maeda5`.  Copy the telemetry
  summaries (not the full logs) into `research/iteration18-buildlogs.md`.
- *Why*: §7 ("read the previous session's logs first").  `/tmp` is not
  durable.
- *Effort*: S.
- *Done when*: every measured number in §1, §27 and §33 can be traced to a
  committed file.
- *Owner decision*: no.

**P2-5. Branch hygiene.**
- *What*:
  - `origin/master` has Iteration 18 (`3362d60`).
  - Local `master` is one commit ahead (`9217d4e`, review Part I).
  - `review/iteration-18` contains Parts I–IV plus this document.
  - Fast-forward `master` to the review branch once the review is accepted.
- *Effort*: S.
- *Done when*: `master` contains the review files and the local and remote
  branches agree.
- *Owner decision*: **yes**, merging to master and pushing.

---

## 3. Recommended next three actions

1. **P0-1 + P0-2 together.**  Commit the Modal runner scripts, fix the
   AGENTS.md/CLAUDE.md commands, and snapshot the chain cache.  This is cheap,
   needs no build, and removes the two ways the next iteration could lose
   hours or credits.  It needs your call on the canonical account.
2. **P0-4.**  Run the axiom audit for the certificates off the cached chain.
   It is the one open item against the non-negotiable proof standard, and it
   costs one light run if the cache is intact.
3. **P1-4, then P1-1.**  Fix Iteration 19's scope (irreducibility for dims
   6–10 vs Galois), then build the generator lint and self-check before
   writing any new generator.  Schedule the single heavy rebuild (P1-2 +
   P2-1) only if the plan keeps the `S₅` files evolving.
