# AGENTS.md — MathProof

Autonomous research workspace for the **Langlands program / modular forms**: each
iteration of the research loop picks an open problem and contributes *formally
verified* mathematics in Lean 4 + Mathlib. The standard of proof is strict: no
`sorry`, no `native_decide`, no external CAS — computations must be verified by
Lean's kernel alone (`decide`).

## Build

Toolchain and Mathlib are pinned (`lean-toolchain`, `lakefile.toml`: Lean
`v4.36.0-rc1`, Mathlib `v4.36.0-rc1`).

### Primary: build on Modal

All builds and verification runs happen on Modal (modal.com) via the existing
scripts `lean_build.py` / `lean_check.py` — don't invent new plumbing.

**Modal account (since 2026-10-29): Linux user `xyz`.**  The doz workspace
(`/home/doz/dozenv/bin/modal` fails with `workspace … is
disabled`).  The canonical CLI is `/home/xyz/xyzenv/bin/modal`, reached via
passwordless `sudo -u xyz`; xyz cannot read `/home/doz`, so the working tree
is mirrored into `/home/xyz/math-proof1` first.  `tools/modal_run.sh` does
both — mirror + `modal run lean_check.py` as xyz — and passes every argument
through; use it instead of calling `modal` directly (bare `python3` cannot
import `modal` either).  `MODAL_USER` / `MODAL_BIN` / `MODAL_MIRROR` override
the account.  The heavy MaedaGalois5 chain has its own staged runner,
`tools/stage_chain.sh [first-stage]` (one `lean_check` per module, stops at
the first failure, resumable through the build cache; never run two heavy
stages concurrently).

- **Iterate with `lean_check.py`** (app `mathproof-check`): fresh-clones the
  GitHub repo, overlays every locally modified *or untracked* `.lean` file
  (or just `--file <path>` — which also *builds* that file's module unless
  `--target` says otherwise), symlinks the baked warm dependency tree into
  `.lake/packages`, and builds one target on the container's local disk.
  No push needed (~1 min round trip):

  ```bash
  tools/modal_run.sh --target MathProof.Tau.CongruenceSmall
  tools/modal_run.sh --file MathProof/Tau/SomeFile.lean
  ```

  **Telemetry**: both scripts print `[telemetry]` resource lines for the
  `lake` process tree — live peak-RSS milestones (≥10 % growth) and a final
  `wall / peak_tree_rss / CPU / children ru_maxrss` summary plus a decimated
  RSS curve. Std-lib only; no Modal resources involved. Two measured caveats:
  Modal `memory=` is a *soft* request (a "32 GiB" container was observed at
  60 GiB RSS), and multi-minute `decide +kernel`s need
  `set_option maxHeartbeats <large>` or the kernel dies with
  `(kernel) deterministic timeout` (default 200000 ≈ 200 s of kernel work).

  **Memory alerts — investigation policy (since 2026-10-29).**  Every build
  whose `lake` tree reaches **64 GiB** RSS must be investigated; "it fit in
  the container" is not an answer.  The tooling makes this mechanical:
  1. `lean_check.py` prints a `[memory]` table (peak RSS per module, from
     the `lean` process of each module) after every run, and at ≥ 64 GiB
     (`LEAN_CHECK_MEM_ALERT_GIB` overrides) `[memory-alert]` lines naming the
     hot modules plus the profiling command for each.
  2. `tools/modal_run.sh` keeps every run's log (`$TMPDIR/mathproof-runs/`)
     and appends each alert to `research/memory-alerts.md` as an **OPEN**
     entry.
  3. Investigate with `LEAN_CHECK_PROFILE=<Module> tools/modal_run.sh`: it
     builds (and caches) only the module's imports, then elaborates an
     instrumented copy of the module with plain `lean` (`Elab.async=false`):
     a `#eval` mark before every top-level command timestamps it, and the RSS
     samples between marks give each declaration's peak and growth
     (`[profile]` tables: top 15 by RSS growth, top 10 by duration; line
     numbers refer to the original source).  The instrumented
     copy lives in `/tmp`; the build tree and cache are untouched.  Cost: one
     elaboration of that module.
  4. Record the top declarations, the cause and the fix (or why the cost is
     inherent) in the entry and mark it **CLOSED**.  Recurring causes go into
     the "Conventions and gotchas" below.

- **Full / final build with `lean_build.py`** (app `math-proof1-build`):
  builds the pushed GitHub state (`picodozbotdoz/math-proof1`);
  `--target ''` runs the default (light) targets; heavy modules are built
  explicitly, e.g. `--target MathProof.Tau.LehmerPacked`.  It needs no
  working-tree mirror beyond the script itself, so run it as xyz from the
  mirror `tools/modal_run.sh` keeps up to date:

  ```bash
  sudo -n -u xyz bash -lc 'cd ~/math-proof1 && ~/xyzenv/bin/modal run lean_build.py --target MathProof.Tau.Lehmer'
  sudo -n -u xyz bash -lc "cd ~/math-proof1 && ~/xyzenv/bin/modal run lean_build.py --target ''"   # full `lake build`
  ```

  Caveat: it clones only when `/tmp/repo` is absent, so a reused container can
  build a stale clone. To verify freshly pushed code use `lean_check.py`
  (always fresh-clones) or expect a fresh container.

- **Debug interactively**: `modal shell lean_build.py::build` (same image +
  volumes as the build function) or `modal shell --volume lean-cache`
  (mounted at `/mnt/lean-cache`).

Existing shared Modal resources (see `lean_build.py`) — **reuse them, never
recreate them**:

- **Volume `lean-cache`** — mounted at `/cache`.  Never write individual
  `.olean`s to it (thousands of tiny writes to a network volume stall at
  ~40 MB / 11 min — measured).  `lean_check.py` keeps exactly one file there:
  `/cache/buildcache/latest.tar.gz`, a rolling tarball of the project's
  `.lake/build`, restored before and re-saved after every run (failed ones
  too), so unchanged MathProof modules are not rebuilt.  Lake's hash traces
  decide what is stale, so a restore is always safe.  Opt out with
  `LEAN_CHECK_NO_CACHE=1` (e.g. for clean timing measurements).
- **Image** — Debian slim + elan v4.2.4 + the pinned Lean toolchain + the
  warm dependency tree (mathlib + deps at the manifest's exact revisions, with
  the full Mathlib olean cache fetched at image-build time into `/opt/warmrepo`;
  keep each package's `.git` or lake re-fetches everything). Defined
  *identically* in both scripts so the layer cache is shared. If one must
  change, change both — and expect the image rebuild to pay for `lake update`
  + `lake exe cache get` once (~15 min).
- Per run: 4 CPUs, 32 GiB RAM, 4-hour timeout. Logs stream from `modal run`.

### Least preferred: building on this machine

Local `lake build` requires the ~7 GB Mathlib cache and `MathProof.Tau.Lehmer`
alone costs ~2 CPU-minutes of kernel time. Build locally **only** when Modal is
unavailable and a check is still needed — and then build single modules:

```bash
lake build MathProof.Tau.Lehmer     # build a single module
```

### Modal resource policy — hard rule

AI agents are **forbidden from proactively adding or registering additional
Modal resources**: no new apps, volumes, secrets, environments, or image
definitions, and no `modal deploy` — anything persistent requires an explicit
decision by the human user. Agents may only *run* the existing scripts
(`modal run lean_build.py` / `lean_check.py`, which are ephemeral runs) against
the resources listed above. If those seem insufficient for a task, stop and
surface the limitation to the user instead of creating workarounds on Modal.

**Exception (user-authorized 2026-10-30):** `lean_tauceti.py` (app `tauceti-check`,
own image: TauCeti-pinned toolchain + Mathlib cache + prebuilt TauCeti modules;
no volume/secret, ephemeral `modal run` only) for TauCeti port checks, run via
`tools/modal_tauceti.sh`.  Reuse it for TauCeti tasks; it grants nothing else.

## Layout

- `MathProof/Tau/Basic.lean` — `Ramanujan.tau`: algebraic definition of τ
  (coefficients of `Δ = q ∏ (1 − q^m)^24`), truncation stability, hand-rolled
  kernel-friendly `List ℤ` arithmetic (`pmul`, `psub`, `pow24`, …), verified
  values `tau_one` … `tau_twenty_one`.
- `MathProof/Tau/Lehmer.lean` — Lehmer's conjecture: `tau_ne_zero_of_le_128`
  (kernel-verified nonvanishing over `ℤ` for `n ≤ 128`).
- `MathProof/Tau/LehmerMod.lean` — same list arithmetic mod `P = 999999937`
  (`decide +kernel`), raising the verified bound to `n ≤ 512`
  (`tau_ne_zero_of_le_512`, `tau_prime_ne_zero_of_le_512`); the 512 kernel
  decide needs ~5 min and >6 GB heap, so build this module on Modal (a 1024
  attempt was measured at >71 GB heap — beyond the 32 GiB budget; the way
  past that wall is the packed route below, not more memory).
- `MathProof/Tau/LehmerPacked.lean` — **packed-bignum** mod-`P` arithmetic:
  each coefficient list packed into a single `Nat` in base `2^80` (balanced
  fuel-structural pack/unpack), one GMP `Nat.mul` per dense product, entries
  from Euler's pentagonal number theorem via a structural Newton isqrt.
  Kernel-verified bound `n ≤ 65536` (`tau_ne_zero_of_le_65536`,
  `tau_prime_ne_zero_of_le_65536`; also the 16384 versions); soundness
  `deltaPacked_eq` + `pentRes_eq` rides Mathlib's `Pentagonal.PowerSeries`.
  The kernel decides need ~18 GiB (16384) / ~63 GiB (65536) of heap: build on
  Modal only (like `LehmerMod`, not in the CI target list); for the 65536
  decide override the check container's memory, e.g.
  `LEAN_CHECK_MEMORY_MIB=98304 tools/modal_run.sh --file
  MathProof/Tau/LehmerPacked.lean`.
- `MathProof/Tau/CongruenceSmall.lean` — gap congruences mod 2 and 3:
  `τ n` even unless `n ≡ 1 [MOD 8]`, `3 ∣ τ n` unless `n ≡ 1 [MOD 3]`.
- `research/lehmer-mod-scaling-study.md` — measured analysis of why
  `LehmerMod.lean` cannot pass 512 (kernel retention + heartbeat cap) and the
  benchmarked packed-bignum route to 16384–65536 (Iteration 5 study).
- `Bench/` — the study's benchmark modules in a dedicated library
  (`Bench` in `lakefile.toml`), **not part of the proof library**: never
  imported by `MathProof.lean`, never built by default or CI.  See
  `Bench/README.md` (which modules pass, which fail *by design*, and costs).
  `tools/gen_packed_bench.py` generates the packed-benchmark data (verified
  against the kernel-checked τ values).
- `MathProof/Tau/Bridge.lean` — the analytic bridge: `(qExpansion 1 Δ).coeff n = τ n`
  for Mathlib's analytic discriminant `Δ`.
- `MathProof/ModularForms/Weight12.lean` — Ramanujan's weight-12 identity
  `691 • E₁₂ = 441 • E₄³ + 250 • E₆²` via the Sturm bound; exports
  `E12_qExpansion_coeff` and Bernoulli evaluations `B₄, B₆, B₁₂`.
- `MathProof/ModularForms/Congruence691.lean` — `tau_modEq_sigma`:
  `τ n ≡ σ₁₁ n [ZMOD 691]`.
- `MathProof/ModularForms/HeckeLevelOne.lean` — the Hecke operator `T_p` on
  level-one cusp forms from scratch (invariance via explicit coset
  factorization, q-expansion coefficient formula `(T_p f)_m = f_{pm} +
  p^{k-1} [p ∣ m] f_{m/p}`).
- `MathProof/Tau/Mordell.lean` — **Mordell's theorem** `tau_mul_coprime`
  (τ multiplicative on coprime arguments) via `heckeTP_discriminant_eq`
  (`T_p Δ = τ(p)·Δ`, the eigenform equation) and the prime-power recursion
  `tau_prime_pow_succ`.
- `MathProof/Tau/LehmerUnbounded.lean` — `tau_ne_zero_of_prime_pows`: τ ≠ 0
  on all of `n` from prime-power-block nonvanishing (Mordell lift).
- `MathProof/Tau/PowChain.lean` (light) + `MathProof/Tau/LehmerPow32.lean`
  (heavy, Modal): Mordell-recursion chains over `ZMod P` seeded by
  `LehmerPacked.tauResList` — `τ(p^a) ≠ 0` for `p ≤ 65536`, `p^a ≤ 2^32`
  (one decide walks all 65535 chains; 2089 s / 143.8 GiB measured).
- `MathProof/Tau/LehmerSieve691.lean` (light) — the mod-691 sieve
  (`691 ∤ σ₁₁ n → τ n ≠ 0`): every prime `p ≢ −1 [MOD 691]` of arbitrary
  size has `τ p ≠ 0`; root-of-unity classification `prime_pow_dvd_sigma_iff`.
- `MathProof/Tau/LehmerPrimePower.lean` (heavy, Modal) — iteration-8
  instantiation `tau_ne_zero_of_prime_pow_le_65536` +
  `tau_of_65519_mul_65521_ne_zero`.
- `MathProof/Tau/LehmerGrand.lean` (heavy, Modal) — `tau_ne_zero_grand`
  (chains ⊕ sieve fused; every `n < 2^32` whose large prime factors avoid
  `−1 [MOD 691]`), `tau_of_4294967295_ne_zero`.
- `MathProof/Tau/LehmerPrimeReduction.lean` (light) — Lehmer's lemma
  `tau_prime_pow_ne_zero` (`τ p ≠ 0 → τ (p^a) ≠ 0`, elementary: p-adic vs
  archimedean dominance of the recurrence), `lehmerConjecture_iff_primes`,
  any-exponent sieve and the parametric initial-segment lemma.
- `MathProof/Tau/LehmerPrimeGrand.lean` (heavy, Modal; needs only
  `LehmerPacked`) — `tau_ne_zero_of_lt_70481`,
  `tau_ne_zero_of_prime_factors_le_65536_or_mod` (supersedes the chain-based
  `LehmerGrand` at less than half the memory).
- `MathProof/ModularForms/EigenLevelOne.lean` (light) — weight-generic
  `IsNormalizedRankOne k f a`: Hecke eigenform, Mordell, Lehmer prime-power
  lemma and reduction to primes for any normalized generator of a rank-one
  `S_k`; `eq_smul`.  `BernoulliHigh.lean` — `B₁₃ … B₂₆` (recurrence chain).
- `MathProof/ModularForms/LehmerWeight{16,18,20,22,26}.lean` (light) — the
  eigenforms `Δ·E_{k−12}`: integer coefficients, congruence mod the reduced
  `B_k` numerator `num B_k / gcd(num B_k, 2k·den B_k)` (from `E_k − H ∈ S_k`,
  no Sturm bound), prime sieve, initial segment (`a16_ne_zero_of_lt_21701`,
  …).  Exact moduli 3617, 43867, 283·617, 131·593 (= num B₂₂ / 11) and 657931
  (= num B₂₆ / 13); the 20/22 moduli are composite (per-prime sieve + coprime
  cancel); weight 26 has five bad classes (explicit `X⁵ − 1` factorization in
  `ZMod 657931`).
- `MathProof/ModularForms/Maeda{Weight24,LevelOne,SmallWeights}.lean`
  (light) — Maeda's conjecture (irreducible charpoly of `T₂`) for all
  level-one weights with `dim S_k ∈ {2, 3}`.  `MaedaLevelOne`: `prodForm`
  (`Δ^(i+1) E₄^a E₆^b`, coefficients `seqP` evaluated by `decide +kernel`),
  `heckeTPₗ`, `charpoly_dim2/3`, `irreducible_of_noRoot`.
  `MaedaSmallWeights.lean` is generated by `tools/gen_maeda.py` (regenerate,
  don't hand-edit).
  `MaedaGalois.lean` — `galActionHom_bijective_of_cubic` (S₃ from a non-square
  discriminant) and the six cubic-weight Galois instances.
  `MaedaDim4.lean` — memoized list coefficients (`seqPL`, `seqP_getD`; use these
  for indices ≳ 6, plain `seqP` decides blow up), `charpoly_dim4`,
  `charpoly_fin_four`, quartic irreducibility certificate;
  `MaedaDim4Weights.lean` — generated, weights 48–62.
  `MaedaGalois4.lean` — `galActionHom_bijective_of_quartic` (S₄ from irreducible
  resolvent + non-square discriminant; `vieta4`, `disc4`, `resolvent`) and the
  six instances.
  `MaedaDim5.lean` — `charpoly_dim5` (five-row back-substitution),
  `charpoly_fin_five` (principal-minor formula, proved by two rounds of
  `det_succ_row_zero` + `ring`), `irreducible_quintic` /
  `irreducible_quintic_of_mod` (no root + no monic quadratic × cubic
  factorization ⇒ irreducible; the cubic's `r, s, t` are forced by `u, v`,
  leaving an `ℓ²`-pair scan);
  `MaedaDim5Weights.lean` — generated (`tools/gen_maeda.py`), weights 60–74
  (the six `dim S_k = 5` weights; irreducibility).
  Galois `S₅`: `Poly5.lean` (light) — sparse
  five-variable polynomials with structural merge arithmetic, `PEval`
  homomorphism lemmas and the tail-recursive certificate check `pBeq`
  (`List`'s `DecidableEq` blows the kernel stack past a few thousand terms;
  `pMul`'s kernel stack grows with its *left* operand — keep it small).
  `MaedaGalois5Defs` (light) — `S₅` subgroup structure, `disc5`, the `F₂₀`
  sextic `resolvent5`, `theta`;  heavy (Modal only, not in CI; 8–35 GiB per
  module, ≈ 33 min for the chain — `tools/stage_chain.sh`):
  `MaedaGalois5IdBase → IdE4 → IdE5 → IdE6 → MaedaGalois5Identities` — the
  resolvent-coefficient and discriminant identities as `Poly5` kernel
  certificates, generated by `tools/gen_poly5.py` (one module per heavy
  identity, chained so lake builds them one at a time).  Kernel `decide`
  memory is ≈ 27 GiB per million `Poly5` list operations *within one
  declaration* (`research/poly5-memory-study/`), so the generator computes
  e_k(Θ) by the recurrence `E_{j,k} = E_{j−1,k} + Θ_j·E_{j−1,k−1}`, certifies
  every recurrence node as a literal with its own `decide` (`E·_·_ck`), and
  checkpoints the Horner side into literals at ≈ 0.5 M modelled operations;
  `MaedaGalois5` — `galActionHom_bijective_of_quintic`;
  `MaedaGalois5Weights` — the six instances (generated, `tools/gen_galois5.py`);
  `MaedaGalois5AxCheck` (heavy) — `#print axioms` for every certificate.
- `MathProof/ModularForms/HornerCert.lean` (light) — `propext`-free residue
  certificates: `hornerZ` (structural Horner over `ℤ`), `no_root_of_cert`,
  `ne_sq_of_cert`.  State "no root / non-square mod ℓ" as
  `∀ y : ℕ, y < ℓ → hornerZ cs y % ℓ ≠ 0` (no axioms), never as
  `∀ x : ZMod ℓ, …` (`decide` then depends on `Classical.choice` and
  `Quot.sound`).
- `MathProof/ModularForms/MaedaCertC.lean` (light) — `seqPLc`, the Maeda
  coefficient lists without `Finset`/`ArithmeticFunction`/`Ramanujan.tau`
  (`sigmaL`, `convLc`, `dCc`), and `seqPLc_eq` back to `seqPL`; the `L{j}c`
  certificates of `MaedaDim{4,5}Weights` are about it.
- `MathProof/AxCheckDecide.lean` (opt-in audit, imports the light root) —
  `#audit_decide_certs`: finds every `decide` certificate in the light library
  and reports those depending on more than `propext`; `#axiom_path ax n`
  prints the chain of constants that pulls axiom `ax` into `n`.
- `MathProof.lean` — root import file for the *light* modules. The heavy
  kernel-decide modules (`LehmerMod`, `LehmerPacked`) and `AxCheck` are
  deliberately **not** imported there — the root must stay cheap for
  downstream consumers. Add every new light module here; heavy ones stay
  standalone.
- `research/research-log.md` — the research loop log. Each iteration is recorded
  here (problem, contributions, next steps); update it (and `README.md`)
  when completing an iteration.
- `docs/` — the GitHub Pages source folder (`/docs`, deploy-from-branch),
  serving `https://picodozbotdoz.github.io/math-proof1/`: `docs/index.html`
  is the project landing page (results, verified τ values — keep in sync
  with `tau_one` … `tau_twenty_one` in `Basic.lean`), and `docs/langlands.html`
  is the standalone interactive educational page (GL₂ Langlands by example),
  self-contained by design: no network requests, no CDN. Preview with
  `python3 -m http.server` from that directory.

## Conventions and gotchas

- Everything τ-related lives in `namespace Ramanujan`; files `open Polynomial`.
- **Kernel-reducibility is the central engineering constraint.** The hand-rolled
  list arithmetic must be defined structurally: a naive definition can silently
  compile to well-founded recursion (`Acc.rec`), which the kernel cannot reduce,
  breaking every `decide`. Keep list functions structurally recursive; verify
  `decide` still works after touching them.
- **Editing an import ancestor of `MaedaGalois5Defs` rebuilds the heavy
  chain** (≈ 33 min, up to 35 GiB): lake's traces are input-based, so a change
  to `Tau/Basic`, `Lehmer`, `Bridge`, `Weight12`, `Congruence691`,
  `HeckeLevelOne`, `Mordell`, `LehmerWeight16`, `EigenLevelOne`,
  `MaedaLevelOne`, `MaedaDim4`, `MaedaDim5`, `MaedaSmallWeights`,
  `MaedaGalois` (or their imports) invalidates `IdBase … Identities` even when
  the `.olean`s come out identical.  Put new infrastructure in a new module
  (as `HornerCert`, `MaedaCertC`), and batch unavoidable ancestor edits with
  an approved chain rebuild.
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
- `defaultTargets` in `lakefile.toml` lists the light modules only: a bare
  `lake build` (CI, Reservoir's automated builder, downstream consumers of
  the package) must never pull the heavy kernel decides. When adding a
  module: light → add it to `defaultTargets`, `MathProof.lean`, and the CI
  list; heavy → add it to none of those, and build it explicitly on Modal.
