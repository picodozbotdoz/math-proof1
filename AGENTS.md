# AGENTS.md — MathProof

Autonomous research workspace for the **Langlands program / modular forms**: each
iteration of the research loop picks an open problem and contributes *formally
verified* mathematics in Lean 4 + Mathlib. The standard of proof is strict: no
`sorry`, no `native_decide`, no external CAS — computations must be verified by
Lean's kernel alone (`decide`).

## git
master branch is managed by human user. Any changes to master branch are to be
done by user unless the user specifically ask/instruct/allowed agent to do it.
git push is never to be done by ai agent, even when the user ask the agent to do.

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
  whose `lake` tree reaches **16 GiB** RSS must be investigated (lowered from
  64 on 2026-10-31 when requests were right-sized — anything above 16 GiB of
  *actual* use now deserves a look even when it fits); "it fit in
  the container" is not an answer.  The tooling makes this mechanical:
  1. `lean_check.py` prints a `[memory]` table (peak RSS per module, from
     the `lean` process of each module) after every run, and at ≥ 16 GiB
     (`LEAN_CHECK_MEM_ALERT_GIB` overrides) `[memory-alert]` lines naming the
     hot modules plus the profiling command for each.
  2. `tools/modal_run.sh` keeps every run's log
     (`/home/doz/tmp/math-proof1-temp/mathproof-runs/` — persistent across
     reboots, unlike `/tmp`; override with `MODAL_RUN_LOG_DIR`)
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
- Per run: 4 CPUs, 8 GiB RAM **requested** by default, 4-hour timeout.  The
  request is soft (Modal may grant more) but right-sized
  (`research/iteration21/MEMORY-RIGHTSIZING.md`): `tools/modal_run.sh`
  auto-escalates 8 → 16 → 32 GiB when a run OOMs (`lean_check.py` detects
  peak ≥ 97 % of the request and exits 42); heavier targets pass an explicit
  `LEAN_CHECK_MEMORY_MIB` (or `LEAN_BUILD_MEMORY_MIB` for `lean_build.py`),
  e.g. 98304 for the `LehmerPacked`-class decides.  Logs stream from `modal run`.

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
  The finite scans are `decide +kernel`; the Mersenne prime `2³¹ − 1` is
  certified by Mathlib's Lucas–Lehmer test, not trial division.
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
- `MathProof/Tau/LehmerCoverageCount.lean` (light) — kernel-verified Lehmer
  coverage anchors: structural trial-division certificate `noFactorFrom`
  (`Nat.Prime` is NOT kernel-decidable — minFac is well-founded; never
  `decide` a `Nat.Prime` filter), bad-prime census `badPrimes2p18_filter`
  (285 candidates → 17 primes) / `badPrimes2p20_filter` (1423 → 98),
  no-overlap count `card_uncoveredSet` (structural), `uncovered_2p18` = 23 /
  `covered_count_2p18` = 262120, 2^20 twins = 227 / 1048348.  Exact study:
  `research/iteration22/lehmer-coverage/` (STUDY.md, script, npy;
  99.9093 % of indices below 2^32 covered; 131072 descoped —
  DECISION-131072.md).
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
  sextic `resolvent5` (its coefficient blocks are split into the private
  defs `r5c5 … r5c0p*` so each elaborates under the default heartbeat
  budget), `theta`;  heavy (Modal only, not in CI; 8–35 GiB per
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
- `MathProof/ModularForms/CharpolyDimN.lean` (light) — the dimension-generic
  echelon extraction `charpoly_dimN` (ℕ-indexed basis hypotheses; the
  back-substitution matrix of any endomorphism from q-coefficient tables).
- `MathProof/ModularForms/FrobeniusCycleType.lean` (light) — Dedekind's theorem in
  cycle-type form, `frob_cycleType_of_factorization`: `IsArithFrobAt` on the root
  order `ℤ[x₁…xₙ]` + the finite-field orbit lemma `cycleType_of_frobenius_roots`.
  `JordanPrimitive.lean` (light) — transitive + `(n−1)`-cycle ⟹ primitive; with a
  swap, `Sₙ`.  `MaedaGaloisFull.lean` (light) — `bijective_of_frobenius`,
  `cycleType_of_cert`, Bézout Rabin test `irreducible_of_rabin_bezout`.
  `MaedaGaloisDim{6..10}Weights.lean` (light, generated — `tools/gen_galoisfull.py`
  from `research/iteration21/data/galoisfull_certs.json`, `--check` for
  byte-identical regeneration) — `MaedaWeightK.maeda_galois_full` for the 30 weights
  `72 ≤ k ≤ 134`; Modal 70–80 s / ≤ 7.5 GiB per file on a warm cache.
  `MaedaGaloisFullAxCheck.lean` — opt-in `#print axioms` audit, not in the root.
  `MaedaT3GaloisDim{6..10}Weights.lean` (light, generated —
  `tools/galoisfull_certs.py --prime 3` +
  `tools/gen_galoisfull.py --prime 3` from
  `research/iteration22-t3-galois/data/t3_galoisfull_certs.json`, charpolys
  pinned to the kernel-verified `P` literals of the T₃ dim files; `--check`
  byte-identical, T₂ mode untouched) — the T₃ twin
  `MaedaT3WeightK.maeda_galois_full` (Gal = Sₙ for the T₃ charpolys, same 30
  weights; Bézout witnesses throughout, transposition ℓ up to ≈ 8.7·10⁶);
  Modal 25–83 s / ≤ 6.3 GiB per file.  `MaedaT3GaloisFullAxCheck.lean` — the
  twin opt-in audit (all 30 on the standard three axioms).
  `MaedaGaloisQuad.lean` (light, Mathlib-only infra, trio-registered) —
  `bijective_of_quadratic`: a monic integer quadratic irreducible over ℚ has
  `Gal = S₂` (pretransitive action on the two complex roots; the image of
  `galActionHom` has 2 ≤ card ≤ 2!, so it is ⊤).
  `MaedaT3GaloisSmallWeights.lean` (light, generated —
  `tools/galoisfull_certs.py --small` +
  `tools/gen_galoisfull.py --prime 3 --small` from
  `research/iteration22/data/t3_galoisfull_small_certs.json`, charpolys
  pinned to the kernel-verified `P` literals of `MaedaT3SmallWeights.lean`;
  `--check` byte-identical, T₂/prime-3-dim modes untouched) — Gal = Sₙ for
  the T₃ charpolys of the 24 weights `k ≤ 74` with `2 ≤ dim S_k ≤ 5`
  (dims 3–5: the same two Frobenius certificates, all ℓ ≤ 89; dim 2: the
  certificate-free `MaedaGaloisQuad.bijective_of_quadratic`; the n = 3
  `{3−1}`/`{2}` defeq holds, no wrapper needed).  Completes T₃ Maeda in full
  (all 54 weights `2 ≤ dim S_k ≤ 10`).  Root-ONLY registration (imports the
  non-CI `MaedaT3SmallWeights` — see the lakefile note).  Modal: 34 s /
  5.38 GiB (galois file), 83 s / 4.76 GiB (the opt-in
  `MaedaT3GaloisSmallAxCheck.lean`, all 24 on the standard three axioms).
- `MathProof/ModularForms/MaedaDim{6,7,8,9,10}Weights.lean` (light,
  generated — `tools/gen_maedan.py`, never hand-edit; `--check` verifies
  byte-identical regeneration) — Maeda irreducibility for the 30 weights
  `72 ≤ k ≤ 134` with `6 ≤ dim S_k ≤ 10`: literal T₂-matrix per weight,
  charpoly via `CharpolyEngine` determinant interpolation, Rabin
  irreducibility certificates (`RabinCert.irreducible_of_rabin_int`).
  Coefficients past 80 digits are emitted as chunked `c0 * 10 ^ e0 + c1 …`
  literals; a chunked `det_t` needs `norm_num` after `eval_det` (the tactic
  leaves `flat = chunked`); the back-substitution is STAGED (`Lv{a}_{j}`
  list lemmas, one-step `change` unfolds + `rw` — a full-cascade
  `simp only [coordsAux]` exhausts the default heartbeats at dim ≥ 9, and
  `show` is rejected by `linter.style.show`, use `change`).  Build cost on
  Modal (staged, measured 2026-10-31): dim 6 = 88 s / 6.4 GiB, dim 7 = 138 s
  / 7.1 GiB, dim 8 = 333 s / 8.1 GiB, dim 9 = 413 s / 9.3 GiB, dim 10 =
  1167 s / 11.6 GiB (the k=120 Rabin decide, ~28k ZMod-muls, fits the
  200 s kernel budget per declaration).  Cold full pass of the five files
  ≈ 36 min — CI pays this on every push now.
- `MathProof/ModularForms/HeckeCommute.lean` (light) — level-one Hecke
  commutativity: `heckeTP2_qExpansion_coeff` (composed coefficient formula),
  `heckeTP_qExpansion_coeff_commute` (all prime pairs incl. `p = q`),
  `heckeTP_commute`, `heckeTPₗ_commute` (the `Commute` hypothesis consumed by
  the upgrade); q-expansion injectivity for cusp forms (`qExpansion_coeff_ext`).
- `MathProof/ModularForms/HeckeGeneratedByT2.lean` (light) — the upgrade
  algebra: `exists_aeval_of_commute_of_minpoly_eq_charpoly` (cyclic-operator
  form; cyclic vector from `Module.exists_ker_toSpanSingleton_eq_annihilator`
  on `Module.AEval' T₂`),
  `minpoly_eq_charpoly_of_map_of_irreducible` (separability + eigenvalues over
  ℂ), weight-generic wrapper `heckeTP_mem_spanT2`.
  `HeckeGeneratedByT2{Small,}Weights.lean` (light, generated by
  `tools/gen_hecke_gen_t2.py` — regenerate, don't hand-edit) — the 54
  per-weight theorems `heckeTP_mem_spanT2_weightKK`: for every prime `p`,
  `∃ Q : ℂ[X], T_p = aeval T₂ Q` on `S_k` (Hecke algebra generated by `T₂`,
  every even weight 24–134).  One namespace, two files split at the CI
  full-only boundary: `…SmallWeights` (dims 2–5, push tier) and `…Weights`
  (dims 6–10, imports the small file; full-only) — import the small one
  when only dims ≤ 5 are needed.  Modal: ≈ 32–50 s / ≤ 6.3 GiB per module.
- `MathProof/ModularForms/HeckeTPCoeff.lean` (light) — `heckeTP_coeff`, the
  p-generic twin of `heckeT2_coeff` (one `rw` from
  `heckeTP_qExpansion_coeff`); new light module because `MaedaLevelOne` is
  an ancestor of the heavy `MaedaGalois5` chain.
- `MathProof/ModularForms/HeckeRational.lean` (light) — the rational-witness
  machinery: `linearIndependent_dimN` + `represents_dimN` (the representation
  sibling of `charpoly_dimN`) and `exists_aeval_rat_dimN` (echelon bundle +
  integer certificate `∑_{j<n} N_j • M₂^j = D • M₃` ⇒ `∃ Q : ℚ[X],
  T₃ = aeval T₂ (Q.map (algebraMap ℚ ℂ))`; witness built internally, no
  commutativity input).
  `HeckeRationalWeights.lean` (light, generated — `tools/gen_hecke_rat.py`,
  `--check` byte-identity; regenerate, don't hand-edit) — the 30 dims-6–10
  instances `heckeT3_eq_aeval_rat_weightKK` (reuses the T₂ dim files'
  Xtab/hX/M/entry via the audited fb/Atab defeq bridge; per weight only the
  certificate + entry bridges are emitted; certificate literals >341 digits
  go out in Horner form base `10 ^ 74`).  Modal 234 s / 8.4 GiB.
  `HeckeRationalSmallWeights.lean` (light, generated) — the 24 dims-2–5
  twins: T₂ data re-derived fresh (Xtab2/hX2 via `heckeT2_coeff` + the T₃
  file's q-lemmas, LvT2/entryT2/M2) — root-only registration (follows its
  parent `MaedaT3SmallWeights`), NOT a defaultTargets/CI item.  Modal 67 s /
  7 GiB.  The scaled identities are `decide +kernel` ENTRYWISE
  (`ext`+`fin_cases`): a matrix-level `decide` inherits
  `Fintype.decidablePiFintype`'s simp-built Iff proof (Classical) and fails
  the AxCheckDecide audit.
- `MathProof/ModularForms/HeckeCyclic.lean` (light, trio) — iteration-24 b2
  generic cyclicity: `t2Span T2 n = span ℤ {T₂^j : j<n}` (the b1
  `HeckeLatticeIndex.t2Lattice` contract form, rfl-identical so adoption is
  free), `heckeLattice_le_sup_t3`/`quotient_generated` (the quotient
  `𝕋 ⧸ ℤ[T₂]` is generated by `[T₃]` at `n ≤ 4`: `T₁ = 1`,
  `T₄ = T₂² − 2^{k−1}T₁` from `heckeTM_two_mul_even`),
  `card_dvd_of_generator` (ZMod.lift + Lagrange: generator killed by `D`
  ⟹ `Nat.card ∣ D`), `order_minimal` (Bézout cross-multiplication, the
  `den_dvd_index` pattern), `D_eq_Ik_of_cyclic` (cyclicity + `D ∣ I_k`
  landed + positivity ⟹ `D = I_k`), the iff `heckeLattice_eq_t2Span_iff`
  and the unconditional dim-2 equality `heckeLattice_eq_t2Span_two`.
  33 s / 5.9 GiB; root-only twin `HeckeCyclicWeights` (G3) instantiates.
- `MathProof/ModularForms/HeckeCyclicWeights.lean` (light, generated —
  `tools/gen_hecke_cyclic.py`, `--check` byte-identity; regenerate, don't
  hand-edit; root-only registration — imports the non-CI
  `HeckeIndexSmallWeights`/`HeckeIndexCardSmallWeights`/
  `HeckeRationalSmallWeights`/`MaedaT3SmallWeights`) — the 18 dims-2-4
  instances of `HeckeCyclic`, all unconditional: at dims 3-4 `index_card`
  (`Nat.card (𝕋 ⧸ ℤ[T₂]) = |I_k|`, index-card's
  `HeckeIndexCardWeightKK.index_card_natCard` moved along `heckeTM_prime`;
  `t2Lattice` is `t2Span` by definition), `D_eq_Ik` (`D = I_k`) and
  `heckeLattice_ne_t2Span` (`𝕋 ≠ ℤ[T₂]`); at the six dim-2 weights the
  lattice equality `heckeLattice_eq_t2Span` (`𝕋 = ℤ[T₂]`, no index
  input).  45 s / 6.2 GiB on Modal (warm).
- `MathProof/ModularForms/HeckeTM.lean` (light, trio) — `T_m` for every
  `m` (recursive route over `minFac`), coefficient formula
  `heckeTM_qExpansion_coeff`, `heckeTM_one`, `heckeTM_prime`, commutation,
  full `heckeTM_mul`.  `HeckeIndex.lean` (light, trio) — Miller basis,
  integer Cramer certificates, `den_dvd_index`, and the Hecke-ring quarter:
  `miller_expand`, `hecke_dual` (pointwise), `hecke_independent`,
  `heckeLattice`/`heckeRing`.  `HeckeIndexSmallWeights` (dims 2–5) /
  `HeckeIndexWeights` (dims 6–10) (light, generated —
  `tools/gen_hecke_index.py`, `--check` covers both; root-only): index
  `I_k = |det A|` (`eval_det`), entrywise certificates, `D ∣ I_k`; split by
  dim so each builds under the default 8 GiB request (69 s / 5.14 GiB and
  336 s / 6.56 GiB).  `HeckeFieldDim2.lean` (light, trio) — dim-2
  integrality for every `m`.  `HeckeFieldRat.lean` (light, trio) — every
  `T_m ∈ ℚ[T₂]` from echelon data (`miller_int`, `heckeTM_eq_aeval_rat`).
  `HeckeFieldWeights.lean` (light, generated — `tools/gen_hecke_field.py`;
  root-only) — T-Rat + T-Field for every `m` at all 54 weights.
  `MaedaT2GaloisSmallWeights.lean` (light, trio) — `Gal = S₂` for the six
  dim-2 T₂ charpolys.
  `HeckeLatticeIndex.lean` (light, trio; iteration 24) — the lattice index
  as an honest `AddSubgroup.relIndex`: `t2Lattice T₂ n = span_ℤ {T₂^i}`,
  `relIndex_t2_eq_det` (`AddSubgroup.relIndex_eq_natAbs_det` with
  `Basis.span` bases; no `toIntSubmodule` friction once `Module ℤ` is the
  canonical `AddCommGroup.toIntModule` — never add a separate `[Module ℤ M]`
  binder), `natCard_quot_eq_det`, the ℤ Miller accumulator
  `millerTopC`/`millerCoeff`, and the dual route `T₂^i = ∑_j C i j • T_{j+1}`
  with `C i j = a_1(T₂^i g_j)` (`t2_pow_eq_smul_heckeTM`); per-weight entry
  points `index_card_dimN` / `index_card_natCard_dimN`.
  `HeckeIndexCard{Small,}Weights.lean` (light, generated —
  `tools/gen_hecke_index.py --card`, `--check` covers all four
  HeckeIndex/HeckeIndexCard files; root-only like their parents) —
  `HeckeIndexCardWeightKK.index_card` / `index_card_natCard`:
  `[𝕋 : ℤ[T₂]] = |I_k|` at all 54 weights (`C` literal; ONE `List`-sum
  Bool decide per weight `hcheck : cardCheck atab m2tab ctab n = true`,
  bridged to the matrix `hcard` by `hcard_of_check`; `det_C` by
  `eval_det`).  Nested-audit clean: the certificate mentions only integer
  pattern-match tables (no `Matrix` literal — `!![…]` pulls `Quot.sound`),
  `Int.decEq` (not `==`: `BEq ℤ` routes through
  `Int.instLinearOrderPackage` → `Classical.choice`) and pow-free chunked
  numerals (no `Monoid.npow`).  Modal 11 s / 5.1 GiB (dims 2–5) and
  47 s / 7.4 GiB (dims 6–10).
  `HeckeRingGens.lean` (light, trio; iteration 24) — ring generators of 𝕋:
  `gensOf k ps`, `heckeTM_mem_closure_of_smooth` (every `ps`-smooth `T_m`
  lies in `Subring.closure`), transport `heckeRing_eq_closure`, the
  certificate-free `heckeRing_eq_closure_gens{2357,235,23,2}` (n ≤ 10/6/4/2),
  `heckeRing_eq_closure_gens235_of_t7`, row certificate
  `heckeTM_mem_closure_of_rows` (`T_{m₀} = ∑ cₜ T_{Mₜ}` checked on first
  q-coefficients via `op_eq_of_first_coeff`).  ℤ[T_p : p ∈ ps] =
  span_ℤ{smooth T_m}, so no Cayley–Hamilton / index machinery is needed.
  `HeckeRingGens{Small,}Weights.lean` (light, generated —
  `tools/gen_hecke_ring_gens.py`, `--check`; root-only) — all 54 weights:
  `heckeRing_eq_gens2357` everywhere, `heckeRing_eq_gens235` at the 22
  {3,5}-weights (dims 5–6 free; dims 7–9: ten `T₇` Bezout certificates over
  smooth m ≤ 3n, ≤ 66 digits), `…gens23` (n ≤ 4), `…gens2` (n = 2).
  Modal 46 s / 4.8 GiB and 86 s / 5.2 GiB.
- `MathProof/ModularForms/MaedaCertCExt.lean` (light) — `tau22 … tau30`
  (kernel-verified against `Ramanujan.tau`), `tauTableX`, `dCc3`,
  `seqPLc3`, `seqPLc3_eq` with cap `N ≤ 31`: the T₃ coefficient formula
  reads basis coefficients up to index `3n` (30 at dim 10), past
  `MaedaCertC.seqPLc`'s `N ≤ 22`.
- `MathProof/ModularForms/MaedaT3Dim{6,7,8,9,10}Weights.lean` (light,
  generated — `tools/gen_maedan.py --prime 3`, never hand-edit) — the T₃
  twin of the dim-6…10 run: `Irreducible (charpoly (T₃ | S_k))` for the
  same 30 weights `72 ≤ k ≤ 134` (`MaedaT3WeightK.charpoly_T3`,
  `MaedaT3WeightK.maeda`), same staged back-substitution + Rabin
  certificates.  T₃ numerics outgrow T₂'s (charpoly coefficients to 317
  digits, matrix entries to 82), which forced two generator-side changes:
  chunked literals cap every place-value exponent at 256 (Lean's default
  `exponentiation.threshold` — norm_num refuses `10 ^ 257` and light
  modules may not raise the option; the first chunk grows for d > 316),
  and oversized `((… : ℤ) : ℂ)` cast items chunk across lines
  (`cast_item_lines` budgets; the longLine linter silently stops reporting
  once the file has any error, so failed builds under-report style
  warnings).  Build cost on Modal (measured 2026-10-31): dim 6 = 165 s /
  10.57 GiB, dim 7 = 209 s / 8.49 GiB, dim 8 = 527 s / 9.53 GiB, dim 10 =
  1227 s / 12.38 GiB (dim 9 green; its run finished just before the host
  reboot and the telemetry was lost with /tmp).
- `MathProof/ModularForms/MaedaT3SmallWeights.lean` (light, generated —
  `tools/gen_maedan.py --prime 3 --small`) — the T₃ stretch: the 24
  weights `k ≤ 74` with `2 ≤ dim S_k ≤ 5` through the same
  dimension-generic engine (`charpoly_dimN`).  Registered in the root
  `MathProof.lean` only (so `AxCheckDecide` audits its certificates);
  deliberately NOT a `defaultTargets`/CI item — the T₃ dim files already
  add ≈ 35–50 min per push and this bonus file would add more (see the
  lakefile note).
- `MathProof/ModularForms/HornerCert.lean` (light) — `propext`-free residue
  certificates: `hornerZ` (structural Horner over `ℤ`), `no_root_of_cert`,
  `ne_sq_of_cert`.  State "no root / non-square mod ℓ" as
  `∀ y : ℕ, y < ℓ → hornerZ cs y % ℓ ≠ 0` (no axioms), never as
  `∀ x : ZMod ℓ, …` (`decide` then depends on `Classical.choice` and
  `Quot.sound`).
- `MathProof/ModularForms/IntCastCert.lean` (light) —
  `intCast_eq_of_emod`: `n % ℓ = r` over `ℤ` (decided, `propext`-only) ⇒
  `((n : ℤ) : ZMod ℓ) = ((r : ℤ) : ZMod ℓ)`.  The `hmap` cast rewrites of
  `gen_maedan.py`'s files (all modes) go through it; never decide a `ZMod`
  cast equation directly (`Classical.choice` + `Quot.sound`).
- `MathProof/ModularForms/MaedaCertC.lean` (light) — `seqPLc`, the Maeda
  coefficient lists without `Finset`/`ArithmeticFunction`/`Ramanujan.tau`
  (`sigmaL`, `convLc`, `dCc`), and `seqPLc_eq` back to `seqPL`; the `L{j}c`
  certificates of `MaedaDim{4,5}Weights` and `gen_maedan.py`'s dim-6…10
  files are about it.
- `MathProof/AxCheckDecide.lean` (opt-in audit, imports the light root) —
  `#audit_decide_certs`: finds every `decide` certificate in the light library
  and reports those depending on more than `propext`;
  `#audit_decide_certs_nested` (iteration 24) does the same for the internal
  auxiliary lemmas of `decide +kernel` calls *inside* tactic proofs
  (entrywise `ext; fin_cases <;> decide +kernel`, `show … by decide +kernel`); `#axiom_path ax n`
  prints the chain of constants that pulls axiom `ax` into `n`.
- `MathProof.lean` — root import file for the *light* modules. The heavy
  kernel-decide modules (`LehmerMod`, `LehmerPacked`) and `AxCheck` are
  deliberately **not** imported there — the root must stay cheap for
  downstream consumers. Add every new light module here; heavy ones stay
  standalone.
- `research/research-log.md` — the research loop log. Each iteration is recorded
  here (problem, contributions, next steps); update it (and `README.md`)
  when completing an iteration.
- `tools/wave_watchdog.sh` — wave-worker liveness report, the artifact side
  of the stuck-worker protocol (`external-doc/RESEARCH-WORKFLOW.md` §6):
  per worktree under `worktree/mp1/` — branch/tip age, dirty count, WORKLOG
  heartbeat age + last dated entry, newest artifact mtime, newest mirror
  run-log age, live modal-client count (matched by that worktree's own
  `mrun.sh` mirror path, never a sibling's).  Explicit slugs = the wave's
  active set (all signals stale ⇒ STALLED, exit 3); no args = cold survey
  (stale ⇒ IDLE, exit 0).  `WAVE_WATCHDOG_STALL_MIN` overrides the 60 min
  default; `WAVE_WT_ROOT` the worktree root.
- `docs/` — the GitHub Pages source folder (`/docs`, deploy-from-branch),
  serving `https://picodozbotdoz.github.io/math-proof1/`: `docs/index.html`
  is the project landing page (results, verified τ values — keep in sync
  with `tau_one` … `tau_twenty_one` in `Basic.lean`), and `docs/langlands.html`
  is the standalone interactive educational page (GL₂ Langlands by example),
  self-contained by design: no network requests, no CDN. Preview with
  `python3 -m http.server` from that directory.
  `docs/articles/` holds the standalone discovery articles (`index.html`,
  shared `article.css`/`article.js`, same-origin only, no CDN): each separates
  what Lean proves from what is computed or classical, so update the relevant
  article when a result it cites changes.

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
- `RabinCert.zpgcd` inverts by a Fermat power structural in `ℓ` (`zspow`): the kernel
  recursion depth grows with `ℓ` and overflows near `ℓ ≈ 5·10⁶`.  For large primes use
  Bézout witnesses (`MaedaGaloisFull.irreducible_of_rabin_bezout`), never `maxRecDepth`.
- Lakefile options: `relaxedAutoImplicit = false`, `linter.mathlibStandardSet = true`,
  Mathlib-style copyright headers disabled. No `autoImplicit` tricks.
- `decide` / `norm_num [bernoulli]` time out on Mathlib's well-founded Bernoulli
  definition — `Weight12.lean` chains the defining recurrence instead; reuse it.
- Mod-P computations (`LehmerMod.lean`) keep every intermediate below `2^60` by
  reducing `% P` after each operation; soundness is proved by transporting into
  `ZMod P` (mirror `L2P` as `L2PMod`). A nonzero residue mod a prime certifies
  the integer coefficient is nonzero — no magnitude bound needed.
- CI (`.github/workflows/lean_action_ci.yml`) runs `lean-action` on pushes
  to **master only** (since 2026-11-01); keep `lake build` clean before
  merging to master.  Branches are verified on Modal instead
  (`lean_check.py` overlays the working tree, no push needed).
  **Selective targets (since 2026-11-03, iteration23-review §8)**:
  `tools/ci_targets.py` derives the targets from `defaultTargets` (single
  source — no CI copy to sync).  A master push builds the *push* tier:
  every default target except the expensive per-weight certificate roots
  in `.github/ci-full-only.txt` (the T₂/T₃ dim-6–10 Maeda files) and
  everything importing them (computed from the import graph — 22 of 76
  today).  Split generated all-weights files at that boundary (as
  `HeckeGeneratedByT2{Small,}Weights`) so small-dim consumers stay on the
  push path.  The weekly schedule and `workflow_dispatch` (default) build the
  *full* tier.  Pushes touching no Lean build input (docs, research,
  tools) skip CI, and runs queue (`concurrency`, no cancel) so a newer push
  restores the finished build's `.lake` cache instead of a stale one.
  Before CI's first push of a new module, check `tools/ci_targets.py
  --report` (exit 1 on a full-only root outside `defaultTargets` or a
  default target unreachable from `MathProof.lean`).  A new expensive
  generated family (cold cost of several minutes) goes into
  `ci-full-only.txt` with the reason in its layout entry.
- `defaultTargets` in `lakefile.toml` lists the light modules only: a bare
  `lake build` (CI, Reservoir's automated builder, downstream consumers of
  the package) must never pull the heavy kernel decides. When adding a
  module: light → add it to `defaultTargets` and `MathProof.lean` (CI
  follows `defaultTargets`); heavy → add it to neither, and build it
  explicitly on Modal.  ("Trio" in older notes = these two + the former CI
  list.)
- **Coding rules** (`external-doc/CODING_STANDARDS.md`) apply to
  every light module since iteration 18b: no `set_option` at all (no
  heartbeat/recdepth raises, no linter suppressions), no `#eval`/`meta`/
  `unsafe`, no `native_decide`/`sorry`, Mathlib-level imports only.  Check
  with `tools/tauceti_audit.sh` (comment-aware).  If a light `decide` trips
  the default elaborator budget, first try `decide +kernel` (the elaborator's
  re-evaluation is usually the hog) or `norm_num`; if an elaboration genuinely
  needs more, split the declaration (cf. the `r5c*` coefficient defs in
  `MaedaGalois5Defs`) instead of raising `maxHeartbeats`.  Only Tier C heavy
  modules keep `set_option`, each with a measured reason
  (`research/refactor-i18-tauceti/README.md`).
- **A red build under-reports style warnings** (2026-10-31, maeda-t3 dim-10):
  Mathlib's linter pipeline skips every remaining command in a file after the
  first *error*, so a failed build shows only a prefix of the real style
  violations (observed: 24 longLine violations, 9 reported).  Never claim
  "zero warnings" from a failed build — get the errors fixed and the build
  green first (this is also why the Modal check treats warnings as blockers).
- **Lean's default `exponentiation.threshold = 256`** (2026-10-31): `norm_num`
  refuses numerals like `10 ^ 257` in light modules (where raising the option
  is forbidden).  Big chunked literals must keep chunk exponents ≤ 256 — grow
  the *first* chunk (≤ 341 digits total observed fine) instead of emitting
  more chunks with bigger exponents.
- **Surveying TauCeti** (2026-11-02): the clone at `~/zcode-workdir/tauceti` is
  shallow and its `main` is old, so run `git fetch` and `git grep <regex>
  origin/main -- TauCeti` without checking out, and search by concept
  (`cycleType`, `factorDegrees`), not only by name.  A name-based survey missed
  Dedekind, Jordan and the `Sₙ` criterion (iteration21-review §5 correction).
  Study only: never import TauCeti.
- **`tools/modal_run.sh` does not work from a git worktree** (2026-10-31):
  the worktree's `.git` *file* dangles for the mirroring user (xyz).  Run it
  from a normal clone, or build a standalone mirror (rsync the tree minus
  `.git`/`.lake` into the mirror, keep a git repo there whose
  `refs/remotes/origin/master` points at an empty-tree commit so
  `git diff --name-only origin/master` lists every file and the overlay
  covers the complete state — see the iteration-21 agent mirrors under
  `/home/doz/tmp/math-proof1-temp/agent-work/`).  Local temp artifacts (run
  logs, mirrors, scratch) go under `/home/doz/tmp/math-proof1-temp/` — `/tmp`
  is wiped on reboot (2026-10-31 19:26 incident).
- **A stuck wave worker is the orchestrator's to resolve, autonomously**
  (2026-11-04; iteration23-review §6.6 — two workers died silently with the
  completion notifications lost, and a third stall needed an operator
  rescue): detect via `tools/wave_watchdog.sh` + background-task polls
  (never idle on notifications alone), then terminate → salvage (`salvage:`
  commit on the worker's own `impl/` branch, worktree preserved) → fresh
  respawn with a reconstruction briefing; two stalls on one gate →
  changed-strategy respawn, third → park + report to the operator.  Workers
  treat their WORKLOG as a heartbeat (first session, every §9 checkpoint,
  before/after any > 10 min run).  Full protocol: `external-doc/
  RESEARCH-WORKFLOW.md` §6 "Stuck-worker protocol".
- **`Nat.Prime` is not kernel-decidable** (2026-11-02, iteration-22 lehmer
  worker): `Nat.minFac` is well-founded recursion, so any `decide` touching
  `.Prime` breaks in the kernel.  Use a structural trial-division
  certificate instead (`noFactorFrom` + `prime_of_noFactorFrom` in
  `Tau/LehmerCoverageCount.lean`).
- **Matrix-level `decide` pulls `Classical.choice` via
  `Fintype.decidablePiFintype`** (2026-11-02, iteration-22 hecke-rational
  worker): deciding `∀ i : Fin n, …` or matrix equality lets the instance
  build an `Iff` with `simp`-produced classical pieces; `AxCheckDecide`
  flags it.  Certify entrywise (`ext i j` / `fin_cases` +
decide +kernel`
  per cell) so every decide stays `propext`-clean.
- **`Finset` sums inside a `decide` pull `Classical.choice` + `Quot.sound`**
  (2026-11-03, iteration-23 merge audit): a generated Bézout check
  `∑ j ∈ Finset.range n, … = 1 := by decide +kernel` failed AxCheckDecide at
  48 weights.  Decide the `List` sum (`((List.range n).map f).sum`) and
  derive the `Finset` form with `MaedaLevelOne.finset_sum_range_eq_list`.
- **Entrywise certificates are audited too** (2026-11-05, iteration-24
  integration): the top-level `#audit_decide_certs` never saw `decide
  +kernel` calls inside tactic proofs; `#audit_decide_certs_nested` found
  7600 of 9256 beyond `propext` (5296 in pre-24 files remain — see
  iteration24-review §6.1).  Three causes: `Finset` sums / `Matrix`
  products in the decided cell; `==` on `ℤ` (`BEq ℤ` →
  `Int.instLinearOrderPackage` → `Classical.choice`; use `Int.decEq`); any
  `!![…]` literal in the statement (`Quot.sound`) and `^` on numerals
  (`Monoid.npow`).  Recipe (`HeckeLatticeIndex.hcard_of_check`): integer
  pattern-match tables bridged to the matrices by `fin_cases <;> rfl`, ONE
  `List`-based Bool `decide +kernel` per weight, one generic bridge lemma.
  Run both passes at every close-out.
- **`Polynomial.natDegree_map` needs `[IsSimpleRing R]`** at the pin: for
  `ℤ → ℂ` use `natDegree_map_eq_of_injective (RingHom.injective_int _)`.
  Also missing at the pin: `LinearMap.coeFn_sum` (use
  `LinearMap.sum_apply`), `LinearMap.mul_eq_comp` (`Module.End` mul is comp
  by `rfl`); `dif_pos`/`if_pos` are deprecated (`dite_eq_left`/`ite_eq_left`).
- **Memory: generated per-weight files are import floor + retained
  literals** (2026-11-03 profile): no single declaration dominated; the
  54-weight `HeckeIndexWeights` tree crossed 97 % of the 8 GiB request
  through accumulation alone.  Split such files by dimension (each half
  imports only its own parents) rather than raising the request; and drop
  imports kept only for superseded slices (the profile tells you: a file
  whose declarations all show `+0.00` growth is paying only for imports).
