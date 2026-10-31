# Worklog — impl/iteration21/maeda-galois-full

Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations from the blueprint).  This file
is the inter-session resume point: make it possible to continue cold.

## Entries

### 2026-10-31 — Context read; ARCHITECTURE DECISION (before any code)

Read: AGENTS.md, CODING_STANDARDS.md, BLUEPRINT.md, MaedaPermCriterion/MaedaGalois{,4,5},
S3-handoff (25 gotchas), census JSON, Mathlib at the pin (Resultant/, Jordan.lean,
Primitive/Blocks, PolynomialGaloisGroup, Finite/, Perfect).

**Key discovery 1 — `JordanFor n` is false for our n (6..10), as its own docstring warns.**
The interface `JordanFor n` quantifies over ALL transitive groups containing ANY p-cycle
(p ≤ n−3); the S₃≀S₂ ≤ S₆ counterexample kills n = 6 (transitive, 3-cycle, no A₆), and
similar wreath products kill 7..10. Discharging it via the corrected Jordan form needs
Wielandt 13.9 (primitive + prime-order cycle ⟹ Aₙ), which is an explicit Mathlib TODO.
⇒ Take the blueprint's sanctioned fallback for ALL 30 weights: **(n−1)-cycle + transposition**.
Route: transitive + (n−1)-cycle ⟹ *primitive* (elementary block argument, to be proved in
`JordanPrimitive.lean`), then Mathlib `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`
(primitive + swap ⟹ Sₙ) — the swap itself supplies the odd element, so no separate
disc-non-square input is needed for the finish.

**Key discovery 2 — Dedekind/Frobenius is absent from Mathlib (risk R2 confirmed) but has a
fully elementary proof avoiding number theory ("golden bijection").** Plan for
`FrobeniusCycleType.lean`:
- q : ℤ[X] monic, q_ℚ separable, K = splitting field, x₁..xₙ the roots (enumerated),
  O = ℤ[x₁..xₙ] ⊆ K (finite free, rank = |Gal|), Ā = O/ℓO (F_ℓ-algebra).
- G = Gal acts on Ā by F_ℓ-algebra automorphisms; ℓ ∤ disc(q) ⟹ each x̄ᵢ − x̄ⱼ is a unit
  in Ā (Bézout on the integer disc(q)).
- Freeness: χ ∘ σ̄ = χ with σ ≠ 1 is impossible because the χ(x̄ᵢ) are distinct.
- Count: #Hom_{F_ℓ-alg}(Ā, F̄_ℓ) ≤ dim_{F_ℓ} Ā = |G| by **Dedekind independence of
  characters** (homs are F_ℓ-linear, independent over F̄, dual space has dim = dim Ā);
  no reducedness of Ā needed (this is the trick that avoids ring-of-integers theory).
- Nonempty: Ā ≠ 0 ⟹ maximal ideal ⟹ residue field embeds into F̄_ℓ.
- One orbit ⟹ Hom ≅ G; Frobenius postcomposition (χ ↦ (·^ℓ) ∘ χ) commutes with the
  G-action ⟹ there is σ₀ ∈ Gal with χ₀(σ₀ xᵢ) = χ₀(xᵢ)^ℓ for all i.
- Finite-field side: the ξᵢ := χ₀(x̄ᵢ) are the distinct roots of q̄ in F̄; the Frobenius
  orbit of ξᵢ has size deg(minpoly) = deg(its irreducible factor ḡⱼ) (G(T) := ∏_{k<s}(T−fr^k ξ)
  has F_ℓ-coefficients since fr permutes its roots cyclically, so minpoly ∣ G ∣ minpoly).
- Conclusion: Gal contains an element whose permutation of the roots has cycleType =
  {deg ḡⱼ} — this discharges `MaedaGalois.FrobHasCycleType`.
Facts to certify per weight (all kernel-cheap): q̄ = ∏ ḡⱼ mod ℓ (reflected product check,
gen_maedan's `hmap` pipeline), each ḡⱼ irreducible mod ℓ (Rabin certificates —
irreducible factors of a squarefree-free... plus pairwise coprime ⟹ q̄ squarefree ⟹
ℓ ∤ disc(q) via resultant_map + resultant_eq_zero_iff + resultant_deriv/discr).
Deviations from blueprint §3/§4 (both within its fallback provisions):
- corrected-Jordan p > n/2 route NOT taken (needs unformalized Wielandt 13.9);
  (n−1)-cycle route for all dims (it is in any case the only option for n ∈ {6,7}).
- `eq_top_of_transitive_of_jordan_of_odd` unused; finish via Mathlib swap theorem.
`FrobHasCycleType` is still the interface discharged (statement unchanged).


### 2026-10-31 (afternoon) — reboot recovery; G0a: golden lemma COMPLETE (commit 428acf5)

Host reboot killed the predecessor mid-run. Recovered state from worktree +
WORKLOG (decisions honored: (n-1)-cycle route for all dims, swap-theorem
finish, FrobHasCycleType interface unchanged).

`FrobeniusCycleType.lean` WIP had two `sorry`s, a broken tail and a bogus
`Finite` instance. Completed and compiled clean locally (single module,
`lake env lean`, ~0 errors after fixes), zero warnings, no banned constructs:

* `FrobeniusCert.card_algHom_le_finrank` — Dedekind count (kept from WIP).
* `FrobeniusCert.nonempty_algHom` — kept from WIP.
* `FrobeniusCert.finite_algHom` — **new**: finiteness of `A →ₐ[ZMod ℓ] F̄`;
  injects homs into `Π a, (minpoly (ZMod ℓ) a).rootSet F̄` (each rootSet
  finite, `Fintype A` index). Integrality via `IsIntegral.of_finite`;
  membership via `mem_rootSet` (aeval-based in this Mathlib) +
  `aeval_algHom_apply` + `minpoly.aeval`.
* `FrobeniusCert.exists_frobenius_perm` — **the golden lemma, complete**:
  for `act : G →* (A ≃ₐ[ZMod ℓ] A)`, `y : Fin n → A` with `hperm`/`hfree`/
  `hunit`/`hcard : #G = finrank`, there are `χ : A →ₐ F̄`, `τ : G`,
  `π : Perm (Fin n)` with `act τ (y i) = y (π i)` and
  `χ (y (π i)) = χ (y i) ^ ℓ`.  Frobenius postcomposition is
  `(FiniteField.frobeniusAlgHom (ZMod ℓ) F̄).comp χ` (`coe = (· ^ card)`,
  `ZMod.card` turns it into `^ ℓ`); orbit = everything by Dedekind count +
  injectivity antisymmetry; surjectivity of the orbit map through
  `Set.card_range_of_injective` (plain-function variant; `Fintype.card_range`
  now wants an `EmbeddingLike`).

Lean gotchas hit (all reproducible, worth remembering):
1. **A one-step `calc a = b := e` inside a `by`-block swallows the following
   tactic lines at parse time** (the parser keeps looking for `:=`) — the
   resulting phantom errors ("unknown identifier" for names defined earlier,
   "unknown tactic obtain") point at unrelated lines.  Replace with plain
   `rw`.  Multi-step calcs are fine.
2. **Type-ascribed `set x : T := e with h` misbinds** (bound x : first
   component of T in one probe) — use un-ascribed `set x := e with h`.
3. `Fintype.card_range` now requires `EmbeddingLike`; for a plain injective
   function use `Set.card_range_of_injective`.
4. `Set.Finite.fintype` cannot be registered as an instance (non-class
   argument); a `private noncomputable rangeFintype` helper + local instance
   works.  `Set.mem_rootSet` is aeval-based in this Mathlib and needs
   `Module.IsTorsionFree (ZMod ℓ) F̄` (supplied by the file's field instance).
5. `Frobenius` on `F̄` as a `ZMod ℓ`-algebra hom: `FiniteField.frobeniusAlgHom
   (ZMod ℓ) F̄` (K finite, R arbitrary K-algebra) — do NOT hand-roll.

Next: Modal tooling recreation, then the Dedekind instantiation
(Ā = ℤ[x₁..xₙ] ⊗ F_ℓ, rank = #Gal via finrank_baseChange, unit differences
via resultant Bézout) and `frob_cycleType_of_factorization`.

### 2026-10-31 (evening) — G1 PASSED: certificates re-derived for all 30 weights

`tools/galoisfull_certs.py` + `research/iteration21/data/galoisfull_certs.json`.
Every weight has BOTH certificate primes (never trusted the census; census
cross-checked where applicable — it had missed e.g. k=110 nm1@137, k=134
transp@7403183, because its scan range was too small for the Chebotarev
density 1/(2(n-2)!) of transposition primes).  Certificate shape per weight:
- nm1: (ell1, root r, gbar) with P mod ell1 = (X - r) * gbar, gbar monic
  irreducible deg n-1, gbar(r) != 0  => cycleType {n-1};
- transp: (ell2, roots r_1..r_{n-2}, hbar) with P mod ell2 =
  prod (X - r_i) * hbar, hbar monic irreducible deg 2, r_i distinct,
  hbar(r_i) != 0  => cycleType {2} (a swap; Mathlib isSwap_iff_cycleType:
  IsSwap <-> cycleType = {2} — fixed points do not appear in cycleType).
Both give q-bar squarefree (gcd(P,P')=1 re-derived), hence ell ∤ Res(q,q').
