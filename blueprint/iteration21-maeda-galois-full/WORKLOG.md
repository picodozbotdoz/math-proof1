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

### 2026-10-31 (late) — JordanPrimitive.lean COMPLETE: the (n-1)-cycle + swap finish

`MathProof/ModularForms/JordanPrimitive.lean` (218 lines, light, compiles clean
locally, zero warnings): 
* `MaedaGalois.exists_pow_eq_of_isCycle` — within a cycle's support, every
  point is an iterate of any other (via `SameCycle.exists_pow_eq'`).
* `MaedaGalois.isPreprimitive_of_isPretransitive_of_cycleType_mem` — a
  pretransitive subgroup of Perm(alpha) (card alpha = n >= 3) containing a
  permutation of cycleType {n-1} is PREPRIMITIVE.  Block argument: for a
  block B, either g•B = B (B is a union of g-orbits; if it meets the
  (n-1)-support it contains it, and the translate h^-1•B containing pt cannot
  be disjoint from B, so pt in B and B = univ; else B subset {pt}) or
  g•B is disjoint from B (pt lies in NO g^k-translate; the translates cover
  the support; the translate containing pt is disjoint from all of them,
  hence is the singleton {pt}).
* `MaedaGalois.eq_top_of_isPretransitive_of_cycleType_of_isSwap_mem` — the
  S_n finish through Mathlib's
  `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`.

Gotchas: `MulAction.IsPreprimitive` is a class extending IsPretransitive —
construct with `{ toIsPretransitive := ..., isTrivialBlock_of_isBlock := ... }`;
`IsBlock`'s binders are named g1/g2; pointwise set-smul needs
`open scoped Pointwise`; the subgroup-action smul is NOT syntactically the
Perm-coe smul (one_smul is a field, not rfl — un-ascribe cardinality lemmas
and rewrite); mem_erase's IFF is (ne AND mem) shaped; IsBlock/IsTrivialBlock
API: `Set.eq_empty_iff_forall_notMem`, `Set.disjoint_of_subset_right`,
`Set.mem_smul_set` (Iff.rfl).

Math note: cycleType records only NONTRIVIAL cycles, so the certificate
targets are `FrobHasCycleType q {n-1}` and `FrobHasCycleType q {2}` (the
latter is exactly IsSwap by `isSwap_iff_cycleType`).

### 2026-10-31 (night) — instantiation DESIGN finalized (execution is the next session's first task)

The remaining piece is the Dedekind instantiation in `FrobeniusCycleType.lean`
(the golden lemma is DONE; what follows is the fully-worked-out plan, checked
against the pinned Mathlib, so it can be executed cold):

**Setup.**  `Q := q.map (Int.castRingHom ℚ)` (q : ℤ[X] monic, natDegree n ≥ 3),
`K := Q.SplittingField`, `G := Q.Gal`.  Roots: `x : Fin n ≃ ↥(Q.rootSet K)`
(`Fintype.equivFinOfCardEq` + `card_rootSet_eq_natDegree` from separability);
`Q.rootSet K` Fintype instance exists.  `ℓ` prime with `ℓ ∤ n` and the
certificate `Q̄ := q.map (Int.castRingHom (ZMod ℓ)) = (X - C r) * ḡ`,
`ḡ` monic irreducible of degree n-1, `ḡ(r) ≠ 0` (resp. the transposition
version with two roots and a degree-2 `ḡ`).

**The algebra.**  `ev : MvPolynomial (Fin n) ℤ →+* K :=
MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i => (x i : K))`;
`I := RingHom.ker ev`; `J := I.map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))`;
`A := MvPolynomial (Fin n) (ZMod ℓ) ⧸ J`; `y i := Ideal.Quotient.mk J (X i)`.
All instances are stock (quotient of an MvPolynomial algebra).  NO
ℤ-algebra on K and NO tensor products are needed.

**Golden-lemma hypotheses.**
- `hperm`: `MvPolynomial.rename_apply` gives `act σ (y i) = y (πσ i)` where
  `πσ` is σ's permutation of the roots transported along the enumeration;
  the action is `Ideal.quotientEquiv`-style lift of `MvPolynomial.renameEquiv πσ`
  (J-stability: for p ∈ I, `eval₂Hom cast x (rename πσ p) = eval p (x ∘ πσ)`
  [eval₂Hom-rename] `= σ (eval₂Hom cast x p) [MvPolynomial.hom_eval₂] = σ 0 = 0`,
  using that σ permutes the roots and `σ ∘ Int.castRingHom = Int.castRingHom`).
- `hfree`: if `act σ` fixes all `y i` then πσ = id (the y i are DISTINCT —
  from hunit + Nontrivial A), and G acts faithfully on the rootSet
  (`galActionHom_injective q K` with `Fact (SplittingField.splits)`).
- `hunit`: the certificate identity `Res(q, q') = (x i - x j)² · W` in K
  (`resultant_eq_prod_eval` for monic splitting q: Res = ∏ q'(x i); then
  `Splits.eval_root_derivative`: q'(x i) = ∏_{roots erase x i} (x i - ·)`),
  transported into A by "the difference polynomial vanishes at the roots,
  hence lies in I" — NO injectivity of ev needed.  `Res mod ℓ ≠ 0` is a unit
  scalar of A, so `y i - y j` is a unit.
- `hcard`: `#G = finrank ℚ K` (`Gal.card_of_separable`); `finrank ℤ
  (MvPolynomial ℤ ⧸ I) = finrank ℚ K` via `Module.finrank_baseChange`
  (twice: F_ℓ-side and ℚ-side) + the isos `(ℤ[X]/I) ⊗ ℚ ≅ ℚ[X]/I_ℚ ≅
  ℚ[x₁..xₙ] = K` (K = ℚ[x₁..xₙ] because each root is invertible: q(0) ≠ 0
  for irreducible q of degree ≥ 2, and the splitting field is generated by
  the roots — `SplittingFieldAux.adjoin_rootSet`).  This is the heaviest
  chunk (~200 lines).

**F̄-side analysis.**  The golden lemma gives χ, τ, π with
`χ (y (π i)) = χ (y i)^ℓ`; `ξ i := χ (y i)` are n distinct roots of Q̄ in F̄
(`aeval_algHom_apply`), hence ALL roots.  π is conjugate (via i ↦ ξ i) to the
Frobenius on rootSet Q̄ F̄, whose orbits are {r} (fixed: `FiniteField.pow_card`
for ZMod ℓ) and the root set of ḡ — one orbit of size d := deg ḡ: the orbit
O = {α^(ℓ^k)} satisfies α^(ℓ^d) = α (α lies in F_ℓ(α), a finite field with
ℓ^d elements — `FiniteField.pow_card_pow` after `FiniteField.card`), the
polynomial ∏_{k<s}(T - α^(ℓ^k)) has F_ℓ-coefficients (Frobenius fixes its
coefficients; the fixed field of Frobenius on F̄ is F_ℓ via rootSet-card of
X^ℓ - X), is divisible by minpoly α = ḡ, and has degree s ≤ d, whence = ḡ.
So cycleType π = {d} by conjugation-invariance (`cycleType_conj`) and
`IsCycle.cycleType`-counting on the Frobenius permutation of the d roots.

**Packaging.**  `FrobHasCycleType Q {n-1}`: take σ := τ; the galActionHom-permutation
of rootSet ℂ is conjugate to σ's action on rootSet K
(`rootsEquivRootsAux`), which is conjugate to π (both transport σ along root
enumerations) — cycleType equal by `cycleType_conj`.  Ditto {2} for the
transposition certificate.  Then `MaedaGalois.
eq_top_of_isPretransitive_of_cycleType_of_isSwap_mem` finishes each weight
(transitivity from `galAction_isPretransitive` on rootSet ℂ; the subgroup
`galActionHom Q ℂ '' Q.Gal`).

Per-weight data: `research/iteration21/data/galoisfull_certs.json` (committed).
Estimated remaining Lean: ~600-900 lines over the packaging + rank chunks.

### 2026-10-31 (night, cont.) — G2 partial: certificate slice WIP saved; session close

The Dedekind instantiation is ~50% drafted.  The freshman's-dream lemma
(`not_irreducible_of_monic_of_derivative_eq_zero`: monic + deg >= 2 + gb' = 0
=> not irreducible, via gb = expand l gb0 = gb0^l and the degree/l-unit
argument) is ~90% written but not yet green: the remaining errors are
mechanical (the coeff-of-Finset-sum simp-lemma name — `Polynomial.finset_sum_coeff`
does NOT exist at this pin; use the `congrArg (Polynomial.lcoeff (ZMod ℓ) i)
hgb0` + `map_sum` route; `Nat.mul_div_cancel'` does not exist for Nat — use
`Nat.div_add_mod` + `Nat.mod_eq_zero_of_dvd`; `Polynomial.isUnit_iff` is the
`∃ r, IsUnit r ∧ C r = p` form; `Nat.cast_add_one` is `↑(n+1) = ↑n + 1`
(reversed); `Irreducible`'s second field is applied as `hirr.2 ⟨a, b, hab, _, _⟩`;
U+1E21 (ḡ) is NOT accepted in Lean identifiers — use gb).
The draft (incl. the two IsCoprime-stability mini-lemmas, the factor-theorem
Bézout `hc1`, the `dvd_or_coprime` route to `IsCoprime (Q̄, Q̄')`, and the
resultant transport through `resultant_map_map` +
`natDegree_map_eq_of_isUnit_leadingCoeff`) is saved at
/home/doz/tmp/math-proof1-temp/agent-work/maeda-galois-full/wip/FrobeniusCycleType.WIP.lean
and the library file is restored to the committed green state.

Tooling: mrun.sh now passes LEAN_CHECK_MEMORY_MIB=8192 per the base-branch
memory right-sizing (01b58a9); the mirror's lean_check.py stays at the
pre-change copy until merge time; LEAN_CHECK_NO_CACHE=1 does not work in the
old copy (do not rely on it).

### 2026-11-01 — G2 continuation: certificate slice GREEN; Frobenius.lean route discovered; descope

**Certificate slice GREEN (commit 6ca292d).**  `resultant_ne_zero_of_linear_mul_irreducible`
in FrobeniusCycleType.lean (396 lines, light, zero warnings): from the
factorization certificate to IsCoprime (Q-bar, Q-bar') and Res(q,q') not-Equiv 0
mod l.  Key routes at this pin: PerfectRing.ofFiniteOfIsReduced + toPerfectField
give PerfectField (ZMod l) as a haveI; PerfectField.separable_of_irreducible
kills gb' = 0; EuclideanDomain.dvd_or_coprime + natDegree_derivative_lt kill
gb | gb'; the factor-theorem Bezout is scaled via C-mul/inv_mul_cancel with the
ATOM-matching caveat (C(-x) and -C(x) are different ring-atoms for
linear_combination — keep the u-argument in the negated-product form
-(C c^-1 * s), NOT the scalar-smul form); the resultant transport needs
resultant_map_map (the f/g/m/n section variables instantiated with named args)
and degree equalities via coeff_map/coeff_derivative/coeff_natDegree + hQbd
(Monic.natDegree_map) + derivative natDegree = n-1 via le_antisymm of
natDegree_derivative_le and coeff_natDegree (NOT natDegree_map_eq_of_isUnit —
the Z-cast of n is not a Z-unit); the coe_castRingHom rewrite exposes the
ring-hom application for resultant_map_map (the goal's coercion arrow is
Int.cast, not the RingHom coe — bridge with a show rfl term).

**FROBENIUS.LEAN ROUTE DISCOVERED (major simplification for G2b/c).**
Mathlib.RingTheory.Frobenius.lean HAS Dedekind's theorem:
`IsArithFrobAt.exists_of_isInvariant [Q.IsPrime] [Finite (S/Q)] :
  ∃ σ : G, IsArithFrobAt R σ Q` — in the setting of a finite group G acting
on a ring S (MulSemiringAction), R the base with SMulCommClass, under
`Algebra.IsInvariant R S G` (every fixed point of S lies in the image of R),
and Q a prime of S with finite residue.  IsArithFrobAt R σ Q means
σ•x - x^(Nat.card (R ⧸ Q.under R)) ∈ Q for ALL x : S.

Instantiation plan (replaces the entire golden-lemma application AND the
presented-algebra count):
- S := O := ℤ[x₁..xₙ] ⊆ K (rootOrder := Algebra.adjoin ℤ (Set.range x);
  Module.Finite ℤ O via Algebra.finite_adjoin_of_finite_of_isIntegral — DONE
  in the WIP2 draft); the x i are integral (roots of monic q).
- G := Q.Gal acts on O (σ x i = x (πσ i) keeps O stable; the MulSemiringAction
  instance is transported from the K-action through the O ↪ K embedding —
  the one genuinely new instance, ~60 lines).
- R := ℤ with SMulCommClass (Galois fixes ℤ) and Algebra.IsInvariant ℤ O G
  (a G-fixed element of O lies in the Galois-fixed field ℚ — via
  IsGalois.tfae on Q.SplittingField — and is integral, hence in ℤ).
- 𝔪 := a maximal ideal of O containing ℓO (ℓO is proper: 1/ℓ is not integral;
  Ideal.exists_maximal); Finite (O/𝔪) (finite module over ZMod ℓ);
  𝔪.under ℤ = (ℓ) (𝔪 is maximal over ℓ); Nat.card (ℤ/(ℓ)) = ℓ.
- IsArithFrobAt.exists_of_isInvariant gives σ with σ x - x^ℓ ∈ 𝔪 for ALL x ∈ O.
- Reducing the roots: x̄ i := x i mod 𝔪 are distinct (the resultant identity
  transported into O via the IsScalarTower ℤ O K, then mod 𝔪; Res mod l ≠ 0 is
  a unit of O/𝔪) and exhaust the roots of Q-bar in O/𝔪 ⊆ F̄ (n distinct roots
  of a separable degree-n polynomial); x̄ (πτ i) = x̄ i ^ l, so the Frobenius
  orbits on the roots are the factor-degree orbits {r} and the roots of gb
  (one orbit of size n-1 by the minpoly = gb argument); cycleType transport
  via rootsEquivRootsAux + cycleType_conj gives FrobHasCycleType.
- Note IsArithFrobAt's exponent is #(ℤ/(𝔪 ∩ ℤ)) = l EXACTLY (the invariant
  subring is Z, not the full ring of integers) — the right power for the
  factor-degree analysis.  The full AKLB instance
  (Algebra.isInvariant_of_isGalois, Invariant/Galois.lean) also exists for
  B := the integral closure of Z in K if the O-version needs backup.

Estimated remaining for G2: ~250-350 lines (the MulSemiringAction-on-O
instance, IsInvariant ℤ O G, the maximal ideal, the root-reduction transport,
the orbit analysis, the packaging).  G2-final/G3/G4 unchanged.
WIP2 draft (rootOrder + finiteness) saved at wip/FrobeniusCycleType.WIP2.lean;
the library file is restored to the committed green state (6ca292d).
