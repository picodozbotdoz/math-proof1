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

