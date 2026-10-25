# Iteration 7 plan — Mordell's theorem via level-one Hecke operators T_p

**Goal.** Formalize Mordell's 1917 theorem on the Ramanujan τ function:

* `τ(p·n) = τ(p)·τ(n)` for `p` prime with `p ∤ n`,
* `τ(p^{r+1}) = τ(p)·τ(p^r) − p^{11}·τ(p^{r−1})`,
* hence `τ(m·n) = τ(m)·τ(n)` for coprime `m, n` (full multiplicativity).

## Proof architecture (classical, mapped to Mathlib as of v4.36.0-rc1)

1. **The operator.** For `p ≥ 1`, `f : ℍ → ℂ`, weight `k`:
   `T_p f (z) = p⁻¹ · Σ_{j<p} f((z+j)/p) + p^{k−1} · f(p·z)`
   (this is `p^{k−1} Σ_σ f ∣[k] σ` over the coset reps `σ ∈ {[1 j; 0 p]} ∪ {[p 0; 0 1]}`
   of `Γ(1)\M_p`).

2. **Modularity** (needs `p` prime). `T_p f ∣[k] γ = T_p f` for all `γ ∈ SL(2,ℤ)`, via
   `SlashInvariantForm.slash_action_generators_SL2Z` (S and T generate):
   * *T-invariance*: index shift `j ↦ j+1` + 1-periodicity of `f`
     (`f(w + n) = f(w)` from `T ^ n • w = n +ᵥ w`, `denom (T^n) = 1`).
   * *S-invariance*: the classical coset permutation, made explicit. With
     `S • z = −1/z`:
     - `j = 0` term: `f(−1/(pz)) = (pz)^k f(pz)` (S-invariance at `pz`).
     - second term: `f(−p/z) = (z/p)^k f(z/p)` (S-invariance at `z/p`).
     - `j ∈ [1, p−1]`: let `j'` solve `j·j' ≡ −1 (mod p)` (prime `p`), and
       `σ_j = [[j, −(jj'+1)/p], [p, −j']] ∈ SL(2,ℤ)`. Point identity:
       `σ_j • ((z+j')/p) = (jz−1)/(pz)` and `denom σ_j ((z+j')/p) = z`, giving
       `z^{−k} f((jz−1)/(pz)) = f((z+j')/p)`. The map `j ↦ j'` is the involution
       `−(·)⁻¹` of `(ZMod p)ˣ`, so it bijects `[1, p−1]`.
3. **Holomorphy / cusp condition.** `(z+j)/p = γ_j • z` with `γ_j = [1 j; 0 p] ∈ GL⁺(2,ℝ)`:
   MDiff via `mdifferentiable_smul` + comp; bounded/zero at `i∞` via
   `tendsto_smul_atImInfty` (needs `γ 1 0 = 0`) composed with `f`'s condition.
   `T_p` maps `ModularForm 𝒮ℒ k → ModularForm 𝒮ℒ k` and `CuspForm → CuspForm`.
4. **q-expansion coefficient formula** (needs only `p ≥ 1`):
   `(T_p f)_m = f_{pm} + p^{k−1} [p ∣ m] f_{m/p}`, via
   `ModularFormClass.qExpansion_coeff_unique` from the pointwise `HasSum`
   (`ModularForm.hasSum_qExpansion`):
   - `f(pz)`: `𝕢 1 (pz) = (𝕢 1 z)^p`, then *pad* the subsequence `n = p·m`.
   - `Σ_j f((z+j)/p)`: `𝕢 1 ((z+j)/p) = ρ·ξ^j` (`ρ = e^{2πiz/p}`, `ξ = e^{2πi/p}`),
     the root-of-unity filter `Σ_{j<p} ξ^{jn} = p·[p ∣ n]`, then *unpad* `n = p·m`.
   Pad/unpad both reduce to `hasSum_extend_zero` (`Function.extend (·*p) u 0`).
5. **Eigenform + coefficients** (`MathProof/Tau/Mordell.lean`). `T_p Δ ∈ S₁₂ = ℂ·Δ`
   (Mathlib: `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`), so
   `T_p Δ = λ_p Δ`; comparing `q^1`-coefficients via the formula and the Iteration-2
   bridge `(qExpansion 1 Δ)_n = τ n` gives `λ_p = τ(p)` (using `τ 1 = 1`); comparing
   `q^n`-coefficients gives Mordell. Full coprimality statement by strong induction
   on the prime factorization.

## Novelty (research agent, 2026-10-25)

* Mathlib has **no** Hecke operators on modular forms (only a stalled 88-line
  definition PR #40934; abstract Hecke-ring scaffolding #41251+ is unconnected to forms).
* **tomdif/RamanujanLean** (independent, outside Mathlib, unpublished) has τ-multiplicativity
  sorry-free with the same architecture (prime `T_p` on cusp forms). We cite it as
  concurrent independent work; our contribution is the independent formalization,
  integrated with this repo's stack (algebraic τ ↔ analytic Δ bridge, kernel-verified
  values/bounds, congruences), all about *our* `Ramanujan.tau`.
* Remaining formalization novelty (next iterations): general `T_n` over
  `FixedDetMatrices.reps`, operator multiplicativity `T_m T_n = T_{mn}` (coprime) —
  a mathlib PR candidate.

## File plan

* `MathProof/ModularForms/HeckeLevelOne.lean` — steps 1–4 (light module, CI target).
* `MathProof/Tau/Mordell.lean` — step 5 (light module, CI target).

## Status log

- [x] API survey (all lemmas above exist at this Mathlib pin; verified by #check)
- [ ] HeckeLevelOne.lean
- [ ] Mordell.lean
- [ ] Modal verify + docs + log
