import MathProof.ModularForms.HeckeLevelOne
import MathProof.ModularForms.MaedaLevelOne

/-!
# Hecke operators commute at level one

For level-one cusp forms of any weight, the Hecke operators `T_p`, `T_q`
(defined in `MathProof/ModularForms/HeckeLevelOne.lean`) commute.  The whole
computational content is the q-coefficient formula

    (T_p f)_m = f_{p m} + p^{k-1} [p ∣ m] f_{m / p},

unrolled twice: `(T_p (T_q f))_m` and `(T_q (T_p f))_m` both reduce to

    f_{q p m} + (cross terms),

and the two expansions agree after case-splitting the divisibility lattice
`p ∣ m`, `q ∣ m` (for distinct primes the indicators `[q ∣ p m]`, `[p ∣ m]`
match branchwise; for `p = q` both sides are literally the same expression).
Operator equality then follows from injectivity of the q-expansion
(`ModularForm.qExpansion_injective`, lifted to cusp forms through
`CuspForm.toModularFormₗ`).

Main results:

* `heckeTP2_qExpansion_coeff`: the composed coefficient formula (one unrolling
  of `heckeTP_qExpansion_coeff` on each factor);
* `heckeTP_commute`: `T_p (T_q f) = T_q (T_p f)` for all primes `p q`, cusp
  forms `f` of any weight;
* `heckeTPₗ_commute`: the `ℂ`-linear-map version `Commute (heckeTPₗ k hp)
  (heckeTPₗ k hq)` — the hypothesis discharged by the Hecke-algebra upgrade
  (`HeckeAlgebra.exists_aeval_of_commute_of_irreducible_charpoly` in
  `MathProof/ModularForms/HeckeAlgebraQT2.lean`, instantiated per weight in
  `MathProof/ModularForms/HeckeGeneratedByT2.lean`).
-/

open UpperHalfPlane ModularForm CuspForm Polynomial HeckeLevelOne MaedaLevelOne
open scoped MatrixGroups

namespace HeckeCommute

/-! ### q-expansion injectivity on cusp forms -/

section Injective

variable {k : ℤ}

/-- **q-expansion injectivity for level-one cusp forms**: two cusp forms of the
same weight whose q-expansion coefficients agree coefficient-by-coefficient
are equal.  (Injectivity is Mathlib's, for modular forms; the cusp-form side
is transported through the inclusion `CuspForm.toModularFormₗ`, which does not
change the underlying function.) -/
theorem qExpansion_coeff_ext {f g : CuspForm 𝒮ℒ k}
    (h : ∀ m : ℕ, (qExpansion 1 f).coeff m = (qExpansion 1 g).coeff m) : f = g := by
  have hcoe : ∀ u : CuspForm 𝒮ℒ k, qExpansion 1 ⇑(toModularFormₗ u) = qExpansion 1 u := fun u => rfl
  have hps : qExpansion 1 ⇑(toModularFormₗ f) = qExpansion 1 ⇑(toModularFormₗ g) := by
    rw [hcoe f, hcoe g]
    exact PowerSeries.ext fun m => h m
  exact CuspForm.toModularFormₗ_injective
    (ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL hps)

end Injective

/-! ### The composed coefficient formula -/

section Composed

variable {p q : ℕ}

/-- **Composed coefficient formula**: unrolling `heckeTP_qExpansion_coeff`
twice, the `m`-th q-coefficient of `T_p (T_q f)` is

    f_{q (p m)} + q^{k-1} [q ∣ p m] f_{(p m)/q}
      + p^{k-1} [p ∣ m] (f_{q (m/p)} + q^{k-1} [q ∣ m/p] f_{(m/p)/q}).

This is the shape in which both applications of the single-operator formula
appear verbatim (the `p^{k-1}` factor sits outside the `p ∣ m` indicator), so
it needs no arithmetic beyond the two rewrites. -/
theorem heckeTP2_qExpansion_coeff (hp : p.Prime) (hq : q.Prime) {k : ℤ}
    (f : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 (heckeTP hp (heckeTP hq f))).coeff m
      = (qExpansion 1 f).coeff (q * (p * m))
        + (q : ℂ) ^ (k - 1)
          * (if q ∣ p * m then (qExpansion 1 f).coeff ((p * m) / q) else 0)
        + (p : ℂ) ^ (k - 1)
          * (if p ∣ m then
              (qExpansion 1 f).coeff (q * (m / p))
                + (q : ℂ) ^ (k - 1)
                  * (if q ∣ m / p then (qExpansion 1 f).coeff ((m / p) / q) else 0)
            else 0) := by
  rw [heckeTP_qExpansion_coeff hp (heckeTP hq f) m,
    heckeTP_qExpansion_coeff hq f (p * m), heckeTP_qExpansion_coeff hq f (m / p)]

end Composed

/-! ### Commutativity -/

section Commute

variable {p q : ℕ}

/-- A prime `q` does not divide a different prime `p`. -/
private lemma prime_not_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : ¬ q ∣ p := by
  intro h
  rcases (Nat.dvd_prime hp).mp h with h1 | h2
  · exact hq.ne_one h1
  · exact hpq h2.symm

/-- If the prime `q` divides `p * m` but not the prime `p ≠ q`, it divides `m`. -/
private lemma dvd_of_dvd_mul' {p q : ℕ} (hq : q.Prime) {m : ℕ} (hqp : ¬ q ∣ p) (h : q ∣ p * m) :
    q ∣ m := by
  rcases hq.dvd_mul.mp h with h1 | h2
  · exact absurd h1 hqp
  · exact h2

/-- **Coefficient-level commutativity**: for all primes `p q` (possibly equal),
every cusp form `f` and every index `m`, the `m`-th q-coefficients of
`T_p (T_q f)` and `T_q (T_p f)` agree.  For `p = q` both composed expansions
are literally the same expression; for `p ≠ q` the divisibility indicators
match branchwise (`q ∣ p m ↔ q ∣ m` for `q ≠ p`, etc.) and each branch closes
by cancellation of the `m / p`, `m / q` divisions. -/
theorem heckeTP_qExpansion_coeff_commute (hp : p.Prime) (hq : q.Prime) {k : ℤ}
    (f : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 (heckeTP hp (heckeTP hq f))).coeff m
      = (qExpansion 1 (heckeTP hq (heckeTP hp f))).coeff m := by
  rw [heckeTP2_qExpansion_coeff hp hq f m, heckeTP2_qExpansion_coeff hq hp f m]
  rcases eq_or_ne p q with rfl | hpq
  · rfl
  have hqnp : ¬ q ∣ p := prime_not_dvd hp hq hpq
  have hpnq : ¬ p ∣ q := prime_not_dvd hq hp hpq.symm
  by_cases hpm : p ∣ m
  · by_cases hqm : q ∣ m
    · -- `p ∣ m` and `q ∣ m`: write `m = p * (q * w)`
      obtain ⟨t, rfl⟩ := hpm
      have hqt : q ∣ t := dvd_of_dvd_mul' hq hqnp hqm
      obtain ⟨w, rfl⟩ := hqt
      have hd1 : p * (p * (q * w)) / q = p * p * w := by
        rw [show p * (p * (q * w)) = q * (p * p * w) from by ring,
          Nat.mul_div_cancel_left _ hq.pos]
      have hd2 : p * (q * w) / p = q * w := Nat.mul_div_cancel_left _ hp.pos
      have hd3 : q * w / q = w := Nat.mul_div_cancel_left _ hq.pos
      have hd4 : q * (p * (q * w)) / p = q * (q * w) := by
        rw [show q * (p * (q * w)) = p * (q * (q * w)) from by ring,
          Nat.mul_div_cancel_left _ hp.pos]
      have hd5 : p * (q * w) / q = p * w := by
        rw [show p * (q * w) = q * (p * w) from by ring, Nat.mul_div_cancel_left _ hq.pos]
      have hd6 : p * w / p = w := Nat.mul_div_cancel_left _ hp.pos
      have hi0 : q * (p * (p * (q * w))) = p * (q * (p * (q * w))) := by ring
      have hi1 : p * (p * w) = p * p * w := by ring
      rw [hd1, hd2, hd3, hd4, hd5, hd6,
        ite_eq_left (show q ∣ p * (p * (q * w)) from ⟨p * p * w, by ring⟩),
        ite_eq_left (show p ∣ p * (q * w) from ⟨q * w, by ring⟩),
        ite_eq_left (show q ∣ q * w from ⟨w, by ring⟩),
        ite_eq_left (show p ∣ q * (p * (q * w)) from ⟨q * q * w, by ring⟩),
        ite_eq_left (show q ∣ p * (q * w) from ⟨p * w, by ring⟩),
        ite_eq_left (show p ∣ p * w from ⟨w, by ring⟩), hi0, hi1]
      ring
    · -- `p ∣ m`, `q ∤ m`: write `m = p * t` with `q ∤ t`
      obtain ⟨t, rfl⟩ := hpm
      have hqt : ¬ q ∣ t := by
        intro h
        rcases h with ⟨r, rfl⟩
        exact hqm ⟨p * r, by ring⟩
      have hd2 : p * t / p = t := Nat.mul_div_cancel_left _ hp.pos
      have hd4 : q * (p * t) / p = q * t := by
        rw [show q * (p * t) = p * (q * t) from by ring, Nat.mul_div_cancel_left _ hp.pos]
      have hi0 : q * (p * (p * t)) = p * (q * (p * t)) := by ring
      rw [ite_eq_right (show ¬ q ∣ p * (p * t) from
          fun h => hqm (dvd_of_dvd_mul' hq hqnp h)),
        hd2,
        ite_eq_left (show p ∣ p * t from ⟨t, rfl⟩),
        ite_eq_right hqt,
        ite_eq_left (show p ∣ q * (p * t) from ⟨q * t, by ring⟩),
        ite_eq_right hqm, hi0, hd4]
      ring
  · by_cases hqm : q ∣ m
    · -- `p ∤ m`, `q ∣ m`: write `m = q * u` with `p ∤ u`
      obtain ⟨u, rfl⟩ := hqm
      have hpu : ¬ p ∣ u := by
        intro h
        rcases h with ⟨r, rfl⟩
        exact hpm ⟨q * r, by ring⟩
      have hd2 : q * u / q = u := Nat.mul_div_cancel_left _ hq.pos
      have hd4 : p * (q * u) / q = p * u := by
        rw [show p * (q * u) = q * (p * u) from by ring, Nat.mul_div_cancel_left _ hq.pos]
      have hi0 : q * (p * (q * u)) = p * (q * (q * u)) := by ring
      rw [ite_eq_right (show ¬ p ∣ q * (q * u) from
          fun h => hpu (dvd_of_dvd_mul' hp hpnq (dvd_of_dvd_mul' hp hpnq h))),
        ite_eq_right hpm,
        hd2,
        ite_eq_left (show q ∣ q * u from ⟨u, rfl⟩),
        ite_eq_right hpu,
        ite_eq_left (show q ∣ p * (q * u) from ⟨p * u, by ring⟩), hi0, hd4]
      ring
    · -- `p ∤ m`, `q ∤ m`: only the leading coefficients survive
      rw [ite_eq_right (show ¬ q ∣ p * m from fun h => hqm (dvd_of_dvd_mul' hq hqnp h)),
        ite_eq_right hpm,
        ite_eq_right (show ¬ p ∣ q * m from fun h => hpm (dvd_of_dvd_mul' hp hpnq h)),
        ite_eq_right hqm,
        show q * (p * m) = p * (q * m) from by ring]
      ring

/-- **Hecke operators commute at level one**: `T_p (T_q f) = T_q (T_p f)` for
all primes `p q` and cusp forms `f` of any weight. -/
theorem heckeTP_commute (hp : p.Prime) (hq : q.Prime) {k : ℤ} (f : CuspForm 𝒮ℒ k) :
    heckeTP hp (heckeTP hq f) = heckeTP hq (heckeTP hp f) :=
  qExpansion_coeff_ext fun _ => heckeTP_qExpansion_coeff_commute hp hq f _

/-- The linear-map version: `heckeTPₗ k hp` commutes with `heckeTPₗ k hq`. -/
theorem heckeTPₗ_commute (hp : p.Prime) (hq : q.Prime) (k : ℤ) :
    Commute (heckeTPₗ k hp) (heckeTPₗ k hq) := by
  change heckeTPₗ k hp * heckeTPₗ k hq = heckeTPₗ k hq * heckeTPₗ k hp
  refine LinearMap.ext fun f => ?_
  change heckeTP hp (heckeTP hq f) = heckeTP hq (heckeTP hp f)
  exact heckeTP_commute hp hq f

end Commute

end HeckeCommute
