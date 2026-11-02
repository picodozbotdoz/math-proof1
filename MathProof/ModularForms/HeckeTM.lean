import MathProof.ModularForms.HeckeCommute

/-!
# The Hecke operators `T_m` for all `m ≥ 1` at level one

For every integer weight `k` and every index `m ≥ 1` we define the level-one
Hecke operator `heckeTM k m` on `CuspForm 𝒮ℒ k` by the RECURSIVE ROUTE
(iteration-23 probe 1, §2): `T₁ = id`, and for `m ≥ 2`, with `p = m.minFac`
the least prime factor and `n = m / p`,

    T_m = T_p ∘ T_n − p^(k-1) • [p ∣ n] T_{n/p},

where `T_p` is the landed prime operator `HeckeLevelOne.heckeTP` (as a linear
map, `heckeTPₗ`).  No coset sums are needed: every operator so defined is a
ℂ-linear combination of compositions of landed prime operators.

The main theorem is the general coefficient formula

    `heckeTM_qExpansion_coeff`:  (T_m f)_n = ∑_{d ∣ gcd m n} d^(k-1) • f_{m n / d²},

proved by strong induction on `m`.  The arithmetic heart is the divisor-lattice
reindexing `tsumF_prime_step` (probe 1, check B at one prime): sums over
`{d : d ∣ m, d ∣ n}` split along the `p`-divisibility of `d` into a `p`-free
part and a scaled part `d ↦ p * d`, and the two explosions of the filter by
`p` (through the first or the second slot) assemble into the two-term
recursion.

Consequences: the prime specialization `heckeTM_prime` (a one-line rewrite to
the landed `heckeTP_qExpansion_coeff`), `heckeTM_one` (the duality ingredient
`(T_m f)₁ = f_m`), and the prime-power two-term recursion
`heckeTM_prime_pow_succ`.

## Non-objectives

The coset-sum definition of `T_m` (our operator coincides with it on cusp
forms through the shared coefficient formula — TauCeti's
`heckeTCuspLevelOne` is the reference shape, study only); operators on
non-cusp forms; level `N > 1`.
-/

open UpperHalfPlane ModularForm CuspForm HeckeLevelOne HeckeCommute MaedaLevelOne
open scoped MatrixGroups

namespace HeckeTM

/-! ### A divisor-sum transform (pure arithmetic) -/

section Arithmetic

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The divisor-sum transform in filter form:
`tsumF k m j c = ∑_{d ∣ m, d ∣ j} d^(k-1) • c (m * j / d²)`.  All reindexing
below happens in this form; `tsumF_eq` transports it to the `gcd`-divisor
shape of the public statements. -/
noncomputable def tsumF (k : ℤ) (m j : ℕ) (c : ℕ → M) : M :=
  ∑ d ∈ (Nat.divisors m).filter (fun d => d ∣ j), ((d : ℂ) ^ (k - 1)) • c (m * j / (d * d))

lemma tsumF_one_left (k : ℤ) (j : ℕ) (c : ℕ → M) : tsumF k 1 j c = c j := by
  have h1 : (Nat.divisors 1).filter (fun d => d ∣ j) = {1} := by
    simp [Nat.divisors_one]
  rw [tsumF, h1, Finset.sum_singleton]
  simp

lemma tsumF_eq (k : ℤ) {m : ℕ} (hm : 0 < m) (j : ℕ) (c : ℕ → M) :
    tsumF k m j c
      = ∑ d ∈ Nat.divisors (Nat.gcd m j), ((d : ℂ) ^ (k - 1)) • c (m * j / (d * d)) := by
  have hg : 0 < Nat.gcd m j := Nat.gcd_pos_of_pos_left j hm
  have hset : (Nat.divisors m).filter (fun d => d ∣ j) = Nat.divisors (Nat.gcd m j) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdvm, -⟩, hdvj⟩
      exact ⟨Nat.dvd_gcd hdvm hdvj, hg.ne'⟩
    · rintro ⟨hdvg, -⟩
      exact ⟨⟨Nat.dvd_trans hdvg (Nat.gcd_dvd_left m j), hm.ne'⟩,
        Nat.dvd_trans hdvg (Nat.gcd_dvd_right m j)⟩
  rw [tsumF, hset]

/-- Split a `ℂ`-scalar weight along `d ↦ p * d`. -/
private lemma weight_split {p : ℕ} (k : ℤ) (d : ℕ) (x : M) :
    (((p * d : ℕ) : ℂ) ^ (k - 1)) • x
      = ((p : ℂ) ^ (k - 1)) • (((d : ℕ) : ℂ) ^ (k - 1)) • x := by
  rw [Nat.cast_mul, mul_zpow, ← smul_smul]

/-- Cancel a factor `p` from the numerator and denominator of an index. -/
private lemma idx_split {p : ℕ} (hp : 0 < p) (m j d : ℕ) :
    m * (p * j) / (p * d * (p * d)) = m * j / (p * d * d) := by
  have h1 : m * (p * j) = p * (m * j) := by ring
  have h2 : p * d * (p * d) = p * (p * d * d) := by ring
  rw [h1, h2, Nat.mul_div_mul_left _ _ hp]

omit [Module ℂ M] in
/-- **Explode the second slot by `p`.**  Divisors of `gcd m (p j)` split into
the `p`-free part of `{d : d ∣ m, d ∣ j}` and the image of `d ↦ p * d` on
`{d : d ∣ m, p * d ∣ m, d ∣ j}`. -/
private lemma sum_mul_p {p : ℕ} (hp : p.Prime) (F : ℕ → M) (m j : ℕ) :
    ∑ d ∈ (Nat.divisors m).filter (fun d => d ∣ p * j), F d
      = ∑ d ∈ ((Nat.divisors m).filter (fun d => d ∣ j)).filter (fun d => ¬ p ∣ d), F d
        + ∑ d ∈ (Nat.divisors m).filter (fun d => p * d ∣ m ∧ d ∣ j), F (p * d) := by
  have hfree : ((Nat.divisors m).filter (fun d => d ∣ p * j)).filter (fun d => ¬ p ∣ d)
      = ((Nat.divisors m).filter (fun d => d ∣ j)).filter (fun d => ¬ p ∣ d) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hdm, hm0⟩, hdj⟩, hnp⟩
      refine ⟨⟨⟨hdm, hm0⟩, ?_⟩, hnp⟩
      have hc : Nat.Coprime d p :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp)
      exact hc.dvd_of_dvd_mul_left hdj
    · rintro ⟨⟨⟨hdm, hm0⟩, hdj⟩, hnp⟩
      exact ⟨⟨⟨hdm, hm0⟩, dvd_mul_of_dvd_right hdj p⟩, hnp⟩
  have hinj : Set.InjOn (fun d : ℕ => p * d)
      (↑((Nat.divisors m).filter (fun d => p * d ∣ m ∧ d ∣ j)) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp.pos hab
  have hpd : ((Nat.divisors m).filter (fun d => d ∣ p * j)).filter (fun d => p ∣ d)
      = ((Nat.divisors m).filter (fun d => p * d ∣ m ∧ d ∣ j)).image (fun d => p * d) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨hdm, hm0⟩, hdj⟩, hpd'⟩
      have hdvd : p * (d / p) = d := Nat.mul_div_cancel' hpd'
      have h1 : p * (d / p) ∣ m := by rw [hdvd]; exact hdm
      have h3 : p * (d / p) ∣ p * j := by rw [hdvd]; exact hdj
      refine ⟨d / p, ⟨⟨Nat.dvd_trans (Nat.dvd_mul_left (d / p) p) h1, hm0⟩, ⟨h1, ?_⟩⟩, hdvd⟩
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos h3
    · rintro ⟨d', ⟨⟨⟨hd'm, hm0⟩, ⟨hpd'm, hd'j⟩⟩, rfl⟩⟩
      exact ⟨⟨⟨hpd'm, hm0⟩, Nat.mul_dvd_mul_left p hd'j⟩, dvd_mul_right p d'⟩
  rw [← Finset.sum_filter_add_sum_filter_not (p := fun d => p ∣ d), hpd,
    Finset.sum_image hinj, hfree]
  abel

omit [Module ℂ M] in
/-- **Explode the first slot by `p`.**  Divisors of `gcd (p m) j` split into
the `p`-free part of `{d : d ∣ m, d ∣ j}` (a `p`-free divisor of `p * m`
divides `m`) and the image of `d ↦ p * d` on `{d : d ∣ m, p * d ∣ j}`. -/
private lemma sum_p_mul {p : ℕ} (hp : p.Prime) (F : ℕ → M) (m j : ℕ) :
    ∑ d ∈ (Nat.divisors (p * m)).filter (fun d => d ∣ j), F d
      = ∑ d ∈ ((Nat.divisors m).filter (fun d => d ∣ j)).filter (fun d => ¬ p ∣ d), F d
        + ∑ d ∈ (Nat.divisors m).filter (fun d => p * d ∣ j), F (p * d) := by
  have hfree : ((Nat.divisors (p * m)).filter (fun d => d ∣ j)).filter (fun d => ¬ p ∣ d)
      = ((Nat.divisors m).filter (fun d => d ∣ j)).filter (fun d => ¬ p ∣ d) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hdpm, hpm0⟩, hdj⟩, hnp⟩
      refine ⟨⟨⟨?_, ?_⟩, hdj⟩, hnp⟩
      · have hc : Nat.Coprime d p :=
          Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp)
        exact hc.dvd_of_dvd_mul_left hdpm
      · intro hc
        exact hpm0 (by rw [hc]; exact Nat.mul_zero p)
    · rintro ⟨⟨⟨hdm, hm0⟩, hdj⟩, hnp⟩
      refine ⟨⟨⟨dvd_mul_of_dvd_right hdm p, ?_⟩, hdj⟩, hnp⟩
      intro hc
      rcases Nat.mul_eq_zero.mp hc with h | h
      · exact absurd h hp.pos.ne'
      · exact hm0 h
  have hinj : Set.InjOn (fun d : ℕ => p * d)
      (↑((Nat.divisors m).filter (fun d => p * d ∣ j)) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp.pos hab
  have hpd : ((Nat.divisors (p * m)).filter (fun d => d ∣ j)).filter (fun d => p ∣ d)
      = ((Nat.divisors m).filter (fun d => p * d ∣ j)).image (fun d => p * d) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨hdpjm, hpm0⟩, hdj⟩, hpd'⟩
      have hdvd : p * (d / p) = d := Nat.mul_div_cancel' hpd'
      have h1 : p * (d / p) ∣ p * m := by rw [hdvd]; exact hdpjm
      have h3 : p * (d / p) ∣ j := by rw [hdvd]; exact hdj
      refine ⟨d / p, ⟨⟨Nat.dvd_of_mul_dvd_mul_left hp.pos h1, ?_⟩, h3⟩, hdvd⟩
      intro hc
      exact hpm0 (by rw [hc]; exact Nat.mul_zero p)
    · rintro ⟨d', ⟨⟨⟨hd'm, hm0⟩, hpd'j⟩, rfl⟩⟩
      refine ⟨⟨⟨Nat.mul_dvd_mul_left p hd'm, ?_⟩, hpd'j⟩, dvd_mul_right p d'⟩
      intro hc
      exact hm0 (Or.resolve_left (Nat.mul_eq_zero.mp hc) hp.pos.ne')
  rw [← Finset.sum_filter_add_sum_filter_not (p := fun d => p ∣ d), hpd,
    Finset.sum_image hinj, hfree]
  abel

/-- Divisors `d` with `p * d ∣ j` are the divisors of `j / p` (when `p ∣ j`). -/
private lemma filter_pd_dvd {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : p ∣ j) (m : ℕ) :
    (Nat.divisors m).filter (fun d => p * d ∣ j)
      = (Nat.divisors m).filter (fun d => d ∣ j / p) := by
  obtain ⟨j', rfl⟩ := hj
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mul_div_cancel_left _ hp.pos]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, Nat.dvd_of_mul_dvd_mul_left hp.pos h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, Nat.mul_dvd_mul_left p h3⟩

/-- Divisors `d` of `m` with `p * d ∣ m` are the divisors of `m / p`
(when `p ∣ m`). -/
private lemma filter_pd_dvd_m {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : p ∣ m) (j : ℕ) :
    (Nat.divisors m).filter (fun d => p * d ∣ m ∧ d ∣ j)
      = (Nat.divisors (m / p)).filter (fun d => d ∣ j) := by
  obtain ⟨m', rfl⟩ := hm
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mul_div_cancel_left _ hp.pos]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    refine ⟨⟨Nat.dvd_of_mul_dvd_mul_left hp.pos h3, ?_⟩, h4⟩
    intro hc
    exact h2 (by rw [hc]; exact Nat.mul_zero p)
  · rintro ⟨⟨h1, h2⟩, h4⟩
    refine ⟨⟨dvd_mul_of_dvd_right h1 p, ?_⟩, ⟨Nat.mul_dvd_mul_left p h1, h4⟩⟩
    intro hc
    exact h2 (Or.resolve_left (Nat.mul_eq_zero.mp hc) hp.pos.ne')

private lemma filter_pd_dvd_m_eq_empty {p m : ℕ} (hpm : ¬ p ∣ m) (j : ℕ) :
    (Nat.divisors m).filter (fun d => p * d ∣ m ∧ d ∣ j) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun d _ hneg => hpm ?_
  exact Nat.dvd_trans (Nat.dvd_mul_right p d) hneg.1

private lemma filter_pd_dvd_eq_empty {p j : ℕ} (hpj : ¬ p ∣ j) (m : ℕ) :
    (Nat.divisors m).filter (fun d => p * d ∣ j) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun d _ hneg => hpj ?_
  exact Nat.dvd_trans (Nat.dvd_mul_right p d) hneg

private lemma idx_left {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : p ∣ j) (m d : ℕ) :
    m * (j / p) / (d * d) = m * j / (p * d * d) := by
  obtain ⟨j', rfl⟩ := hj
  have h2 : m * (p * j') = p * (m * j') := by ring
  have h3 : p * d * d = p * (d * d) := by ring
  rw [Nat.mul_div_cancel_left _ hp.pos, h2, h3, Nat.mul_div_mul_left _ _ hp.pos]

private lemma idx_right {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : p ∣ m) (j d : ℕ) :
    (m / p) * j / (d * d) = m * j / (p * d * d) := by
  obtain ⟨m', rfl⟩ := hm
  have h2 : p * m' * j = p * (m' * j) := by ring
  have h3 : p * d * d = p * (d * d) := by ring
  rw [Nat.mul_div_cancel_left _ hp.pos, h2, h3, Nat.mul_div_mul_left _ _ hp.pos]

/-- **The prime reindexing step** (probe 1, check B at one prime): applying
`T_p` to a sequence in divisor-sum form explodes one `p` from the second slot
at the cost of the correction `p^(k-1) [p ∣ m] tsumF k (m / p)` — the
coefficient-level two-term recursion. -/
lemma tsumF_prime_step {p : ℕ} (hp : p.Prime) (k : ℤ) (m j : ℕ) (c : ℕ → M) :
    tsumF k m (p * j) c + ((p : ℂ) ^ (k - 1)) • (if p ∣ j then tsumF k m (j / p) c else 0)
      = tsumF k (p * m) j c
        + (if p ∣ m then ((p : ℂ) ^ (k - 1)) • tsumF k (m / p) j c else 0) := by
  have e1 : tsumF k m (p * j) c
      = ∑ d ∈ (Nat.divisors m).filter (fun d => d ∣ p * j),
          ((d : ℂ) ^ (k - 1)) • c (m * (p * j) / (d * d)) := rfl
  have e2 : tsumF k (p * m) j c
      = ∑ d ∈ (Nat.divisors (p * m)).filter (fun d => d ∣ j),
          ((d : ℂ) ^ (k - 1)) • c (p * m * j / (d * d)) := rfl
  rw [e1, e2,
    sum_mul_p hp (fun d => ((d : ℂ) ^ (k - 1)) • c (m * (p * j) / (d * d))) m j,
    sum_p_mul hp (fun d => ((d : ℂ) ^ (k - 1)) • c (p * m * j / (d * d))) m j]
  have hfree : ∑ d ∈ ((Nat.divisors m).filter (fun d => d ∣ j)).filter (fun d => ¬ p ∣ d),
        ((d : ℂ) ^ (k - 1)) • c (m * (p * j) / (d * d))
      = ∑ d ∈ ((Nat.divisors m).filter (fun d => d ∣ j)).filter (fun d => ¬ p ∣ d),
        ((d : ℂ) ^ (k - 1)) • c (p * m * j / (d * d)) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    have hmul : m * (p * j) = p * m * j := by ring
    rw [hmul]
  rw [hfree]
  have hs1 : ∑ d ∈ (Nat.divisors m).filter (fun d => p * d ∣ m ∧ d ∣ j),
        (((p * d : ℕ) : ℂ) ^ (k - 1)) • c (m * (p * j) / (p * d * (p * d)))
      = ((p : ℂ) ^ (k - 1)) • ∑ d ∈ (Nat.divisors m).filter (fun d => p * d ∣ m ∧ d ∣ j),
        ((d : ℂ) ^ (k - 1)) • c (m * j / (p * d * d)) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun d _ => by rw [weight_split, idx_split hp.pos]
  have hs2 : ∑ d ∈ (Nat.divisors m).filter (fun d => p * d ∣ j),
        (((p * d : ℕ) : ℂ) ^ (k - 1)) • c (p * m * j / (p * d * (p * d)))
      = ((p : ℂ) ^ (k - 1)) • ∑ d ∈ (Nat.divisors m).filter (fun d => p * d ∣ j),
        ((d : ℂ) ^ (k - 1)) • c (m * j / (p * d * d)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hidx : p * m * j / (p * d * (p * d)) = m * j / (p * d * d) := by
      have hmj : p * m * j = m * (p * j) := by ring
      rw [hmj]
      exact idx_split hp.pos m j d
    rw [weight_split, hidx]
  rw [hs1, hs2]
  by_cases hj : p ∣ j
  · have hL : tsumF k m (j / p) c = ∑ d ∈ (Nat.divisors m).filter (fun d => d ∣ j / p),
          ((d : ℂ) ^ (k - 1)) • c (m * j / (p * d * d)) := by
      rw [tsumF]
      exact Finset.sum_congr rfl fun d _ => by rw [idx_left hp hj]
    by_cases hm : p ∣ m
    · have hR : tsumF k (m / p) j c = ∑ d ∈ (Nat.divisors (m / p)).filter (fun d => d ∣ j),
              ((d : ℂ) ^ (k - 1)) • c (m * j / (p * d * d)) := by
        rw [tsumF]
        exact Finset.sum_congr rfl fun d _ => by rw [idx_right hp hm]
      rw [ite_eq_left hj, ite_eq_left hm, hL, hR, ← filter_pd_dvd hp hj, filter_pd_dvd_m hp hm]
      abel
    · rw [ite_eq_left hj, ite_eq_right hm, filter_pd_dvd_m_eq_empty hm, Finset.sum_empty, hL,
        ← filter_pd_dvd hp hj]
      simp
  · by_cases hm : p ∣ m
    · have hR : tsumF k (m / p) j c = ∑ d ∈ (Nat.divisors (m / p)).filter (fun d => d ∣ j),
              ((d : ℂ) ^ (k - 1)) • c (m * j / (p * d * d)) := by
        rw [tsumF]
        exact Finset.sum_congr rfl fun d _ => by rw [idx_right hp hm]
      rw [ite_eq_right hj, ite_eq_left hm, filter_pd_dvd_eq_empty hj, Finset.sum_empty, hR,
        filter_pd_dvd_m hp hm]
      simp
    · rw [ite_eq_right hj, ite_eq_right hm, filter_pd_dvd_m_eq_empty hm, filter_pd_dvd_eq_empty hj,
        Finset.sum_empty]
      simp

end Arithmetic

/-! ### Coefficient helpers -/

section Coeff

variable {k : ℤ}

/-- Bridge between the folded coercion form and `qL` (both sides are
definitionally `qExpansion 1 ⇑X`). -/
private lemma qExpansion_eq_qL (X : CuspForm 𝒮ℒ k) :
    qExpansion 1 ((⇑X : ℍ → ℂ)) = qL k X := (qL_apply X).symm

/-- `qL` respects differences. -/
private lemma qL_sub (f g : CuspForm 𝒮ℒ k) : qL k (f - g) = qL k f - qL k g := by
  have h : qL k (f - g) + qL k g = qL k f := by
    rw [← map_add, sub_add_cancel]
  exact eq_sub_of_add_eq h

/-- `qL` respects scalar multiples. -/
private lemma qL_smul (c : ℂ) (f : CuspForm 𝒮ℒ k) : qL k (c • f) = c • qL k f := by
  rw [qL_apply, qL_apply, qe_smul]

private lemma ps_coeff_sub (F G : PowerSeries ℂ) (n : ℕ) :
    (F - G).coeff n = F.coeff n - G.coeff n := by simp

private lemma ps_coeff_smul (c : ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    (c • F).coeff n = c * F.coeff n := by simp

end Coeff

/-! ### The recursive definition of `T_m` -/

/-- **The Hecke operator `T_m` on level-one cusp forms** (`m ≥ 1`; `T_0 = 0`
by convention, unused).  `T₁ = id`; for `m ≥ 2`, writing `p = m.minFac` and
`n = m / p`, `T_m = T_p ∘ T_n − p^(k-1) • [p ∣ n] T_{n/p}` — the two-term
recursion at the least prime factor, so every `T_m` is a ℂ-linear combination
of compositions of the landed prime operators `heckeTP`. -/
noncomputable def heckeTM (k : ℤ) : ℕ → CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k
  | 0 => 0
  | 1 => LinearMap.id
  | m + 2 =>
      heckeTPₗ k (Nat.minFac_prime (show m + 2 ≠ 1 by omega))
        ∘ₗ heckeTM k ((m + 2) / (m + 2).minFac)
        - ((m + 2).minFac : ℂ) ^ (k - 1) •
          (if (m + 2).minFac ∣ (m + 2) / (m + 2).minFac then
            heckeTM k ((m + 2) / (m + 2).minFac / (m + 2).minFac) else 0)
  termination_by m => m
  decreasing_by
    · exact Nat.div_lt_self (by omega) (Nat.minFac_prime (show m + 2 ≠ 1 by omega)).one_lt
    · exact Nat.lt_of_le_of_lt
        (Nat.div_le_self ((m + 2) / (m + 2).minFac) (m + 2).minFac)
        (Nat.div_lt_self (by omega) (Nat.minFac_prime (show m + 2 ≠ 1 by omega)).one_lt)

lemma heckeTM_zero (k : ℤ) : heckeTM k 0 = 0 := by rw [heckeTM]

lemma heckeTM_id (k : ℤ) : heckeTM k 1 = LinearMap.id := by rw [heckeTM]

lemma heckeTM_add_two (k : ℤ) (m : ℕ) :
    heckeTM k (m + 2) =
      heckeTPₗ k (Nat.minFac_prime (show m + 2 ≠ 1 by omega))
        ∘ₗ heckeTM k ((m + 2) / (m + 2).minFac)
        - ((m + 2).minFac : ℂ) ^ (k - 1) •
          (if (m + 2).minFac ∣ (m + 2) / (m + 2).minFac then
            heckeTM k ((m + 2) / (m + 2).minFac / (m + 2).minFac) else 0) := by
  rw [heckeTM]

lemma heckeTM_ge_two (k : ℤ) {m : ℕ} (hm : 2 ≤ m) :
    heckeTM k m =
      heckeTPₗ k (Nat.minFac_prime (show m ≠ 1 by omega)) ∘ₗ heckeTM k (m / m.minFac)
        - ((m.minFac : ℂ) ^ (k - 1)) •
          (if m.minFac ∣ m / m.minFac then heckeTM k (m / m.minFac / m.minFac) else 0) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  exact heckeTM_add_two k m'

/-- Pointwise form of the defining recursion, `m ≥ 2`. -/
lemma heckeTM_apply_ge_two {k : ℤ} {m : ℕ} (hm : 2 ≤ m) (f : CuspForm 𝒮ℒ k) :
    heckeTM k m f =
      heckeTP (Nat.minFac_prime (show m ≠ 1 by omega)) (heckeTM k (m / m.minFac) f)
        - (if m.minFac ∣ m / m.minFac then
            ((m.minFac : ℂ) ^ (k - 1)) • heckeTM k (m / m.minFac / m.minFac) f else 0) := by
  rw [heckeTM_ge_two k hm]
  by_cases h : m.minFac ∣ m / m.minFac
  · rw [ite_eq_left h, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      ite_eq_left h]
    rfl
  · rw [ite_eq_right h, LinearMap.sub_apply, LinearMap.comp_apply, smul_zero,
      LinearMap.zero_apply, ite_eq_right h]
    rfl

/-! ### The coefficient formula -/

section CoeffFormula

variable {k : ℤ}

/-- **Coefficient formula for `T_m`** (divisor-sum form): for `m ≥ 1`, the
`n`-th q-coefficient of `T_m f` is `∑_{d ∣ m, d ∣ n} d^(k-1) • f_{m n / d²}`.
Strong induction on `m`; the step is `tsumF_prime_step`. -/
theorem heckeTM_coeff_tsumF (f : CuspForm 𝒮ℒ k) :
    ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ,
      (qExpansion 1 (heckeTM k m f)).coeff n
        = tsumF k m n (fun i => (qExpansion 1 f).coeff i) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm n
    rcases m with _ | m1
    · exact absurd hm (by omega)
    rcases m1 with _ | m'
    · -- `m = 1`: `T₁ = id`, and `tsumF k 1 n c = c n`
      simp [heckeTM_id, LinearMap.id_apply, tsumF_one_left]
    · -- `m = m' + 2 ≥ 2`: unfold at the least prime factor
      have hmp : (m' + 2).minFac.Prime := Nat.minFac_prime (by omega)
      have h2p : 2 ≤ (m' + 2).minFac := hmp.one_lt
      have hdvd : (m' + 2).minFac ∣ m' + 2 := Nat.minFac_dvd (m' + 2)
      have hmeq : (m' + 2).minFac * ((m' + 2) / (m' + 2).minFac) = m' + 2 :=
        Nat.mul_div_cancel' hdvd
      have hn1 : 1 ≤ (m' + 2) / (m' + 2).minFac :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hmp.pos
      have hnlt : (m' + 2) / (m' + 2).minFac < m' + 2 := Nat.div_lt_self (by omega) h2p
      rw [heckeTM_apply_ge_two (by omega) f, qExpansion_eq_qL, qL_sub]
      by_cases hmid : (m' + 2).minFac ∣ (m' + 2) / (m' + 2).minFac
      · -- correction present
        have hc1 : 1 ≤ (m' + 2) / (m' + 2).minFac / (m' + 2).minFac := by
          obtain ⟨t, ht⟩ := hmid
          have hz : (m' + 2) / (m' + 2).minFac = (m' + 2).minFac * t := ht
          have htt : (m' + 2) / (m' + 2).minFac / (m' + 2).minFac = t := by
            rw [hz, Nat.mul_div_cancel_left _ hmp.pos]
          rcases Nat.eq_zero_or_pos t with h0 | hpos
          · rw [h0, Nat.mul_zero] at hz
            exact absurd hn1 (by rw [hz]; omega)
          · rw [htt]; exact hpos
        have hclt : (m' + 2) / (m' + 2).minFac / (m' + 2).minFac < m' + 2 :=
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnlt
        simp only [hmid, ite_true, qL_smul, ps_coeff_sub, ps_coeff_smul]
        rw [qL_apply (heckeTP hmp (heckeTM k ((m' + 2) / (m' + 2).minFac) f)),
          heckeTP_qExpansion_coeff hmp,
          ih _ hnlt hn1, ih _ hnlt hn1,
          qL_apply (heckeTM k ((m' + 2) / (m' + 2).minFac / (m' + 2).minFac) f),
          ih _ hclt hc1]
        have key := tsumF_prime_step hmp k ((m' + 2) / (m' + 2).minFac) n
          (fun i => (qExpansion 1 f).coeff i)
        rw [hmeq] at key
        by_cases hpn : (m' + 2).minFac ∣ n
        · simp only [hpn, ite_true, hmid, ite_true] at key ⊢
          simp only [smul_eq_mul] at key ⊢
          linear_combination key
        · simp only [hpn, ite_false, hmid, ite_true] at key ⊢
          simp only [smul_eq_mul, mul_zero] at key ⊢
          linear_combination key
      · -- no correction
        simp only [hmid, ite_false, map_zero, sub_zero]
        rw [qL_apply (heckeTP hmp (heckeTM k ((m' + 2) / (m' + 2).minFac) f)),
          heckeTP_qExpansion_coeff hmp, ih _ hnlt hn1, ih _ hnlt hn1]
        have key := tsumF_prime_step hmp k ((m' + 2) / (m' + 2).minFac) n
          (fun i => (qExpansion 1 f).coeff i)
        rw [hmeq] at key
        by_cases hpn : (m' + 2).minFac ∣ n
        · simp only [hpn, ite_true, hmid, ite_false] at key ⊢
          simp only [smul_eq_mul] at key ⊢
          linear_combination key
        · simp only [hpn, ite_false, hmid, ite_false] at key ⊢
          simp only [smul_eq_mul, mul_zero] at key ⊢
          linear_combination key

/-- **Coefficient formula for `T_m`**: for `m ≥ 1`,
`(T_m f)_n = ∑_{d ∣ gcd m n} d^(k-1) • f_{m n / d²}`. -/
theorem heckeTM_qExpansion_coeff (f : CuspForm 𝒮ℒ k) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    (qExpansion 1 (heckeTM k m f)).coeff n
      = ∑ d ∈ Nat.divisors (Nat.gcd m n),
          ((d : ℂ) ^ (k - 1)) * (qExpansion 1 f).coeff (m * n / (d * d)) := by
  rw [heckeTM_coeff_tsumF f m hm n,
    tsumF_eq k (Nat.pos_of_ne_zero (fun h => by omega)) n (fun i => (qExpansion 1 f).coeff i)]
  exact Finset.sum_congr rfl fun d _ => by rw [smul_eq_mul]

/-- **Duality ingredient**: the first coefficient of `T_m f` is the `m`-th
coefficient of `f` — `a₁(T_m f) = a_m f`. -/
theorem heckeTM_one (f : CuspForm 𝒮ℒ k) {m : ℕ} (hm : 1 ≤ m) :
    (qExpansion 1 (heckeTM k m f)).coeff 1 = (qExpansion 1 f).coeff m := by
  rw [heckeTM_qExpansion_coeff f hm 1]
  simp [Nat.gcd_one_right, Nat.divisors_one, one_zpow]

end CoeffFormula

/-! ### Prime and prime-power specializations -/

section PrimeSpec

variable {k : ℤ}

/-- The least prime factor of a prime is itself. -/
private lemma minFac_eq {p : ℕ} (hp : p.Prime) : p.minFac = p := by
  rcases (Nat.dvd_prime hp).mp (Nat.minFac_dvd p) with h1 | h2
  · exact absurd h1 (by have := (Nat.minFac_prime (show p ≠ 1 from hp.ne_one)).one_lt; omega)
  · exact h2

/-- The least prime factor of `p ^ s` (`s ≥ 2`) is `p`. -/
private lemma minFac_prime_pow {p : ℕ} (hp : p.Prime) {s : ℕ} (hs : 2 ≤ s) :
    (p ^ s).minFac = p := by
  have hp1 : p ^ s ≠ 1 := by
    have h2 : 2 ≤ p * p := by nlinarith [hp.one_lt]
    have hle : p ^ 2 ≤ p ^ s := Nat.pow_le_pow_right hp.pos hs
    have h3 : p * p = p ^ 2 := by ring
    omega
  have hpf : (p ^ s).minFac.Prime := Nat.minFac_prime hp1
  have hdvdp : (p ^ s).minFac ∣ p := hpf.dvd_of_dvd_pow (Nat.minFac_dvd (p ^ s))
  rcases (Nat.dvd_prime hp).mp hdvdp with h1 | h2
  · exact absurd h1 hpf.ne_one
  · exact h2

/-- **Prime specialization**: `T_p` is the landed `heckeTP` (as a linear map),
so the general coefficient formula reduces to the landed
`heckeTP_qExpansion_coeff` by a one-line rewrite. -/
lemma heckeTM_prime (k : ℤ) {p : ℕ} (hp : p.Prime) : heckeTM k p = heckeTPₗ k hp := by
  have hn1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.eq_one_of_dvd_one h)
  rw [heckeTM_ge_two k hp.one_lt]
  simp only [minFac_eq hp, Nat.div_self hp.pos, heckeTM_id, LinearMap.comp_id, ite_eq_right hn1,
    smul_zero, sub_zero]

/-- The coefficient formula at a prime index is the landed
`heckeTP_qExpansion_coeff`. -/
theorem heckeTM_qExpansion_coeff_prime {p : ℕ} (hp : p.Prime) (f : CuspForm 𝒮ℒ k) (n : ℕ) :
    (qExpansion 1 (heckeTM k p f)).coeff n
      = (qExpansion 1 f).coeff (p * n)
        + (p : ℂ) ^ (k - 1) * (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0) := by
  rw [heckeTM_prime k hp]
  exact heckeTP_qExpansion_coeff hp f n

/-- The general unfold at an explicit prime factor `q = m.minFac` of `m ≥ 2`,
for prime-power bookkeeping. -/
lemma heckeTM_ge_two' (k : ℤ) {m q : ℕ} (hm : 2 ≤ m) (hq : q.Prime) (hqm : q = m.minFac) :
    heckeTM k m = heckeTPₗ k hq ∘ₗ heckeTM k (m / q)
      - ((q : ℂ) ^ (k - 1)) • (if q ∣ m / q then heckeTM k (m / q / q) else 0) := by
  subst hqm
  exact heckeTM_ge_two k hm

/-- **The prime-power two-term recursion**: for `r ≥ 0`,
`T_{p^(r+2)} = T_p ∘ T_{p^(r+1)} − p^(k-1) T_{p^r}`. -/
theorem heckeTM_prime_pow_succ (k : ℤ) {p : ℕ} (hp : p.Prime) (r : ℕ) :
    heckeTM k (p ^ (r + 2)) = heckeTPₗ k hp ∘ₗ heckeTM k (p ^ (r + 1))
      - ((p : ℂ) ^ (k - 1)) • heckeTM k (p ^ r) := by
  have hp2 : 2 ≤ p ^ (r + 2) := by
    have h4 : 2 ≤ p * p := by nlinarith [hp.one_lt]
    have hle : p ^ 2 ≤ p ^ (r + 2) := Nat.pow_le_pow_right hp.pos (by omega)
    have h3 : p * p = p ^ 2 := by ring
    omega
  have hd1 : p ^ (r + 2) / p = p ^ (r + 1) := by
    rw [pow_succ, Nat.mul_comm (p ^ (r + 1)) p, Nat.mul_div_cancel_left _ hp.pos]
  have hd2 : p ^ (r + 1) / p = p ^ r := by
    rw [pow_succ, Nat.mul_comm (p ^ r) p, Nat.mul_div_cancel_left _ hp.pos]
  have hpd : p ∣ p ^ (r + 1) := ⟨p ^ r, by rw [pow_succ, Nat.mul_comm]⟩
  rw [heckeTM_ge_two' k hp2 hp (minFac_prime_pow hp (by omega)).symm, hd1, hd2]
  simp only [hpd, ite_true]

end PrimeSpec

end HeckeTM
