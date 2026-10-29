import MathProof.ModularForms.MaedaLevelOne

/-!
# Maeda's conjecture for the level-one weights with `dim S_k ∈ {2, 3}`

Instances of `MathProof/ModularForms/MaedaLevelOne.lean`, generated from the
numerical data (`tools/gen_maeda.py`): for each weight the triangular basis
`Δ^i E₄^a E₆^b`, its first q-coefficients (kernel-computed), the matrix of `T₂`
(from `charpoly_dim2` / `charpoly_dim3`), the characteristic polynomial and its
irreducibility over `ℚ` (no root modulo a small prime).
-/

open UpperHalfPlane ModularForm CuspForm Polynomial MaedaLevelOne
open scoped MatrixGroups

/-! ### Weight 28 (dim 2) -/

namespace MaedaWeight28

/-- `Δ^1 E₄^4 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((28 : ℕ) : ℤ) :=
  prodForm _ 0 4 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 4 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 4 0 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (936 : ℂ) := by
  rw [c1, show seqP 0 4 0 2 = 936 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (53282368 : ℂ) := by
  rw [c1, show seqP 0 4 0 4 = 53282368 by decide +kernel]; norm_num

/-- `Δ^2 E₄^1 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((28 : ℕ) : ℤ) :=
  prodForm _ 1 1 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 1 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 1 0 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 1 0 2 = 1 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (-8280 : ℂ) := by
  rw [c2, show seqP 1 1 0 4 = -8280 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((28 : ℕ) : ℤ)) = 2 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 16 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_28`. -/
noncomputable def T2 := heckeTPₗ ((28 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (936 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (187500096 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (-8280 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

/-- The integer characteristic polynomial of `T₂` on `S_28`. -/
noncomputable def P : ℤ[X] :=
  X ^ 2 + C (8280) * X + C (-195250176)

/-- **The characteristic polynomial of `T₂` on `S_28`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim2 finrank_eq f1 f2 q1_1 q1_2 q2_1 q2_2 T2
    t1_1 t1_2 t2_1 t2_2, Matrix.charpoly_fin_two]
  simp [P, Matrix.trace_fin_two, Matrix.det_fin_two, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 29 →
    ((x : ℤ) ^ 2 + (8280) * (x : ℤ) + (-195250176)) % 29 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 29,
    x ^ 2 + (8280) * x + (-195250176) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 28**: the characteristic polynomial of `T₂`
on `S_28(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 29). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 29 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 2 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight28

/-! ### Weight 30 (dim 2) -/

namespace MaedaWeight30

/-- `Δ^1 E₄^3 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((30 : ℕ) : ℤ) :=
  prodForm _ 0 3 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 3 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 3 1 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (192 : ℂ) := by
  rw [c1, show seqP 0 3 1 2 = 192 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (-80642048 : ℂ) := by
  rw [c1, show seqP 0 3 1 4 = -80642048 by decide +kernel]; norm_num

/-- `Δ^2 E₄^0 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((30 : ℕ) : ℤ) :=
  prodForm _ 1 0 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 0 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 0 1 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 0 1 2 = 1 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (8640 : ℂ) := by
  rw [c2, show seqP 1 0 1 4 = 8640 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((30 : ℕ) : ℤ)) = 2 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 18 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_30`. -/
noncomputable def T2 := heckeTPₗ ((30 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (192 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (456228864 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (8640 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

/-- The integer characteristic polynomial of `T₂` on `S_30`. -/
noncomputable def P : ℤ[X] :=
  X ^ 2 + C (-8640) * X + C (-454569984)

/-- **The characteristic polynomial of `T₂` on `S_30`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim2 finrank_eq f1 f2 q1_1 q1_2 q2_1 q2_2 T2
    t1_1 t1_2 t2_1 t2_2, Matrix.charpoly_fin_two]
  simp [P, Matrix.trace_fin_two, Matrix.det_fin_two, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 29 →
    ((x : ℤ) ^ 2 + (-8640) * (x : ℤ) + (-454569984)) % 29 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 29,
    x ^ 2 + (-8640) * x + (-454569984) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 30**: the characteristic polynomial of `T₂`
on `S_30(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 29). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 29 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 2 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight30

/-! ### Weight 32 (dim 2) -/

namespace MaedaWeight32

/-- `Δ^1 E₄^5 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((32 : ℕ) : ℤ) :=
  prodForm _ 0 5 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 5 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 5 0 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (1176 : ℂ) := by
  rw [c1, show seqP 0 5 0 2 = 1176 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (134859328 : ℂ) := by
  rw [c1, show seqP 0 5 0 4 = 134859328 by decide +kernel]; norm_num

/-- `Δ^2 E₄^2 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((32 : ℕ) : ℤ) :=
  prodForm _ 1 2 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 2 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 2 0 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 2 0 2 = 1 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (39960 : ℂ) := by
  rw [c2, show seqP 1 2 0 4 = 39960 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((32 : ℕ) : ℤ)) = 2 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 20 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_32`. -/
noncomputable def T2 := heckeTPₗ ((32 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (1176 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (2282342976 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (39960 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

/-- The integer characteristic polynomial of `T₂` on `S_32`. -/
noncomputable def P : ℤ[X] :=
  X ^ 2 + C (-39960) * X + C (-2235350016)

/-- **The characteristic polynomial of `T₂` on `S_32`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim2 finrank_eq f1 f2 q1_1 q1_2 q2_1 q2_2 T2
    t1_1 t1_2 t2_1 t2_2, Matrix.charpoly_fin_two]
  simp [P, Matrix.trace_fin_two, Matrix.det_fin_two, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 29 →
    ((x : ℤ) ^ 2 + (-39960) * (x : ℤ) + (-2235350016)) % 29 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 29,
    x ^ 2 + (-39960) * x + (-2235350016) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 32**: the characteristic polynomial of `T₂`
on `S_32(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 29). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 29 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 2 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight32

/-! ### Weight 34 (dim 2) -/

namespace MaedaWeight34

/-- `Δ^1 E₄^4 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((34 : ℕ) : ℤ) :=
  prodForm _ 0 4 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 4 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 4 1 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (432 : ℂ) := by
  rw [c1, show seqP 0 4 1 2 = 432 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (-129459968 : ℂ) := by
  rw [c1, show seqP 0 4 1 4 = -129459968 by decide +kernel]; norm_num

/-- `Δ^2 E₄^1 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((34 : ℕ) : ℤ) :=
  prodForm _ 1 1 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 1 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 1 1 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 1 1 2 = 1 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (-121680 : ℂ) := by
  rw [c2, show seqP 1 1 1 4 = -121680 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((34 : ℕ) : ℤ)) = 2 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 22 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_34`. -/
noncomputable def T2 := heckeTPₗ ((34 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (432 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (8460474624 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (-121680 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

/-- The integer characteristic polynomial of `T₂` on `S_34`. -/
noncomputable def P : ℤ[X] :=
  X ^ 2 + C (121680) * X + C (-8513040384)

/-- **The characteristic polynomial of `T₂` on `S_34`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim2 finrank_eq f1 f2 q1_1 q1_2 q2_1 q2_2 T2
    t1_1 t1_2 t2_1 t2_2, Matrix.charpoly_fin_two]
  simp [P, Matrix.trace_fin_two, Matrix.det_fin_two, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 31 →
    ((x : ℤ) ^ 2 + (121680) * (x : ℤ) + (-8513040384)) % 31 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 31,
    x ^ 2 + (121680) * x + (-8513040384) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 34**: the characteristic polynomial of `T₂`
on `S_34(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 31). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 31 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 2 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight34

/-! ### Weight 38 (dim 2) -/

namespace MaedaWeight38

/-- `Δ^1 E₄^5 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((38 : ℕ) : ℤ) :=
  prodForm _ 0 5 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 5 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 5 1 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (672 : ℂ) := by
  rw [c1, show seqP 0 5 1 2 = 672 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (-166181888 : ℂ) := by
  rw [c1, show seqP 0 5 1 4 = -166181888 by decide +kernel]; norm_num

/-- `Δ^2 E₄^2 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((38 : ℕ) : ℤ) :=
  prodForm _ 1 2 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 2 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 2 1 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 2 1 2 = 1 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (-194400 : ℂ) := by
  rw [c2, show seqP 1 2 1 4 = -194400 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((38 : ℕ) : ℤ)) = 2 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 26 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_38`. -/
noncomputable def T2 := heckeTPₗ ((38 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (672 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (137272771584 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (-194400 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

/-- The integer characteristic polynomial of `T₂` on `S_38`. -/
noncomputable def P : ℤ[X] :=
  X ^ 2 + C (194400) * X + C (-137403408384)

/-- **The characteristic polynomial of `T₂` on `S_38`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim2 finrank_eq f1 f2 q1_1 q1_2 q2_1 q2_2 T2
    t1_1 t1_2 t2_1 t2_2, Matrix.charpoly_fin_two]
  simp [P, Matrix.trace_fin_two, Matrix.det_fin_two, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 41 →
    ((x : ℤ) ^ 2 + (194400) * (x : ℤ) + (-137403408384)) % 41 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 41,
    x ^ 2 + (194400) * x + (-137403408384) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 38**: the characteristic polynomial of `T₂`
on `S_38(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 41). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 41 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 2 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight38

/-! ### Weight 36 (dim 3) -/

namespace MaedaWeight36

/-- `Δ^1 E₄^6 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((36 : ℕ) : ℤ) :=
  prodForm _ 0 6 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 6 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 6 0 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (1416 : ℂ) := by
  rw [c1, show seqP 0 6 0 2 = 1416 by decide +kernel]; norm_num

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (842652 : ℂ) := by
  rw [c1, show seqP 0 6 0 3 = 842652 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (271386688 : ℂ) := by
  rw [c1, show seqP 0 6 0 4 = 271386688 by decide +kernel]; norm_num

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (5356057835232 : ℂ) := by
  rw [c1, show seqP 0 6 0 6 = 5356057835232 by decide +kernel]; norm_num

/-- `Δ^2 E₄^3 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((36 : ℕ) : ℤ) :=
  prodForm _ 1 3 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 3 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 3 0 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 3 0 2 = 1 by decide +kernel]; norm_num

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (672 : ℂ) := by
  rw [c2, show seqP 1 3 0 3 = 672 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (145800 : ℂ) := by
  rw [c2, show seqP 1 3 0 4 = 145800 by decide +kernel]; norm_num

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-233907300 : ℂ) := by
  rw [c2, show seqP 1 3 0 6 = -233907300 by decide +kernel]; norm_num

/-- `Δ^3 E₄^0 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((36 : ℕ) : ℤ) :=
  prodForm _ 2 0 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 0 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, show seqP 2 0 0 1 = 0 by decide +kernel]; norm_num

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, show seqP 2 0 0 2 = 0 by decide +kernel]; norm_num

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, show seqP 2 0 0 3 = 1 by decide +kernel]; norm_num

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (-72 : ℂ) := by
  rw [c3, show seqP 2 0 0 4 = -72 by decide +kernel]; norm_num

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-54528 : ℂ) := by
  rw [c3, show seqP 2 0 0 6 = -54528 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((36 : ℕ) : ℤ)) = 3 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 24 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_36`. -/
noncomputable def T2 := heckeTPₗ ((36 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (1416 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (34631125056 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (5356057835232 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (145800 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-233907300 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (-72 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-54528 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

/-- The integer characteristic polynomial of `T₂` on `S_36`. -/
noncomputable def P : ℤ[X] :=
  X ^ 3 + C (-139656) * X ^ 2 + C (-59208339456) * X + C (-1467625047588864)

/-- **The characteristic polynomial of `T₂` on `S_36`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim3 finrank_eq f1 f2 f3 q1_1 q1_2 q1_3 q2_1 q2_2 q2_3 q3_1 q3_2 q3_3 T2
    t1_1 t1_2 t1_3 t2_1 t2_2 t2_3 t3_1 t3_2 t3_3, charpoly_fin_three]
  simp [P, Matrix.det_fin_three, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 37 →
    ((x : ℤ) ^ 3 + (-139656) * (x : ℤ) ^ 2 + (-59208339456) * (x : ℤ) + (-1467625047588864)) % 37
      ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 37,
    x ^ 3 + (-139656) * x ^ 2 + (-59208339456) * x + (-1467625047588864) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 36**: the characteristic polynomial of `T₂`
on `S_36(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 37). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 37 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 3 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight36

/-! ### Weight 40 (dim 3) -/

namespace MaedaWeight40

/-- `Δ^1 E₄^7 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((40 : ℕ) : ℤ) :=
  prodForm _ 0 7 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 7 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 7 0 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (1656 : ℂ) := by
  rw [c1, show seqP 0 7 0 2 = 1656 by decide +kernel]; norm_num

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (1184652 : ℂ) := by
  rw [c1, show seqP 0 7 0 3 = 1184652 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (476688448 : ℂ) := by
  rw [c1, show seqP 0 7 0 4 = 476688448 by decide +kernel]; norm_num

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (18082094903712 : ℂ) := by
  rw [c1, show seqP 0 7 0 6 = 18082094903712 by decide +kernel]; norm_num

/-- `Δ^2 E₄^4 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((40 : ℕ) : ℤ) :=
  prodForm _ 1 4 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 4 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 4 0 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 4 0 2 = 1 by decide +kernel]; norm_num

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (912 : ℂ) := by
  rw [c2, show seqP 1 4 0 3 = 912 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (309240 : ℂ) := by
  rw [c2, show seqP 1 4 0 4 = 309240 by decide +kernel]; norm_num

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (2272357260 : ℂ) := by
  rw [c2, show seqP 1 4 0 6 = 2272357260 by decide +kernel]; norm_num

/-- `Δ^3 E₄^1 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((40 : ℕ) : ℤ) :=
  prodForm _ 2 1 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 1 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, show seqP 2 1 0 1 = 0 by decide +kernel]; norm_num

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, show seqP 2 1 0 2 = 0 by decide +kernel]; norm_num

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, show seqP 2 1 0 3 = 1 by decide +kernel]; norm_num

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (168 : ℂ) := by
  rw [c3, show seqP 2 1 0 4 = 168 by decide +kernel]; norm_num

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (392832 : ℂ) := by
  rw [c3, show seqP 2 1 0 6 = 392832 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((40 : ℕ) : ℤ)) = 3 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 28 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_40`. -/
noncomputable def T2 := heckeTPₗ ((40 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (1656 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (550232502336 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (18082094903712 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (309240 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (2272357260 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (168 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (392832 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

/-- The integer characteristic polynomial of `T₂` on `S_40`. -/
noncomputable def P : ℤ[X] :=
  X ^ 3 + C (-548856) * X ^ 2 + C (-810051757056) * X + C (213542160549543936)

/-- **The characteristic polynomial of `T₂` on `S_40`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim3 finrank_eq f1 f2 f3 q1_1 q1_2 q1_3 q2_1 q2_2 q2_3 q3_1 q3_2 q3_3 T2
    t1_1 t1_2 t1_3 t2_1 t2_2 t2_3 t3_1 t3_2 t3_3, charpoly_fin_three]
  simp [P, Matrix.det_fin_three, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 37 →
    ((x : ℤ) ^ 3 + (-548856) * (x : ℤ) ^ 2 + (-810051757056) * (x : ℤ) + (213542160549543936)) %
      37 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 37,
    x ^ 3 + (-548856) * x ^ 2 + (-810051757056) * x + (213542160549543936) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 40**: the characteristic polynomial of `T₂`
on `S_40(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 37). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 37 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 3 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight40

/-! ### Weight 42 (dim 3) -/

namespace MaedaWeight42

/-- `Δ^1 E₄^6 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((42 : ℕ) : ℤ) :=
  prodForm _ 0 6 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 6 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 6 1 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (912 : ℂ) := by
  rw [c1, show seqP 0 6 1 2 = 912 by decide +kernel]; norm_num

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (112356 : ℂ) := by
  rw [c1, show seqP 0 6 1 3 = 112356 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (-176983808 : ℂ) := by
  rw [c1, show seqP 0 6 1 4 = -176983808 by decide +kernel]; norm_num

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-24743751611328 : ℂ) := by
  rw [c1, show seqP 0 6 1 6 = -24743751611328 by decide +kernel]; norm_num

/-- `Δ^2 E₄^3 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((42 : ℕ) : ℤ) :=
  prodForm _ 1 3 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 3 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 3 1 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 3 1 2 = 1 by decide +kernel]; norm_num

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (168 : ℂ) := by
  rw [c2, show seqP 1 3 1 3 = 168 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (-209520 : ℂ) := by
  rw [c2, show seqP 1 3 1 4 = -209520 by decide +kernel]; norm_num

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-7334312220 : ℂ) := by
  rw [c2, show seqP 1 3 1 6 = -7334312220 by decide +kernel]; norm_num

/-- `Δ^3 E₄^0 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((42 : ℕ) : ℤ) :=
  prodForm _ 2 0 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 0 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, show seqP 2 0 1 1 = 0 by decide +kernel]; norm_num

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, show seqP 2 0 1 2 = 0 by decide +kernel]; norm_num

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, show seqP 2 0 1 3 = 1 by decide +kernel]; norm_num

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (-576 : ℂ) := by
  rw [c3, show seqP 2 0 1 4 = -576 by decide +kernel]; norm_num

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-231936 : ℂ) := by
  rw [c3, show seqP 2 0 1 6 = -231936 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((42 : ℕ) : ℤ)) = 3 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 30 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_42`. -/
noncomputable def T2 := heckeTPₗ ((42 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (912 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (2198846271744 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-24743751611328 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (-209520 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-7334312220 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (-576 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-231936 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

/-- The integer characteristic polynomial of `T₂` on `S_42`. -/
noncomputable def P : ℤ[X] :=
  X ^ 3 + C (344688) * X ^ 2 + C (-6374982426624) * X + C (-520435526440845312)

/-- **The characteristic polynomial of `T₂` on `S_42`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim3 finrank_eq f1 f2 f3 q1_1 q1_2 q1_3 q2_1 q2_2 q2_3 q3_1 q3_2 q3_3 T2
    t1_1 t1_2 t1_3 t2_1 t2_2 t2_3 t3_1 t3_2 t3_3, charpoly_fin_three]
  simp [P, Matrix.det_fin_three, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 41 →
    ((x : ℤ) ^ 3 + (344688) * (x : ℤ) ^ 2 + (-6374982426624) * (x : ℤ) + (-520435526440845312)) %
      41 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 41,
    x ^ 3 + (344688) * x ^ 2 + (-6374982426624) * x + (-520435526440845312) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 42**: the characteristic polynomial of `T₂`
on `S_42(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 41). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 41 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 3 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight42

/-! ### Weight 44 (dim 3) -/

namespace MaedaWeight44

/-- `Δ^1 E₄^8 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((44 : ℕ) : ℤ) :=
  prodForm _ 0 8 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 8 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 8 0 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (1896 : ℂ) := by
  rw [c1, show seqP 0 8 0 2 = 1896 by decide +kernel]; norm_num

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (1584252 : ℂ) := by
  rw [c1, show seqP 0 8 0 3 = 1584252 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (764588608 : ℂ) := by
  rw [c1, show seqP 0 8 0 4 = 764588608 by decide +kernel]; norm_num

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (47324878173792 : ℂ) := by
  rw [c1, show seqP 0 8 0 6 = 47324878173792 by decide +kernel]; norm_num

/-- `Δ^2 E₄^5 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((44 : ℕ) : ℤ) :=
  prodForm _ 1 5 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 5 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 5 0 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 5 0 2 = 1 by decide +kernel]; norm_num

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (1152 : ℂ) := by
  rw [c2, show seqP 1 5 0 3 = 1152 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (530280 : ℂ) := by
  rw [c2, show seqP 1 5 0 4 = 530280 by decide +kernel]; norm_num

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (13881322620 : ℂ) := by
  rw [c2, show seqP 1 5 0 6 = 13881322620 by decide +kernel]; norm_num

/-- `Δ^3 E₄^2 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((44 : ℕ) : ℤ) :=
  prodForm _ 2 2 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 2 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, show seqP 2 2 0 1 = 0 by decide +kernel]; norm_num

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, show seqP 2 2 0 2 = 0 by decide +kernel]; norm_num

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, show seqP 2 2 0 3 = 1 by decide +kernel]; norm_num

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (408 : ℂ) := by
  rw [c3, show seqP 2 2 0 4 = 408 by decide +kernel]; norm_num

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-2270208 : ℂ) := by
  rw [c3, show seqP 2 2 0 6 = -2270208 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((44 : ℕ) : ℤ)) = 3 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 32 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_44`. -/
noncomputable def T2 := heckeTPₗ ((44 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (1896 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (8796857610816 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (47324878173792 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (530280 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (13881322620 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (408 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-2270208 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

/-- The integer characteristic polynomial of `T₂` on `S_44`. -/
noncomputable def P : ℤ[X] :=
  X ^ 3 + C (2209944) * X ^ 2 + C (-15663522502656) * X + C (-19976984434430705664)

/-- **The characteristic polynomial of `T₂` on `S_44`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim3 finrank_eq f1 f2 f3 q1_1 q1_2 q1_3 q2_1 q2_2 q2_3 q3_1 q3_2 q3_3 T2
    t1_1 t1_2 t1_3 t2_1 t2_2 t2_3 t3_1 t3_2 t3_3, charpoly_fin_three]
  simp [P, Matrix.det_fin_three, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 61 →
    ((x : ℤ) ^ 3 + (2209944) * (x : ℤ) ^ 2 + (-15663522502656) * (x : ℤ) +
      (-19976984434430705664)) % 61 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 61,
    x ^ 3 + (2209944) * x ^ 2 + (-15663522502656) * x + (-19976984434430705664) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 44**: the characteristic polynomial of `T₂`
on `S_44(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 61). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 61 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 3 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight44

/-! ### Weight 46 (dim 3) -/

namespace MaedaWeight46

/-- `Δ^1 E₄^7 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((46 : ℕ) : ℤ) :=
  prodForm _ 0 7 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 7 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 7 1 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (1152 : ℂ) := by
  rw [c1, show seqP 0 7 1 2 = 1152 by decide +kernel]; norm_num

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (333396 : ℂ) := by
  rw [c1, show seqP 0 7 1 3 = 333396 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (-148041728 : ℂ) := by
  rw [c1, show seqP 0 7 1 4 = -148041728 by decide +kernel]; norm_num

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-49223562167808 : ℂ) := by
  rw [c1, show seqP 0 7 1 6 = -49223562167808 by decide +kernel]; norm_num

/-- `Δ^2 E₄^4 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((46 : ℕ) : ℤ) :=
  prodForm _ 1 4 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 4 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 4 1 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 4 1 2 = 1 by decide +kernel]; norm_num

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (408 : ℂ) := by
  rw [c2, show seqP 1 4 1 3 = 408 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (-167040 : ℂ) := by
  rw [c2, show seqP 1 4 1 4 = -167040 by decide +kernel]; norm_num

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-25946816940 : ℂ) := by
  rw [c2, show seqP 1 4 1 6 = -25946816940 by decide +kernel]; norm_num

/-- `Δ^3 E₄^1 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((46 : ℕ) : ℤ) :=
  prodForm _ 2 1 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 1 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, show seqP 2 1 1 1 = 0 by decide +kernel]; norm_num

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, show seqP 2 1 1 2 = 0 by decide +kernel]; norm_num

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, show seqP 2 1 1 3 = 1 by decide +kernel]; norm_num

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (-336 : ℂ) := by
  rw [c3, show seqP 2 1 1 4 = -336 by decide +kernel]; norm_num

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (3844224 : ℂ) := by
  rw [c3, show seqP 2 1 1 6 = 3844224 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((46 : ℕ) : ℤ)) = 3 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 34 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_46`. -/
noncomputable def T2 := heckeTPₗ ((46 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (1152 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (35184224047104 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-49223562167808 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (-167040 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-25946816940 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (-336 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (3844224 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

/-- The integer characteristic polynomial of `T₂` on `S_46`. -/
noncomputable def P : ℤ[X] :=
  X ^ 3 + C (-3814272) * X ^ 2 + C (-44544640241664) * X + C (135250282417024401408)

/-- **The characteristic polynomial of `T₂` on `S_46`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim3 finrank_eq f1 f2 f3 q1_1 q1_2 q1_3 q2_1 q2_2 q2_3 q3_1 q3_2 q3_3 T2
    t1_1 t1_2 t1_3 t2_1 t2_2 t2_3 t3_1 t3_2 t3_3, charpoly_fin_three]
  simp [P, Matrix.det_fin_three, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 53 →
    ((x : ℤ) ^ 3 + (-3814272) * (x : ℤ) ^ 2 + (-44544640241664) * (x : ℤ) +
      (135250282417024401408)) % 53 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 53,
    x ^ 3 + (-3814272) * x ^ 2 + (-44544640241664) * x + (135250282417024401408) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 46**: the characteristic polynomial of `T₂`
on `S_46(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 53). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 53 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 3 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight46

/-! ### Weight 50 (dim 3) -/

namespace MaedaWeight50

/-- `Δ^1 E₄^8 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((50 : ℕ) : ℤ) :=
  prodForm _ 0 8 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 8 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, show seqP 0 8 1 1 = 1 by decide +kernel]; norm_num

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (1392 : ℂ) := by
  rw [c1, show seqP 0 8 1 2 = 1392 by decide +kernel]; norm_num

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (612036 : ℂ) := by
  rw [c1, show seqP 0 8 1 3 = 612036 by decide +kernel]; norm_num

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (-65531648 : ℂ) := by
  rw [c1, show seqP 0 8 1 4 = -65531648 by decide +kernel]; norm_num

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-83773915149888 : ℂ) := by
  rw [c1, show seqP 0 8 1 6 = -83773915149888 by decide +kernel]; norm_num

/-- `Δ^2 E₄^5 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((50 : ℕ) : ℤ) :=
  prodForm _ 1 5 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 5 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, show seqP 1 5 1 1 = 0 by decide +kernel]; norm_num

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, show seqP 1 5 1 2 = 1 by decide +kernel]; norm_num

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (648 : ℂ) := by
  rw [c2, show seqP 1 5 1 3 = 648 by decide +kernel]; norm_num

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (-66960 : ℂ) := by
  rw [c2, show seqP 1 5 1 4 = -66960 by decide +kernel]; norm_num

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-56445600060 : ℂ) := by
  rw [c2, show seqP 1 5 1 6 = -56445600060 by decide +kernel]; norm_num

/-- `Δ^3 E₄^2 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((50 : ℕ) : ℤ) :=
  prodForm _ 2 2 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 2 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, show seqP 2 2 1 1 = 0 by decide +kernel]; norm_num

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, show seqP 2 2 1 2 = 0 by decide +kernel]; norm_num

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, show seqP 2 2 1 3 = 1 by decide +kernel]; norm_num

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (-96 : ℂ) := by
  rw [c3, show seqP 2 2 1 4 = -96 by decide +kernel]; norm_num

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-24220416 : ℂ) := by
  rw [c3, show seqP 2 2 1 6 = -24220416 by decide +kernel]; norm_num

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((50 : ℕ) : ℤ)) = 3 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 38 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_50`. -/
noncomputable def T2 := heckeTPₗ ((50 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (1392 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (562949887889664 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-83773915149888 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (-66960 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-56445600060 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (-96 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-24220416 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

/-- The integer characteristic polynomial of `T₂` on `S_50`. -/
noncomputable def P : ℤ[X] :=
  X ^ 3 + C (24225168) * X ^ 2 + C (-566746931810304) * X + C (-13634883228742736412672)

/-- **The characteristic polynomial of `T₂` on `S_50`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim3 finrank_eq f1 f2 f3 q1_1 q1_2 q1_3 q2_1 q2_2 q2_3 q3_1 q3_2 q3_3 T2
    t1_1 t1_2 t1_3 t2_1 t2_2 t2_3 t3_1 t3_2 t3_3, charpoly_fin_three]
  simp [P, Matrix.det_fin_three, map_ofNat]
  ring

lemma noRoot_raw_cert : ∀ x : ℕ, x < 53 →
    ((x : ℤ) ^ 3 + (24225168) * (x : ℤ) ^ 2 + (-566746931810304) * (x : ℤ) +
      (-13634883228742736412672)) % 53 ≠ 0 := by
  decide +kernel

lemma noRoot_raw : ∀ x : ZMod 53,
    x ^ 3 + (24225168) * x ^ 2 + (-566746931810304) * x + (-13634883228742736412672) ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  refine noRoot_raw_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- **Maeda's conjecture in weight 50**: the characteristic polynomial of `T₂`
on `S_50(SL(2, ℤ))` is irreducible over `ℚ` (no root mod 53). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ 53 fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = 3 by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight50

