import MathProof.ModularForms.MaedaDim4

/-!
# Maeda's conjecture for the level-one weights with `dim S_k = 4`

Instances of `MathProof/ModularForms/MaedaLevelOne.lean`, generated from the
numerical data (`tools/gen_maeda.py`): for each weight the triangular basis
`Δ^i E₄^a E₆^b`, its first q-coefficients (kernel-computed), the matrix of `T₂`
(from `charpoly_dim4`), the characteristic polynomial and its irreducibility
over `ℚ` (irreducible modulo a small prime: no root and no quadratic factor).
-/

open UpperHalfPlane ModularForm CuspForm Polynomial MaedaLevelOne
open scoped MatrixGroups

/-! ### Weight 48 (dim 4) -/

namespace MaedaWeight48

/-- `Δ^1 E₄^9 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((48 : ℕ) : ℤ) :=
  prodForm _ 0 9 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 9 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1 : seqPL 0 9 0 9 =
    [0, 1, 2136, 2041452,
     1148911168, 421432673550, 105266268509472, 18153641950348856,
     2144734201098954240] := by
  decide +kernel

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (2136 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (2041452 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (1148911168 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (105266268509472 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (2144734201098954240 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^6 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((48 : ℕ) : ℤ) :=
  prodForm _ 1 6 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 6 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2 : seqPL 1 6 0 9 =
    [0, 0, 1, 1392,
     808920, 251518400, 44255964780, 4209798293856,
     174519558509120] := by
  decide +kernel

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (1392 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (808920 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (44255964780 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (174519558509120 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^3 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((48 : ℕ) : ℤ) :=
  prodForm _ 2 3 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 3 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3 : seqPL 2 3 0 9 =
    [0, 0, 0, 1,
     648, 129924, 5780352, -416830374,
     8993757888] := by
  decide +kernel

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (648 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (5780352 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (8993757888 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^0 E₆^0`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((48 : ℕ) : ℤ) :=
  prodForm _ 3 0 0 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 0 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4 : seqPL 3 0 0 9 =
    [0, 0, 0, 0,
     1, -96, 4464, -133760,
     2897880] := by
  decide +kernel

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (4464 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (2897880 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((48 : ℕ) : ℤ)) = 4 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 36 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_48`. -/
noncomputable def T2 := heckeTPₗ ((48 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (2136 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (140738637266496 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (105266268509472 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (2445349476225934848 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (808920 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (44255964780 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (315257046864448 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (648 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (5780352 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (8993757888 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (4464 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (2897880 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

/-- The integer characteristic polynomial of `T₂` on `S_48`. -/
noncomputable def P : ℤ[X] :=
  X ^ 4 + C (-5785560) * X ^ 3 + C (-467142374034432) * X ^ 2
    + C (1426830562183253852160) * X + C (3297913828840214320807673856)

/-- **The characteristic polynomial of `T₂` on `S_48`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim4 finrank_eq f1 f2 f3 f4
    q1_1 q1_2 q1_3 q1_4 q2_1 q2_2 q2_3 q2_4
    q3_1 q3_2 q3_3 q3_4 q4_1 q4_2 q4_3 q4_4 T2
    t1_1 t1_2 t1_3 t1_4 t2_1 t2_2 t2_3 t2_4
    t3_1 t3_2 t3_3 t3_4 t4_1 t4_2 t4_3 t4_4, charpoly_fin_four]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 53. -/
def r3 : ZMod 53 := ((-5785560 : ℤ) : ZMod 53)
/-- See `r3`. -/
def r2 : ZMod 53 := ((-467142374034432 : ℤ) : ZMod 53)
/-- See `r3`. -/
def r1 : ZMod 53 := ((1426830562183253852160 : ℤ) : ZMod 53)
/-- See `r3`. -/
def r0 : ZMod 53 := ((3297913828840214320807673856 : ℤ) : ZMod 53)

lemma noRoot : ∀ x : ZMod 53, x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 53,
    ¬ (u * (r2 - v - u * (r3 - u)) + v * (r3 - u) = r1
      ∧ v * (r2 - v - u * (r3 - u)) = r0) := by
  decide +kernel

/-- **Maeda's conjecture in weight 48** (irreducibility): the characteristic
polynomial of `T₂` on `S_48(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 53). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  exact irreducible_quartic_of_mod (by unfold P; monicity!) 53 r3 r2 r1 r0
    (by simp [P, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight48

/-! ### Weight 52 (dim 4) -/

namespace MaedaWeight52

/-- `Δ^1 E₄^10 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((52 : ℕ) : ℤ) :=
  prodForm _ 0 10 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 10 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1 : seqPL 0 10 0 9 =
    [0, 1, 2376, 2556252,
     1643480128, 701595261630, 208905514294752, 44335597481431256,
     6731835627515834880] := by
  decide +kernel

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (2376 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (2556252 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (1643480128 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (208905514294752 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (6731835627515834880 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^7 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((52 : ℕ) : ℤ) :=
  prodForm _ 1 7 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 7 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2 : seqPL 1 7 0 9 =
    [0, 0, 1, 1632,
     1145160, 448672640, 106377019740, 15379969945536,
     1282168451040320] := by
  decide +kernel

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (1632 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (1145160 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (106377019740 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (1282168451040320 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^4 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((52 : ℕ) : ℤ) :=
  prodForm _ 2 4 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 4 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3 : seqPL 2 4 0 9 =
    [0, 0, 0, 1,
     888, 287604, 38368512, 1255462026,
     -77675499072] := by
  decide +kernel

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (888 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (38368512 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (-77675499072 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^1 E₆^0`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((52 : ℕ) : ℤ) :=
  prodForm _ 3 1 0 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 1 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4 : seqPL 3 1 0 9 =
    [0, 0, 0, 0,
     1, 144, -16416, 736960,
     -20189880] := by
  decide +kernel

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (-16416 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (-20189880 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((52 : ℕ) : ℤ)) = 4 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 40 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_52`. -/
noncomputable def T2 := heckeTPₗ ((52 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (2376 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (2251801457165376 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (208905514294752 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (12082111984831984128 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (1145160 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (106377019740 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (3533968264725568 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (888 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (38368512 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (-77675499072 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (-16416 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (-20189880 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

/-- The integer characteristic polynomial of `T₂` on `S_52`. -/
noncomputable def P : ℤ[X] :=
  X ^ 4 + C (-32756040) * X ^ 3 + C (-7956172284567552) * X ^ 2
    + C (269568678949709508771840) * X + C (4615876968087578049834569957376)

/-- **The characteristic polynomial of `T₂` on `S_52`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim4 finrank_eq f1 f2 f3 f4
    q1_1 q1_2 q1_3 q1_4 q2_1 q2_2 q2_3 q2_4
    q3_1 q3_2 q3_3 q3_4 q4_1 q4_2 q4_3 q4_4 T2
    t1_1 t1_2 t1_3 t1_4 t2_1 t2_2 t2_3 t2_4
    t3_1 t3_2 t3_3 t3_4 t4_1 t4_2 t4_3 t4_4, charpoly_fin_four]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 67. -/
def r3 : ZMod 67 := ((-32756040 : ℤ) : ZMod 67)
/-- See `r3`. -/
def r2 : ZMod 67 := ((-7956172284567552 : ℤ) : ZMod 67)
/-- See `r3`. -/
def r1 : ZMod 67 := ((269568678949709508771840 : ℤ) : ZMod 67)
/-- See `r3`. -/
def r0 : ZMod 67 := ((4615876968087578049834569957376 : ℤ) : ZMod 67)

lemma noRoot : ∀ x : ZMod 67, x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 67,
    ¬ (u * (r2 - v - u * (r3 - u)) + v * (r3 - u) = r1
      ∧ v * (r2 - v - u * (r3 - u)) = r0) := by
  decide +kernel

/-- **Maeda's conjecture in weight 52** (irreducibility): the characteristic
polynomial of `T₂` on `S_52(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 67). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  exact irreducible_quartic_of_mod (by unfold P; monicity!) 67 r3 r2 r1 r0
    (by simp [P, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight52

/-! ### Weight 54 (dim 4) -/

namespace MaedaWeight54

/-- `Δ^1 E₄^9 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((54 : ℕ) : ℤ) :=
  prodForm _ 0 9 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 9 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1 : seqPL 0 9 1 9 =
    [0, 1, 1632, 948276,
     84370432, -191835194250, -126496678589568, -42052205012680408,
     -8807931306330193920] := by
  decide +kernel

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (1632 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (948276 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (84370432 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-126496678589568 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (-8807931306330193920 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^6 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((54 : ℕ) : ℤ) :=
  prodForm _ 1 6 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 6 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2 : seqPL 1 6 1 9 =
    [0, 0, 1, 888,
     90720, -179452000, -96134981580, -22378682862864,
     -2714647846067200] := by
  decide +kernel

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (888 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (90720 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-96134981580 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (-2714647846067200 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^3 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((54 : ℕ) : ℤ) :=
  prodForm _ 2 3 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 3 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3 : seqPL 2 3 1 9 =
    [0, 0, 0, 1,
     144, -213300, -70601856, -5571244926,
     106613134848] := by
  decide +kernel

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (144 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-70601856 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (106613134848 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^0 E₆^1`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((54 : ℕ) : ℤ) :=
  prodForm _ 3 0 1 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 0 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4 : seqPL 3 0 1 9 =
    [0, 0, 0, 0,
     1, -600, 36216, -909920,
     7340640] := by
  decide +kernel

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (36216 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (7340640 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((54 : ℕ) : ℤ)) = 4 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 42 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_54`. -/
noncomputable def T2 := heckeTPₗ ((54 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (1632 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (9007199339111424 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-126496678589568 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (5891817877407105024 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (90720 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-96134981580 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (6292551408673792 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (144 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-70601856 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (106613134848 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (36216 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (7340640 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

/-- The integer characteristic polynomial of `T₂` on `S_54`. -/
noncomputable def P : ℤ[X] :=
  X ^ 4 + C (68476320) * X ^ 3 + C (-19584715019010048) * X ^ 2
    + C (-1083312724663489297121280) * X + C (39446133467662904714689328971776)

/-- **The characteristic polynomial of `T₂` on `S_54`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim4 finrank_eq f1 f2 f3 f4
    q1_1 q1_2 q1_3 q1_4 q2_1 q2_2 q2_3 q2_4
    q3_1 q3_2 q3_3 q3_4 q4_1 q4_2 q4_3 q4_4 T2
    t1_1 t1_2 t1_3 t1_4 t2_1 t2_2 t2_3 t2_4
    t3_1 t3_2 t3_3 t3_4 t4_1 t4_2 t4_3 t4_4, charpoly_fin_four]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 83. -/
def r3 : ZMod 83 := ((68476320 : ℤ) : ZMod 83)
/-- See `r3`. -/
def r2 : ZMod 83 := ((-19584715019010048 : ℤ) : ZMod 83)
/-- See `r3`. -/
def r1 : ZMod 83 := ((-1083312724663489297121280 : ℤ) : ZMod 83)
/-- See `r3`. -/
def r0 : ZMod 83 := ((39446133467662904714689328971776 : ℤ) : ZMod 83)

lemma noRoot : ∀ x : ZMod 83, x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 83,
    ¬ (u * (r2 - v - u * (r3 - u)) + v * (r3 - u) = r1
      ∧ v * (r2 - v - u * (r3 - u)) = r0) := by
  decide +kernel

/-- **Maeda's conjecture in weight 54** (irreducibility): the characteristic
polynomial of `T₂` on `S_54(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 83). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 83) := ⟨by norm_num⟩
  exact irreducible_quartic_of_mod (by unfold P; monicity!) 83 r3 r2 r1 r0
    (by simp [P, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight54

/-! ### Weight 56 (dim 4) -/

namespace MaedaWeight56

/-- `Δ^1 E₄^11 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((56 : ℕ) : ℤ) :=
  prodForm _ 0 11 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 11 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1 : seqPL 0 11 0 9 =
    [0, 1, 2616, 3128652,
     2262119488, 1101567980910, 380855513833632, 95999455721198456,
     17828358525310840320] := by
  decide +kernel

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (2616 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (3128652 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (2262119488 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (380855513833632 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (17828358525310840320 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^8 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((56 : ℕ) : ℤ) :=
  prodForm _ 1 8 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 8 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2 : seqPL 1 8 0 9 =
    [0, 0, 1, 1872,
     1539000, 727042880, 216542983500, 41887311683616,
     5206170793363520] := by
  decide +kernel

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (1872 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (1539000 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (216542983500 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (5206170793363520 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^5 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((56 : ℕ) : ℤ) :=
  prodForm _ 2 5 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 5 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3 : seqPL 2 5 0 9 =
    [0, 0, 0, 1,
     1128, 502884, 109318272, 11091114426,
     308459659968] := by
  decide +kernel

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (1128 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (109318272 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (308459659968 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^2 E₆^0`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((56 : ℕ) : ℤ) :=
  prodForm _ 3 2 0 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 2 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4 : seqPL 3 2 0 9 =
    [0, 0, 0, 0,
     1, 384, 20304, -2885120,
     122207160] := by
  decide +kernel

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (20304 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (122207160 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((56 : ℕ) : ℤ)) = 4 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 44 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_56`. -/
noncomputable def T2 := heckeTPₗ ((56 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (2616 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (36028799281083456 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (380855513833632 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (112079691526920580608 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (1539000 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (216542983500 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (41234967812327488 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (1128 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (109318272 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (308459659968 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (20304 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (122207160 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

/-- The integer characteristic polynomial of `T₂` on `S_56`. -/
noncomputable def P : ℤ[X] :=
  X ^ 4 + C (-208622520) * X ^ 3 + C (-69659795501724672) * X ^ 2
    + C (11031882363768735132549120) * X + C (-255678332805518077225389998997504)

/-- **The characteristic polynomial of `T₂` on `S_56`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim4 finrank_eq f1 f2 f3 f4
    q1_1 q1_2 q1_3 q1_4 q2_1 q2_2 q2_3 q2_4
    q3_1 q3_2 q3_3 q3_4 q4_1 q4_2 q4_3 q4_4 T2
    t1_1 t1_2 t1_3 t1_4 t2_1 t2_2 t2_3 t2_4
    t3_1 t3_2 t3_3 t3_4 t4_1 t4_2 t4_3 t4_4, charpoly_fin_four]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 71. -/
def r3 : ZMod 71 := ((-208622520 : ℤ) : ZMod 71)
/-- See `r3`. -/
def r2 : ZMod 71 := ((-69659795501724672 : ℤ) : ZMod 71)
/-- See `r3`. -/
def r1 : ZMod 71 := ((11031882363768735132549120 : ℤ) : ZMod 71)
/-- See `r3`. -/
def r0 : ZMod 71 := ((-255678332805518077225389998997504 : ℤ) : ZMod 71)

lemma noRoot : ∀ x : ZMod 71, x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 71,
    ¬ (u * (r2 - v - u * (r3 - u)) + v * (r3 - u) = r1
      ∧ v * (r2 - v - u * (r3 - u)) = r0) := by
  decide +kernel

/-- **Maeda's conjecture in weight 56** (irreducibility): the characteristic
polynomial of `T₂` on `S_56(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 71). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 71) := ⟨by norm_num⟩
  exact irreducible_quartic_of_mod (by unfold P; monicity!) 71 r3 r2 r1 r0
    (by simp [P, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight56

/-! ### Weight 58 (dim 4) -/

namespace MaedaWeight58

/-- `Δ^1 E₄^10 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((58 : ℕ) : ℤ) :=
  prodForm _ 0 10 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 10 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1 : seqPL 0 10 1 9 =
    [0, 1, 1872, 1342116,
     315488512, -169527029850, -172348484038848, -72825188261246008,
     -19174980960687697920] := by
  decide +kernel

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (1872 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (1342116 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (315488512 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-172348484038848 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (-19174980960687697920 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^7 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((58 : ℕ) : ℤ) :=
  prodForm _ 1 7 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 7 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2 : seqPL 1 7 1 9 =
    [0, 0, 1, 1128,
     306000, -155754400, -139001521500, -45838069535664,
     -8294387594479360] := by
  decide +kernel

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (1128 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (306000 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-139001521500 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (-8294387594479360 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^4 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((58 : ℕ) : ℤ) :=
  prodForm _ 2 4 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 4 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3 : seqPL 2 4 1 9 =
    [0, 0, 0, 1,
     384, -176580, -121476096, -22975433166,
     -1384416479232] := by
  decide +kernel

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (384 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-121476096 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (-1384416479232 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^1 E₆^1`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((58 : ℕ) : ℤ) :=
  prodForm _ 3 1 1 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 1 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4 : seqPL 3 1 1 9 =
    [0, 0, 0, 0,
     1, -360, -105624, 6492640,
     -136828080] := by
  decide +kernel

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (-105624 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (-136828080 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((58 : ℕ) : ℤ)) = 4 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 46 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_58`. -/
noncomputable def T2 := heckeTPₗ ((58 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (1872 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (144115188391344384 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-172348484038848 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (250608651117314494464 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (306000 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-139001521500 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (135820800481376512 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (384 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-121476096 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (-1384416479232 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (-105624 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (-136828080 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

/-- The integer characteristic polynomial of `T₂` on `S_58`. -/
noncomputable def P : ℤ[X] :=
  X ^ 4 + C (217744560) * X ^ 3 + C (-411086477602603008) * X ^ 2
    + C (-42515907658957794091991040) * X + C (18678231666950985607375948785647616)

/-- **The characteristic polynomial of `T₂` on `S_58`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim4 finrank_eq f1 f2 f3 f4
    q1_1 q1_2 q1_3 q1_4 q2_1 q2_2 q2_3 q2_4
    q3_1 q3_2 q3_3 q3_4 q4_1 q4_2 q4_3 q4_4 T2
    t1_1 t1_2 t1_3 t1_4 t2_1 t2_2 t2_3 t2_4
    t3_1 t3_2 t3_3 t3_4 t4_1 t4_2 t4_3 t4_4, charpoly_fin_four]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 61. -/
def r3 : ZMod 61 := ((217744560 : ℤ) : ZMod 61)
/-- See `r3`. -/
def r2 : ZMod 61 := ((-411086477602603008 : ℤ) : ZMod 61)
/-- See `r3`. -/
def r1 : ZMod 61 := ((-42515907658957794091991040 : ℤ) : ZMod 61)
/-- See `r3`. -/
def r0 : ZMod 61 := ((18678231666950985607375948785647616 : ℤ) : ZMod 61)

lemma noRoot : ∀ x : ZMod 61, x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 61,
    ¬ (u * (r2 - v - u * (r3 - u)) + v * (r3 - u) = r1
      ∧ v * (r2 - v - u * (r3 - u)) = r0) := by
  decide +kernel

/-- **Maeda's conjecture in weight 58** (irreducibility): the characteristic
polynomial of `T₂` on `S_58(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 61). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  exact irreducible_quartic_of_mod (by unfold P; monicity!) 61 r3 r2 r1 r0
    (by simp [P, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight58

/-! ### Weight 62 (dim 4) -/

namespace MaedaWeight62

/-- `Δ^1 E₄^11 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((62 : ℕ) : ℤ) :=
  prodForm _ 0 11 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 11 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1 : seqPL 0 11 1 9 =
    [0, 1, 2112, 1793556,
     641646592, -90898219050, -212344464169728, -114552859161702808,
     -37026432522493624320] := by
  decide +kernel

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (2112 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (1793556 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (641646592 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-212344464169728 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (-37026432522493624320 : ℂ) := by
  rw [c1, seqP_getD (N := 9) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^8 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((62 : ℕ) : ℤ) :=
  prodForm _ 1 8 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 8 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2 : seqPL 1 8 1 9 =
    [0, 0, 1, 1368,
     578880, -79871200, -175714019820, -79532788086864,
     -19596808843755520] := by
  decide +kernel

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (1368 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (578880 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-175714019820 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (-19596808843755520 : ℂ) := by
  rw [c2, seqP_getD (N := 9) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^5 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((62 : ℕ) : ℤ) :=
  prodForm _ 2 5 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 5 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3 : seqPL 2 5 1 9 =
    [0, 0, 0, 1,
     624, -82260, -163019136, -52508511006,
     -7162088666112] := by
  decide +kernel

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (624 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-163019136 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (-7162088666112 : ℂ) := by
  rw [c3, seqP_getD (N := 9) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^2 E₆^1`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((62 : ℕ) : ℤ) :=
  prodForm _ 3 2 1 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 2 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4 : seqPL 3 2 1 9 =
    [0, 0, 0, 0,
     1, -120, -189864, -19628000,
     1190856000] := by
  decide +kernel

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (-189864 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (1190856000 : ℂ) := by
  rw [c4, seqP_getD (N := 9) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((62 : ℕ) : ℤ)) = 4 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 50 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_62`. -/
noncomputable def T2 := heckeTPₗ ((62 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (2112 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (2305843009855340544 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-212344464169728 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (4832914002936828002304 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (578880 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-175714019820 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (2286246200369938432 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (624 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-163019136 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (-7162088666112 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (-189864 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (1190856000 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

/-- The integer characteristic polynomial of `T₂` on `S_62`. -/
noncomputable def P : ℤ[X] :=
  X ^ 4 + C (-1146312000) * X ^ 3 + C (-6156169255669690368) * X ^ 2
    + C (2540887466526178560442368000) * X + C (3583176547297492565952659077522784256)

/-- **The characteristic polynomial of `T₂` on `S_62`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim4 finrank_eq f1 f2 f3 f4
    q1_1 q1_2 q1_3 q1_4 q2_1 q2_2 q2_3 q2_4
    q3_1 q3_2 q3_3 q3_4 q4_1 q4_2 q4_3 q4_4 T2
    t1_1 t1_2 t1_3 t1_4 t2_1 t2_2 t2_3 t2_4
    t3_1 t3_2 t3_3 t3_4 t4_1 t4_2 t4_3 t4_4, charpoly_fin_four]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 71. -/
def r3 : ZMod 71 := ((-1146312000 : ℤ) : ZMod 71)
/-- See `r3`. -/
def r2 : ZMod 71 := ((-6156169255669690368 : ℤ) : ZMod 71)
/-- See `r3`. -/
def r1 : ZMod 71 := ((2540887466526178560442368000 : ℤ) : ZMod 71)
/-- See `r3`. -/
def r0 : ZMod 71 := ((3583176547297492565952659077522784256 : ℤ) : ZMod 71)

lemma noRoot : ∀ x : ZMod 71, x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 71,
    ¬ (u * (r2 - v - u * (r3 - u)) + v * (r3 - u) = r1
      ∧ v * (r2 - v - u * (r3 - u)) = r0) := by
  decide +kernel

/-- **Maeda's conjecture in weight 62** (irreducibility): the characteristic
polynomial of `T₂` on `S_62(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 71). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 71) := ⟨by norm_num⟩
  exact irreducible_quartic_of_mod (by unfold P; monicity!) 71 r3 r2 r1 r0
    (by simp [P, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight62

