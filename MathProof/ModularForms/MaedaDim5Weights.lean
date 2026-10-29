import MathProof.ModularForms.MaedaDim5
import MathProof.ModularForms.MaedaCertC

/-!
# Maeda's conjecture for the level-one weights with `dim S_k = 5`

Instances of `MathProof/ModularForms/MaedaLevelOne.lean`, generated from the
numerical data (`tools/gen_maeda.py`): for each weight the triangular basis
`Δ^i E₄^a E₆^b`, its first q-coefficients (kernel-computed), the matrix of `T₂`
(from `charpoly_dim5`), the characteristic polynomial and its irreducibility
over `ℚ` (irreducible modulo a small prime: no root and no quadratic factor).
-/

open UpperHalfPlane ModularForm CuspForm Polynomial MaedaLevelOne
open scoped MatrixGroups

/-! ### Weight 60 (dim 5) -/

namespace MaedaWeight60

/-- `Δ^1 E₄^12 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((60 : ℕ) : ℤ) :=
  prodForm _ 0 12 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 12 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1c : seqPLc 0 12 0 11 =
    [0, 1, 2856, 3758652,
     3018653248, 1651252143390, 650139077750112, 189799422216146456,
     41698318072212994560, 6925107939087424526037, 866141635540622367921840] := by
  decide +kernel

lemma L1 : seqPL 0 12 0 11 =
    [0, 1, 2856, 3758652,
     3018653248, 1651252143390, 650139077750112, 189799422216146456,
     41698318072212994560, 6925107939087424526037, 866141635540622367921840] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L1c

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (2856 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (3758652 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (3018653248 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_5 : (qExpansion 1 f1).coeff 5 = (1651252143390 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (650139077750112 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (41698318072212994560 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_10 : (qExpansion 1 f1).coeff 10 = (866141635540622367921840 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^9 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((60 : ℕ) : ℤ) :=
  prodForm _ 1 9 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 9 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2c : seqPLc 1 9 0 11 =
    [0, 0, 1, 2112,
     1990440, 1100453120, 394370112060, 95438415252096,
     15731771189894720, 1734959081918062080, 121828014479762269470] := by
  decide +kernel

lemma L2 : seqPL 1 9 0 11 =
    [0, 0, 1, 2112,
     1990440, 1100453120, 394370112060, 95438415252096,
     15731771189894720, 1734959081918062080, 121828014479762269470] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L2c

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (2112 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (1990440 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_5 : (qExpansion 1 f2).coeff 5 = (1100453120 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (394370112060 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (15731771189894720 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_10 : (qExpansion 1 f2).coeff 10 = (121828014479762269470 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^6 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((60 : ℕ) : ℤ) :=
  prodForm _ 2 6 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 6 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3c : seqPLc 2 6 0 11 =
    [0, 0, 0, 1,
     1368, 775764, 232453632, 38421326826,
     3209853763008, 84270566144376, -2601592081238016] := by
  decide +kernel

lemma L3 : seqPL 2 6 0 11 =
    [0, 0, 0, 1,
     1368, 775764, 232453632, 38421326826,
     3209853763008, 84270566144376, -2601592081238016] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L3c

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (1368 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_5 : (qExpansion 1 f3).coeff 5 = (775764 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (232453632 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (3209853763008 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_10 : (qExpansion 1 f3).coeff 10 = (-2601592081238016 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^3 E₆^0`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((60 : ℕ) : ℤ) :=
  prodForm _ 3 3 0 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 3 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4c : seqPLc 3 3 0 11 =
    [0, 0, 0, 0,
     1, 624, 114624, 2824000,
     -523767000, 20266211232, -420667929856] := by
  decide +kernel

lemma L4 : seqPL 3 3 0 11 =
    [0, 0, 0, 0,
     1, 624, 114624, 2824000,
     -523767000, 20266211232, -420667929856] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L4c

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_5 : (qExpansion 1 f4).coeff 5 = (624 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (114624 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (-523767000 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_10 : (qExpansion 1 f4).coeff 10 = (-420667929856 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^5 E₄^0 E₆^0`. -/
noncomputable def f5 : CuspForm 𝒮ℒ ((60 : ℕ) : ℤ) :=
  prodForm _ 4 0 0 (by norm_num)

lemma c5 (n : ℕ) : (qExpansion 1 f5).coeff n = seqP 4 0 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L5c : seqPLc 4 0 0 11 =
    [0, 0, 0, 0,
     0, 1, -120, 7020,
     -266560, 7379190, -158562144] := by
  decide +kernel

lemma L5 : seqPL 4 0 0 11 =
    [0, 0, 0, 0,
     0, 1, -120, 7020,
     -266560, 7379190, -158562144] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L5c

lemma q5_1 : (qExpansion 1 f5).coeff 1 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_2 : (qExpansion 1 f5).coeff 2 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_3 : (qExpansion 1 f5).coeff 3 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_4 : (qExpansion 1 f5).coeff 4 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_5 : (qExpansion 1 f5).coeff 5 = (1 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_6 : (qExpansion 1 f5).coeff 6 = (-120 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_8 : (qExpansion 1 f5).coeff 8 = (-266560 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_10 : (qExpansion 1 f5).coeff 10 = (-158562144 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((60 : ℕ) : ℤ)) = 5 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 48 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_60`. -/
noncomputable def T2 := heckeTPₗ ((60 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (2856 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (576460755322076736 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (650139077750112 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (1688070226650790476288 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t1_5 : (qExpansion 1 (T2 f1)).coeff 5 = (866141635540622367921840 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_10]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (1990440 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (394370112060 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (592192523493318208 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t2_5 : (qExpansion 1 (T2 f2)).coeff 5 = (121828014479762269470 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_10]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (1368 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (232453632 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (3209853763008 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t3_5 : (qExpansion 1 (T2 f3)).coeff 5 = (-2601592081238016 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_10]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (114624 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (-523767000 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

lemma t4_5 : (qExpansion 1 (T2 f4)).coeff 5 = (-420667929856 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_10]

lemma t5_1 : (qExpansion 1 (T2 f5)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_2]

lemma t5_2 : (qExpansion 1 (T2 f5)).coeff 2 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_4, q5_1]

lemma t5_3 : (qExpansion 1 (T2 f5)).coeff 3 = (-120 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_6]

lemma t5_4 : (qExpansion 1 (T2 f5)).coeff 4 = (-266560 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_8, q5_2]

lemma t5_5 : (qExpansion 1 (T2 f5)).coeff 5 = (-158562144 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_10]

/-- The integer characteristic polynomial of `T₂` on `S_60`. -/
noncomputable def P : ℤ[X] :=
  X ^ 5
    + C (449691864) * X ^ 4
    + C (-2209450184054433792) * X ^ 3
    + C (-736010060393513697870348288) * X ^ 2
    + C (810634763334812972416233648439689216) * X
    + C (263222216157060824115203098902237248565018624)

/-- **The characteristic polynomial of `T₂` on `S_60`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim5 finrank_eq f1 f2 f3 f4 f5
    q1_1 q1_2 q1_3 q1_4 q1_5 q2_1 q2_2 q2_3 q2_4 q2_5 q3_1 q3_2 q3_3
    q3_4 q3_5 q4_1 q4_2 q4_3 q4_4 q4_5 q5_1 q5_2 q5_3 q5_4 q5_5 T2
    t1_1 t1_2 t1_3 t1_4 t1_5 t2_1 t2_2 t2_3 t2_4 t2_5 t3_1 t3_2 t3_3
    t3_4 t3_5 t4_1 t4_2 t4_3 t4_4 t4_5 t5_1 t5_2 t5_3 t5_4 t5_5, charpoly_fin_five]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 83. -/
def r4 : ZMod 83 := ((449691864 : ℤ) : ZMod 83)
/-- See `r4`. -/
def r3 : ZMod 83 := ((-2209450184054433792 : ℤ) : ZMod 83)
/-- See `r4`. -/
def r2 : ZMod 83 := ((-736010060393513697870348288 : ℤ) : ZMod 83)
/-- See `r4`. -/
def r1 : ZMod 83 := ((810634763334812972416233648439689216 : ℤ) : ZMod 83)
/-- See `r4`. -/
def r0 : ZMod 83 := ((263222216157060824115203098902237248565018624 : ℤ) : ZMod 83)

lemma noRoot_cert : ∀ x : ℕ, x < 83 →
    ((x : ℤ) ^ 5 + (449691864) * (x : ℤ) ^ 4 + (-2209450184054433792) * (x : ℤ) ^ 3 +
      (-736010060393513697870348288) * (x : ℤ) ^ 2
      + (810634763334812972416233648439689216) * (x : ℤ) +
      (263222216157060824115203098902237248565018624)) % 83 ≠ 0 := by
  decide +kernel

lemma noRoot : ∀ x : ZMod 83,
    x ^ 5 + r4 * x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  simp only [r4, r3, r2, r1, r0] at h1
  push_cast at h1
  refine noRoot_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma noQuad_cert : ∀ u : ℕ, u < 83 → ∀ v : ℕ, v < 83 →
    ¬ (((u : ℤ) * ((-736010060393513697870348288) - (v : ℤ) * ((449691864) - (u : ℤ)) - (u : ℤ) *
      ((-2209450184054433792) - (v : ℤ) - (u : ℤ) * ((449691864) - (u : ℤ))))
        + (v : ℤ) * ((-2209450184054433792) - (v : ℤ) - (u : ℤ) * ((449691864) - (u : ℤ))) -
      (810634763334812972416233648439689216)) % 83 = 0
      ∧ ((v : ℤ) * ((-736010060393513697870348288) - (v : ℤ) * ((449691864) - (u : ℤ)) - (u : ℤ) *
      ((-2209450184054433792) - (v : ℤ) - (u : ℤ) * ((449691864) - (u : ℤ)))) -
      (263222216157060824115203098902237248565018624)) % 83 = 0) := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 83,
    ¬ (u * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u)))
        + v * (r3 - v - u * (r4 - u)) = r1
      ∧ v * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u))) = r0) := by
  rintro u v ⟨h1, h2⟩
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq u
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq v
  simp only [r4, r3, r2, r1] at h1
  push_cast at h1
  simp only [r4, r3, r2, r0] at h2
  push_cast at h2
  refine noQuad_cert y hy z hz
    ⟨HornerCert.emod_eq_zero_of_cast ?_, HornerCert.emod_eq_zero_of_cast ?_⟩
  · push_cast
    linear_combination h1
  · push_cast
    linear_combination h2

/-- **Maeda's conjecture in weight 60** (irreducibility): the characteristic
polynomial of `T₂` on `S_60(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 83). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 83) := ⟨by norm_num⟩
  exact irreducible_quintic_of_mod (by unfold P; monicity!) 83 r4 r3 r2 r1 r0
    (by simp [P, r4, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight60

/-! ### Weight 64 (dim 5) -/

namespace MaedaWeight64

/-- `Δ^1 E₄^13 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((64 : ℕ) : ℤ) :=
  prodForm _ 0 13 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 13 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1c : seqPLc 0 13 0 11 =
    [0, 1, 3096, 4446252,
     3926905408, 2383866821070, 1052985191388192, 349419856793731256,
     88665629227071321600, 17347068984457085935077, 2619522800628262688592720] := by
  decide +kernel

lemma L1 : seqPL 0 13 0 11 =
    [0, 1, 3096, 4446252,
     3926905408, 2383866821070, 1052985191388192, 349419856793731256,
     88665629227071321600, 17347068984457085935077, 2619522800628262688592720] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L1c

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (3096 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (4446252 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (3926905408 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_5 : (qExpansion 1 f1).coeff 5 = (2383866821070 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (1052985191388192 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (88665629227071321600 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_10 : (qExpansion 1 f1).coeff 10 = (2619522800628262688592720 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^10 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((64 : ℕ) : ℤ) :=
  prodForm _ 1 10 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 10 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2c : seqPLc 1 10 0 11 =
    [0, 0, 1, 2352,
     2499480, 1582727360, 662792421420, 192477633674976,
     39496260273849920, 5719400651847749760, 572847108823385807310] := by
  decide +kernel

lemma L2 : seqPL 1 10 0 11 =
    [0, 0, 1, 2352,
     2499480, 1582727360, 662792421420, 192477633674976,
     39496260273849920, 5719400651847749760, 572847108823385807310] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L2c

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (2352 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (2499480 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_5 : (qExpansion 1 f2).coeff 5 = (1582727360 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (662792421420 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (39496260273849920 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_10 : (qExpansion 1 f2).coeff 10 = (572847108823385807310 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^7 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((64 : ℕ) : ℤ) :=
  prodForm _ 2 7 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 7 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3c : seqPLc 2 7 0 11 =
    [0, 0, 0, 1,
     1608, 1106244, 421598592, 95895059226,
     12938309178048, 939201256431576, 24818915367335424] := by
  decide +kernel

lemma L3 : seqPL 2 7 0 11 =
    [0, 0, 0, 1,
     1608, 1106244, 421598592, 95895059226,
     12938309178048, 939201256431576, 24818915367335424] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L3c

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (1608 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_5 : (qExpansion 1 f3).coeff 5 = (1106244 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (421598592 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (12938309178048 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_10 : (qExpansion 1 f3).coeff 10 = (24818915367335424 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^4 E₆^0`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((64 : ℕ) : ℤ) :=
  prodForm _ 3 4 0 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 4 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4c : seqPLc 3 4 0 11 =
    [0, 0, 0, 0,
     1, 864, 266544, 31688320,
     405791640, -98556792768, 3332890468544] := by
  decide +kernel

lemma L4 : seqPL 3 4 0 11 =
    [0, 0, 0, 0,
     1, 864, 266544, 31688320,
     405791640, -98556792768, 3332890468544] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L4c

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_5 : (qExpansion 1 f4).coeff 5 = (864 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (266544 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (405791640 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_10 : (qExpansion 1 f4).coeff 10 = (3332890468544 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^5 E₄^1 E₆^0`. -/
noncomputable def f5 : CuspForm 𝒮ℒ ((64 : ℕ) : ℤ) :=
  prodForm _ 4 1 0 (by norm_num)

lemma c5 (n : ℕ) : (qExpansion 1 f5).coeff n = seqP 4 1 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L5c : seqPLc 4 1 0 11 =
    [0, 0, 0, 0,
     0, 1, 120, -19620,
     1165760, -42220890, 1081776096] := by
  decide +kernel

lemma L5 : seqPL 4 1 0 11 =
    [0, 0, 0, 0,
     0, 1, 120, -19620,
     1165760, -42220890, 1081776096] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L5c

lemma q5_1 : (qExpansion 1 f5).coeff 1 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_2 : (qExpansion 1 f5).coeff 2 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_3 : (qExpansion 1 f5).coeff 3 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_4 : (qExpansion 1 f5).coeff 4 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_5 : (qExpansion 1 f5).coeff 5 = (1 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_6 : (qExpansion 1 f5).coeff 6 = (120 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_8 : (qExpansion 1 f5).coeff 8 = (1165760 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_10 : (qExpansion 1 f5).coeff 10 = (1081776096 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((64 : ℕ) : ℤ)) = 5 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 52 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_64`. -/
noncomputable def T2 := heckeTPₗ ((64 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (3096 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (9223372040781681216 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (1052985191388192 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (28644225455329457223168 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t1_5 : (qExpansion 1 (T2 f1)).coeff 5 = (2619522800628262688592720 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_10]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (2499480 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (662792421420 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (9262868297128625728 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t2_5 : (qExpansion 1 (T2 f2)).coeff 5 = (572847108823385807310 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_10]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (1608 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (421598592 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (12938309178048 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t3_5 : (qExpansion 1 (T2 f3)).coeff 5 = (24818915367335424 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_10]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (266544 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (405791640 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

lemma t4_5 : (qExpansion 1 (T2 f4)).coeff 5 = (3332890468544 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_10]

lemma t5_1 : (qExpansion 1 (T2 f5)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_2]

lemma t5_2 : (qExpansion 1 (T2 f5)).coeff 2 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_4, q5_1]

lemma t5_3 : (qExpansion 1 (T2 f5)).coeff 3 = (120 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_6]

lemma t5_4 : (qExpansion 1 (T2 f5)).coeff 4 = (1165760 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_8, q5_2]

lemma t5_5 : (qExpansion 1 (T2 f5)).coeff 5 = (1081776096 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_10]

/-- The integer characteristic polynomial of `T₂` on `S_64`. -/
noncomputable def P : ℤ[X] :=
  X ^ 5
    + C (-507315096) * X ^ 4
    + C (-26316207229657439232) * X ^ 3
    + C (7816999697067374824780726272) * X ^ 2
    + C (93356730870958242939964792647614201856) * X
    + C (59899702063757157544982491709928053576589901824)

/-- **The characteristic polynomial of `T₂` on `S_64`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim5 finrank_eq f1 f2 f3 f4 f5
    q1_1 q1_2 q1_3 q1_4 q1_5 q2_1 q2_2 q2_3 q2_4 q2_5 q3_1 q3_2 q3_3
    q3_4 q3_5 q4_1 q4_2 q4_3 q4_4 q4_5 q5_1 q5_2 q5_3 q5_4 q5_5 T2
    t1_1 t1_2 t1_3 t1_4 t1_5 t2_1 t2_2 t2_3 t2_4 t2_5 t3_1 t3_2 t3_3
    t3_4 t3_5 t4_1 t4_2 t4_3 t4_4 t4_5 t5_1 t5_2 t5_3 t5_4 t5_5, charpoly_fin_five]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 73. -/
def r4 : ZMod 73 := ((-507315096 : ℤ) : ZMod 73)
/-- See `r4`. -/
def r3 : ZMod 73 := ((-26316207229657439232 : ℤ) : ZMod 73)
/-- See `r4`. -/
def r2 : ZMod 73 := ((7816999697067374824780726272 : ℤ) : ZMod 73)
/-- See `r4`. -/
def r1 : ZMod 73 := ((93356730870958242939964792647614201856 : ℤ) : ZMod 73)
/-- See `r4`. -/
def r0 : ZMod 73 := ((59899702063757157544982491709928053576589901824 : ℤ) : ZMod 73)

lemma noRoot_cert : ∀ x : ℕ, x < 73 →
    ((x : ℤ) ^ 5 + (-507315096) * (x : ℤ) ^ 4 + (-26316207229657439232) * (x : ℤ) ^ 3 +
      (7816999697067374824780726272) * (x : ℤ) ^ 2
      + (93356730870958242939964792647614201856) * (x : ℤ) +
      (59899702063757157544982491709928053576589901824)) % 73 ≠ 0 := by
  decide +kernel

lemma noRoot : ∀ x : ZMod 73,
    x ^ 5 + r4 * x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  simp only [r4, r3, r2, r1, r0] at h1
  push_cast at h1
  refine noRoot_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma noQuad_cert : ∀ u : ℕ, u < 73 → ∀ v : ℕ, v < 73 →
    ¬ (((u : ℤ) * ((7816999697067374824780726272) - (v : ℤ) * ((-507315096) - (u : ℤ)) - (u : ℤ) *
      ((-26316207229657439232) - (v : ℤ) - (u : ℤ) * ((-507315096) - (u : ℤ))))
        + (v : ℤ) * ((-26316207229657439232) - (v : ℤ) - (u : ℤ) * ((-507315096) - (u : ℤ))) -
      (93356730870958242939964792647614201856)) % 73 = 0
      ∧ ((v : ℤ) * ((7816999697067374824780726272) - (v : ℤ) * ((-507315096) - (u : ℤ)) - (u : ℤ)
      * ((-26316207229657439232) - (v : ℤ) - (u : ℤ) * ((-507315096) - (u : ℤ)))) -
      (59899702063757157544982491709928053576589901824)) % 73 = 0) := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 73,
    ¬ (u * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u)))
        + v * (r3 - v - u * (r4 - u)) = r1
      ∧ v * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u))) = r0) := by
  rintro u v ⟨h1, h2⟩
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq u
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq v
  simp only [r4, r3, r2, r1] at h1
  push_cast at h1
  simp only [r4, r3, r2, r0] at h2
  push_cast at h2
  refine noQuad_cert y hy z hz
    ⟨HornerCert.emod_eq_zero_of_cast ?_, HornerCert.emod_eq_zero_of_cast ?_⟩
  · push_cast
    linear_combination h1
  · push_cast
    linear_combination h2

/-- **Maeda's conjecture in weight 64** (irreducibility): the characteristic
polynomial of `T₂` on `S_64(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 73). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  exact irreducible_quintic_of_mod (by unfold P; monicity!) 73 r4 r3 r2 r1 r0
    (by simp [P, r4, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight64

/-! ### Weight 66 (dim 5) -/

namespace MaedaWeight66

/-- `Δ^1 E₄^12 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((66 : ℕ) : ℤ) :=
  prodForm _ 0 12 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 12 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1c : seqPLc 0 12 1 11 =
    [0, 1, 2352, 2302596,
     1076668672, 66985254150, -232761990374208, -165707527363458808,
     -64978382303927685120, -17328424302261983568627, -3341328926810119418239200] := by
  decide +kernel

lemma L1 : seqPL 0 12 1 11 =
    [0, 1, 2352, 2302596,
     1076668672, 66985254150, -232761990374208, -165707527363458808,
     -64978382303927685120, -17328424302261983568627, -3341328926810119418239200] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L1c

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (2352 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (2302596 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (1076668672 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_5 : (qExpansion 1 f1).coeff 5 = (66985254150 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-232761990374208 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (-64978382303927685120 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_10 : (qExpansion 1 f1).coeff 10 = (-3341328926810119418239200 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^9 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((66 : ℕ) : ℤ) :=
  prodForm _ 1 9 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 9 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2c : seqPLc 1 9 1 11 =
    [0, 0, 1, 1608,
     909360, 62021600, -193623516540, -121872760564464,
     -39064746818471680, -7830272765877727680, -1026190649656189453050] := by
  decide +kernel

lemma L2 : seqPL 1 9 1 11 =
    [0, 0, 1, 1608,
     909360, 62021600, -193623516540, -121872760564464,
     -39064746818471680, -7830272765877727680, -1026190649656189453050] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L2c

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (1608 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (909360 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_5 : (qExpansion 1 f2).coeff 5 = (62021600 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-193623516540 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (-39064746818471680 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_10 : (qExpansion 1 f2).coeff 10 = (-1026190649656189453050 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^6 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((66 : ℕ) : ℤ) :=
  prodForm _ 2 6 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 6 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3c : seqPLc 2 6 1 11 =
    [0, 0, 0, 1,
     864, 69660, -181406976, -91806574446,
     -20116794465792, -2201520886582392, -103310208629959680] := by
  decide +kernel

lemma L3 : seqPL 2 6 1 11 =
    [0, 0, 0, 1,
     864, 69660, -181406976, -91806574446,
     -20116794465792, -2201520886582392, -103310208629959680] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L3c

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (864 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_5 : (qExpansion 1 f3).coeff 5 = (69660 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-181406976 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (-20116794465792 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_10 : (qExpansion 1 f3).coeff 10 = (-103310208629959680 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^3 E₆^1`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((66 : ℕ) : ℤ) :=
  prodForm _ 3 3 1 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 3 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4c : seqPLc 3 3 1 11 =
    [0, 0, 0, 0,
     1, 120, -216504, -65447840,
     -3930759120, 222846012432, -2332880457760] := by
  decide +kernel

lemma L4 : seqPL 3 3 1 11 =
    [0, 0, 0, 0,
     1, 120, -216504, -65447840,
     -3930759120, 222846012432, -2332880457760] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L4c

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_5 : (qExpansion 1 f4).coeff 5 = (120 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (-216504 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (-3930759120 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_10 : (qExpansion 1 f4).coeff 10 = (-2332880457760 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^5 E₄^0 E₆^1`. -/
noncomputable def f5 : CuspForm 𝒮ℒ ((66 : ℕ) : ℤ) :=
  prodForm _ 4 0 1 (by norm_num)

lemma c5 (n : ℕ) : (qExpansion 1 f5).coeff n = seqP 4 0 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L5c : seqPLc 4 0 1 11 =
    [0, 0, 0, 0,
     0, 1, -624, 50868,
     -1931776, 39193182, -245187648] := by
  decide +kernel

lemma L5 : seqPL 4 0 1 11 =
    [0, 0, 0, 0,
     0, 1, -624, 50868,
     -1931776, 39193182, -245187648] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L5c

lemma q5_1 : (qExpansion 1 f5).coeff 1 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_2 : (qExpansion 1 f5).coeff 2 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_3 : (qExpansion 1 f5).coeff 3 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_4 : (qExpansion 1 f5).coeff 4 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_5 : (qExpansion 1 f5).coeff 5 = (1 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_6 : (qExpansion 1 f5).coeff 6 = (-624 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_8 : (qExpansion 1 f5).coeff 8 = (-1931776 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_10 : (qExpansion 1 f5).coeff 10 = (-245187648 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((66 : ℕ) : ℤ)) = 5 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 54 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_66`. -/
noncomputable def T2 := heckeTPₗ ((66 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (2352 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (36893488148495771904 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-232761990374208 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (86708505740425803116544 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t1_5 : (qExpansion 1 (T2 f1)).coeff 5 = (-3341328926810119418239200 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_10]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (909360 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-193623516540 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (36854423400600631552 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t2_5 : (qExpansion 1 (T2 f2)).coeff 5 = (-1026190649656189453050 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_10]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (864 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-181406976 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (-20116794465792 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t3_5 : (qExpansion 1 (T2 f3)).coeff 5 = (-103310208629959680 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_10]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (-216504 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (-3930759120 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

lemma t4_5 : (qExpansion 1 (T2 f4)).coeff 5 = (-2332880457760 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_10]

lemma t5_1 : (qExpansion 1 (T2 f5)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_2]

lemma t5_2 : (qExpansion 1 (T2 f5)).coeff 2 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_4, q5_1]

lemma t5_3 : (qExpansion 1 (T2 f5)).coeff 3 = (-624 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_6]

lemma t5_4 : (qExpansion 1 (T2 f5)).coeff 4 = (-1931776 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_8, q5_2]

lemma t5_5 : (qExpansion 1 (T2 f5)).coeff 5 = (-245187648 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_10]

/-- The integer characteristic polynomial of `T₂` on `S_66`. -/
noncomputable def P : ℤ[X] :=
  X ^ 5
    + C (3959709648) * X ^ 4
    + C (-142850166119005483008) * X ^ 3
    + C (-339986038308627409973683421184) * X ^ 2
    + C (4888759358323485530147825225712235708416) * X
    + C (6737365607750178848535412403321340119893376237568)

/-- **The characteristic polynomial of `T₂` on `S_66`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim5 finrank_eq f1 f2 f3 f4 f5
    q1_1 q1_2 q1_3 q1_4 q1_5 q2_1 q2_2 q2_3 q2_4 q2_5 q3_1 q3_2 q3_3
    q3_4 q3_5 q4_1 q4_2 q4_3 q4_4 q4_5 q5_1 q5_2 q5_3 q5_4 q5_5 T2
    t1_1 t1_2 t1_3 t1_4 t1_5 t2_1 t2_2 t2_3 t2_4 t2_5 t3_1 t3_2 t3_3
    t3_4 t3_5 t4_1 t4_2 t4_3 t4_4 t4_5 t5_1 t5_2 t5_3 t5_4 t5_5, charpoly_fin_five]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 79. -/
def r4 : ZMod 79 := ((3959709648 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r3 : ZMod 79 := ((-142850166119005483008 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r2 : ZMod 79 := ((-339986038308627409973683421184 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r1 : ZMod 79 := ((4888759358323485530147825225712235708416 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r0 : ZMod 79 := ((6737365607750178848535412403321340119893376237568 : ℤ) : ZMod 79)

lemma noRoot_cert : ∀ x : ℕ, x < 79 →
    ((x : ℤ) ^ 5 + (3959709648) * (x : ℤ) ^ 4 + (-142850166119005483008) * (x : ℤ) ^ 3 +
      (-339986038308627409973683421184) * (x : ℤ) ^ 2
      + (4888759358323485530147825225712235708416) * (x : ℤ) +
      (6737365607750178848535412403321340119893376237568)) % 79 ≠ 0 := by
  decide +kernel

lemma noRoot : ∀ x : ZMod 79,
    x ^ 5 + r4 * x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  simp only [r4, r3, r2, r1, r0] at h1
  push_cast at h1
  refine noRoot_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma noQuad_cert : ∀ u : ℕ, u < 79 → ∀ v : ℕ, v < 79 →
    ¬ (((u : ℤ) * ((-339986038308627409973683421184) - (v : ℤ) * ((3959709648) - (u : ℤ)) - (u :
      ℤ) * ((-142850166119005483008) - (v : ℤ) - (u : ℤ) * ((3959709648) - (u : ℤ))))
        + (v : ℤ) * ((-142850166119005483008) - (v : ℤ) - (u : ℤ) * ((3959709648) - (u : ℤ))) -
      (4888759358323485530147825225712235708416)) % 79 = 0
      ∧ ((v : ℤ) * ((-339986038308627409973683421184) - (v : ℤ) * ((3959709648) - (u : ℤ)) - (u :
      ℤ) * ((-142850166119005483008) - (v : ℤ) - (u : ℤ) * ((3959709648) - (u : ℤ)))) -
      (6737365607750178848535412403321340119893376237568)) % 79 = 0) := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 79,
    ¬ (u * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u)))
        + v * (r3 - v - u * (r4 - u)) = r1
      ∧ v * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u))) = r0) := by
  rintro u v ⟨h1, h2⟩
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq u
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq v
  simp only [r4, r3, r2, r1] at h1
  push_cast at h1
  simp only [r4, r3, r2, r0] at h2
  push_cast at h2
  refine noQuad_cert y hy z hz
    ⟨HornerCert.emod_eq_zero_of_cast ?_, HornerCert.emod_eq_zero_of_cast ?_⟩
  · push_cast
    linear_combination h1
  · push_cast
    linear_combination h2

/-- **Maeda's conjecture in weight 66** (irreducibility): the characteristic
polynomial of `T₂` on `S_66(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 79). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 79) := ⟨by norm_num⟩
  exact irreducible_quintic_of_mod (by unfold P; monicity!) 79 r4 r3 r2 r1 r0
    (by simp [P, r4, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight66

/-! ### Weight 68 (dim 5) -/

namespace MaedaWeight68

/-- `Δ^1 E₄^14 E₆^0`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((68 : ℕ) : ℤ) :=
  prodForm _ 0 14 0 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 14 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1c : seqPLc 0 14 0 11 =
    [0, 1, 3336, 5191452,
     5000699968, 3335948845950, 1633625277211872, 607311921856768856,
     174816931390027645440, 39388684834480281033717, 6976703738092643788489200] := by
  decide +kernel

lemma L1 : seqPL 0 14 0 11 =
    [0, 1, 3336, 5191452,
     5000699968, 3335948845950, 1633625277211872, 607311921856768856,
     174816931390027645440, 39388684834480281033717, 6976703738092643788489200] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L1c

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (3336 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (5191452 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (5000699968 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_5 : (qExpansion 1 f1).coeff 5 = (3335948845950 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (1633625277211872 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (174816931390027645440 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_10 : (qExpansion 1 f1).coeff 10 = (6976703738092643788489200 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^11 E₆^0`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((68 : ℕ) : ℤ) :=
  prodForm _ 1 11 0 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 11 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2c : seqPLc 1 11 0 11 =
    [0, 0, 1, 2592,
     3066120, 2187689600, 1048061687580, 354983343656256,
     87133203776045120, 15618736576491575040, 2032120297292918932350] := by
  decide +kernel

lemma L2 : seqPL 1 11 0 11 =
    [0, 0, 1, 2592,
     3066120, 2187689600, 1048061687580, 354983343656256,
     87133203776045120, 15618736576491575040, 2032120297292918932350] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L2c

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (2592 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (3066120 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_5 : (qExpansion 1 f2).coeff 5 = (2187689600 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (1048061687580 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (87133203776045120 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_10 : (qExpansion 1 f2).coeff 10 = (2032120297292918932350 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^8 E₆^0`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((68 : ℕ) : ℤ) :=
  prodForm _ 2 8 0 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 8 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3c : seqPLc 2 8 0 11 =
    [0, 0, 0, 1,
     1848, 1494324, 690577152, 199479031626,
     36871238513088, 4254381359710776, 278825799490980864] := by
  decide +kernel

lemma L3 : seqPL 2 8 0 11 =
    [0, 0, 0, 1,
     1848, 1494324, 690577152, 199479031626,
     36871238513088, 4254381359710776, 278825799490980864] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L3c

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (1848 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_5 : (qExpansion 1 f3).coeff 5 = (1494324 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (690577152 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (36871238513088 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_10 : (qExpansion 1 f3).coeff 10 = (278825799490980864 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^5 E₆^0`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((68 : ℕ) : ℤ) :=
  prodForm _ 3 5 0 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 5 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4c : seqPLc 3 5 0 11 =
    [0, 0, 0, 0,
     1, 1104, 476064, 97531840,
     8592547080, 69086315232, -19226588304256] := by
  decide +kernel

lemma L4 : seqPL 3 5 0 11 =
    [0, 0, 0, 0,
     1, 1104, 476064, 97531840,
     8592547080, 69086315232, -19226588304256] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L4c

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_5 : (qExpansion 1 f4).coeff 5 = (1104 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (476064 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (8592547080 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_10 : (qExpansion 1 f4).coeff 10 = (-19226588304256 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^5 E₄^2 E₆^0`. -/
noncomputable def f5 : CuspForm 𝒮ℒ ((68 : ℕ) : ℤ) :=
  prodForm _ 4 2 0 (by norm_num)

lemma c5 (n : ℕ) : (qExpansion 1 f5).coeff n = seqP 4 2 0 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L5c : seqPLc 4 2 0 11 =
    [0, 0, 0, 0,
     0, 1, 360, 11340,
     -3277120, 196006230, -6662909664] := by
  decide +kernel

lemma L5 : seqPL 4 2 0 11 =
    [0, 0, 0, 0,
     0, 1, 360, 11340,
     -3277120, 196006230, -6662909664] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L5c

lemma q5_1 : (qExpansion 1 f5).coeff 1 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_2 : (qExpansion 1 f5).coeff 2 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_3 : (qExpansion 1 f5).coeff 3 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_4 : (qExpansion 1 f5).coeff 4 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_5 : (qExpansion 1 f5).coeff 5 = (1 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_6 : (qExpansion 1 f5).coeff 6 = (360 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_8 : (qExpansion 1 f5).coeff 8 = (-3277120 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_10 : (qExpansion 1 f5).coeff 10 = (-6662909664 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((68 : ℕ) : ℤ)) = 5 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 56 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_68`. -/
noncomputable def T2 := heckeTPₗ ((68 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (3336 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (147573952594677112896 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (1633625277211872 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (492481522770550541173248 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t1_5 : (qExpansion 1 (T2 f1)).coeff 5 = (6976703738092643788489200 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_10]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (3066120 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (1048061687580 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (147661085793452458048 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t2_5 : (qExpansion 1 (T2 f2)).coeff 5 = (2032120297292918932350 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_10]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (1848 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (690577152 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (36871238513088 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t3_5 : (qExpansion 1 (T2 f3)).coeff 5 = (278825799490980864 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_10]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (476064 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (8592547080 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

lemma t4_5 : (qExpansion 1 (T2 f4)).coeff 5 = (-19226588304256 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_10]

lemma t5_1 : (qExpansion 1 (T2 f5)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_2]

lemma t5_2 : (qExpansion 1 (T2 f5)).coeff 2 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_4, q5_1]

lemma t5_3 : (qExpansion 1 (T2 f5)).coeff 3 = (360 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_6]

lemma t5_4 : (qExpansion 1 (T2 f5)).coeff 4 = (-3277120 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_8, q5_2]

lemma t5_5 : (qExpansion 1 (T2 f5)).coeff 5 = (-6662909664 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_10]

/-- The integer characteristic polynomial of `T₂` on `S_68`. -/
noncomputable def P : ℤ[X] :=
  X ^ 5
    + C (-5554901256) * X ^ 4
    + C (-528742419683384143872) * X ^ 3
    + C (1360506199877236618906967212032) * X ^ 2
    + C (50978026392314038029857853615859298205696) * X
    + C (-224135116306806567372209572838489759238644853374976)

/-- **The characteristic polynomial of `T₂` on `S_68`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim5 finrank_eq f1 f2 f3 f4 f5
    q1_1 q1_2 q1_3 q1_4 q1_5 q2_1 q2_2 q2_3 q2_4 q2_5 q3_1 q3_2 q3_3
    q3_4 q3_5 q4_1 q4_2 q4_3 q4_4 q4_5 q5_1 q5_2 q5_3 q5_4 q5_5 T2
    t1_1 t1_2 t1_3 t1_4 t1_5 t2_1 t2_2 t2_3 t2_4 t2_5 t3_1 t3_2 t3_3
    t3_4 t3_5 t4_1 t4_2 t4_3 t4_4 t4_5 t5_1 t5_2 t5_3 t5_4 t5_5, charpoly_fin_five]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 97. -/
def r4 : ZMod 97 := ((-5554901256 : ℤ) : ZMod 97)
/-- See `r4`. -/
def r3 : ZMod 97 := ((-528742419683384143872 : ℤ) : ZMod 97)
/-- See `r4`. -/
def r2 : ZMod 97 := ((1360506199877236618906967212032 : ℤ) : ZMod 97)
/-- See `r4`. -/
def r1 : ZMod 97 := ((50978026392314038029857853615859298205696 : ℤ) : ZMod 97)
/-- See `r4`. -/
def r0 : ZMod 97 := ((-224135116306806567372209572838489759238644853374976 : ℤ) : ZMod 97)

lemma noRoot_cert : ∀ x : ℕ, x < 97 →
    ((x : ℤ) ^ 5 + (-5554901256) * (x : ℤ) ^ 4 + (-528742419683384143872) * (x : ℤ) ^ 3 +
      (1360506199877236618906967212032) * (x : ℤ) ^ 2
      + (50978026392314038029857853615859298205696) * (x : ℤ) +
      (-224135116306806567372209572838489759238644853374976)) % 97 ≠ 0 := by
  decide +kernel

lemma noRoot : ∀ x : ZMod 97,
    x ^ 5 + r4 * x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  simp only [r4, r3, r2, r1, r0] at h1
  push_cast at h1
  refine noRoot_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma noQuad_cert : ∀ u : ℕ, u < 97 → ∀ v : ℕ, v < 97 →
    ¬ (((u : ℤ) * ((1360506199877236618906967212032) - (v : ℤ) * ((-5554901256) - (u : ℤ)) - (u :
      ℤ) * ((-528742419683384143872) - (v : ℤ) - (u : ℤ) * ((-5554901256) - (u : ℤ))))
        + (v : ℤ) * ((-528742419683384143872) - (v : ℤ) - (u : ℤ) * ((-5554901256) - (u : ℤ))) -
      (50978026392314038029857853615859298205696)) % 97 = 0
      ∧ ((v : ℤ) * ((1360506199877236618906967212032) - (v : ℤ) * ((-5554901256) - (u : ℤ)) - (u :
      ℤ) * ((-528742419683384143872) - (v : ℤ) - (u : ℤ) * ((-5554901256) - (u : ℤ)))) -
      (-224135116306806567372209572838489759238644853374976)) % 97 = 0) := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 97,
    ¬ (u * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u)))
        + v * (r3 - v - u * (r4 - u)) = r1
      ∧ v * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u))) = r0) := by
  rintro u v ⟨h1, h2⟩
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq u
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq v
  simp only [r4, r3, r2, r1] at h1
  push_cast at h1
  simp only [r4, r3, r2, r0] at h2
  push_cast at h2
  refine noQuad_cert y hy z hz
    ⟨HornerCert.emod_eq_zero_of_cast ?_, HornerCert.emod_eq_zero_of_cast ?_⟩
  · push_cast
    linear_combination h1
  · push_cast
    linear_combination h2

/-- **Maeda's conjecture in weight 68** (irreducibility): the characteristic
polynomial of `T₂` on `S_68(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 97). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact irreducible_quintic_of_mod (by unfold P; monicity!) 97 r4 r3 r2 r1 r0
    (by simp [P, r4, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight68

/-! ### Weight 70 (dim 5) -/

namespace MaedaWeight70

/-- `Δ^1 E₄^13 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((70 : ℕ) : ℤ) :=
  prodForm _ 0 13 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 13 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1c : seqPLc 0 13 1 11 =
    [0, 1, 2592, 2869236,
     1634378752, 330375165750, -214344410364288, -221418441278162008,
     -105250485696450232320, -33282727268605445023587, -7641621695612491634376000] := by
  decide +kernel

lemma L1 : seqPL 0 13 1 11 =
    [0, 1, 2592, 2869236,
     1634378752, 330375165750, -214344410364288, -221418441278162008,
     -105250485696450232320, -33282727268605445023587, -7641621695612491634376000] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L1c

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (2592 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (2869236 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (1634378752 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_5 : (qExpansion 1 f1).coeff 5 = (330375165750 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-214344410364288 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (-105250485696450232320 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_10 : (qExpansion 1 f1).coeff 10 = (-7641621695612491634376000 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^10 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((70 : ℕ) : ℤ) :=
  prodForm _ 1 10 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 10 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2c : seqPLc 1 10 1 11 =
    [0, 0, 1, 1848,
     1297440, 283748000, -176763291660, -168202298776464,
     -68732003383843840, -17470357200946509120, -2990658341899081730250] := by
  decide +kernel

lemma L2 : seqPL 1 10 1 11 =
    [0, 0, 1, 1848,
     1297440, 283748000, -176763291660, -168202298776464,
     -68732003383843840, -17470357200946509120, -2990658341899081730250] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L2c

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (1848 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (1297440 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_5 : (qExpansion 1 f2).coeff 5 = (283748000 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-176763291660 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (-68732003383843840 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_10 : (qExpansion 1 f2).coeff 10 = (-2990658341899081730250 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^7 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((70 : ℕ) : ℤ) :=
  prodForm _ 2 7 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 7 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3c : seqPLc 2 7 1 11 =
    [0, 0, 0, 1,
     1104, 279180, -162815616, -135187959486,
     -42541728118272, -7229071567423512, -675747613727485440] := by
  decide +kernel

lemma L3 : seqPL 2 7 1 11 =
    [0, 0, 0, 1,
     1104, 279180, -162815616, -135187959486,
     -42541728118272, -7229071567423512, -675747613727485440] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L3c

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (1104 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_5 : (qExpansion 1 f3).coeff 5 = (279180 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-162815616 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (-42541728118272 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_10 : (qExpansion 1 f3).coeff 10 = (-675747613727485440 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^4 E₆^1`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((70 : ℕ) : ℤ) :=
  prodForm _ 3 4 1 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 4 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4c : seqPLc 3 4 1 11 =
    [0, 0, 0, 0,
     1, 360, -185544, -117142880,
     -20105065440, -863356285008, 42216123881120] := by
  decide +kernel

lemma L4 : seqPL 3 4 1 11 =
    [0, 0, 0, 0,
     1, 360, -185544, -117142880,
     -20105065440, -863356285008, 42216123881120] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L4c

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_5 : (qExpansion 1 f4).coeff 5 = (360 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (-185544 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (-20105065440 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_10 : (qExpansion 1 f4).coeff 10 = (42216123881120 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^5 E₄^1 E₆^1`. -/
noncomputable def f5 : CuspForm 𝒮ℒ ((70 : ℕ) : ℤ) :=
  prodForm _ 4 1 1 (by norm_num)

lemma c5 (n : ℕ) : (qExpansion 1 f5).coeff n = seqP 4 1 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L5c : seqPLc 4 1 1 11 =
    [0, 0, 0, 0,
     0, 1, -384, -96732,
     8935424, -318733938, 5319470592] := by
  decide +kernel

lemma L5 : seqPL 4 1 1 11 =
    [0, 0, 0, 0,
     0, 1, -384, -96732,
     8935424, -318733938, 5319470592] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L5c

lemma q5_1 : (qExpansion 1 f5).coeff 1 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_2 : (qExpansion 1 f5).coeff 2 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_3 : (qExpansion 1 f5).coeff 3 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_4 : (qExpansion 1 f5).coeff 4 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_5 : (qExpansion 1 f5).coeff 5 = (1 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_6 : (qExpansion 1 f5).coeff 6 = (-384 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_8 : (qExpansion 1 f5).coeff 8 = (8935424 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_10 : (qExpansion 1 f5).coeff 10 = (5319470592 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((70 : ℕ) : ℤ)) = 5 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 58 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_70`. -/
noncomputable def T2 := heckeTPₗ ((70 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (2592 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (590295810360340030464 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-214344410364288 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (1529941489964068599005184 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t1_5 : (qExpansion 1 (T2 f1)).coeff 5 = (-7641621695612491634376000 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_10]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (1297440 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-176763291660 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (590227078355321807872 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t2_5 : (qExpansion 1 (T2 f2)).coeff 5 = (-2990658341899081730250 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_10]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (1104 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-162815616 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (-42541728118272 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t3_5 : (qExpansion 1 (T2 f3)).coeff 5 = (-675747613727485440 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_10]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (-185544 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (-20105065440 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

lemma t4_5 : (qExpansion 1 (T2 f4)).coeff 5 = (42216123881120 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_10]

lemma t5_1 : (qExpansion 1 (T2 f5)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_2]

lemma t5_2 : (qExpansion 1 (T2 f5)).coeff 2 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_4, q5_1]

lemma t5_3 : (qExpansion 1 (T2 f5)).coeff 3 = (-384 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_6]

lemma t5_4 : (qExpansion 1 (T2 f5)).coeff 4 = (8935424 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_8, q5_2]

lemma t5_5 : (qExpansion 1 (T2 f5)).coeff 5 = (5319470592 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_10]

/-- The integer characteristic polynomial of `T₂` on `S_70`. -/
noncomputable def P : ℤ[X] :=
  X ^ 5
    + C (18005734368) * X ^ 4
    + C (-1942747456996431618048) * X ^ 3
    + C (-14539211744046993293953166475264) * X ^ 2
    + C (613518461067953168654246762332094963122176) * X
    + C (4169744246282611427836654706819235757668276180615168)

/-- **The characteristic polynomial of `T₂` on `S_70`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim5 finrank_eq f1 f2 f3 f4 f5
    q1_1 q1_2 q1_3 q1_4 q1_5 q2_1 q2_2 q2_3 q2_4 q2_5 q3_1 q3_2 q3_3
    q3_4 q3_5 q4_1 q4_2 q4_3 q4_4 q4_5 q5_1 q5_2 q5_3 q5_4 q5_5 T2
    t1_1 t1_2 t1_3 t1_4 t1_5 t2_1 t2_2 t2_3 t2_4 t2_5 t3_1 t3_2 t3_3
    t3_4 t3_5 t4_1 t4_2 t4_3 t4_4 t4_5 t5_1 t5_2 t5_3 t5_4 t5_5, charpoly_fin_five]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 79. -/
def r4 : ZMod 79 := ((18005734368 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r3 : ZMod 79 := ((-1942747456996431618048 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r2 : ZMod 79 := ((-14539211744046993293953166475264 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r1 : ZMod 79 := ((613518461067953168654246762332094963122176 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r0 : ZMod 79 := ((4169744246282611427836654706819235757668276180615168 : ℤ) : ZMod 79)

lemma noRoot_cert : ∀ x : ℕ, x < 79 →
    ((x : ℤ) ^ 5 + (18005734368) * (x : ℤ) ^ 4 + (-1942747456996431618048) * (x : ℤ) ^ 3 +
      (-14539211744046993293953166475264) * (x : ℤ) ^ 2
      + (613518461067953168654246762332094963122176) * (x : ℤ) +
      (4169744246282611427836654706819235757668276180615168)) % 79 ≠ 0 := by
  decide +kernel

lemma noRoot : ∀ x : ZMod 79,
    x ^ 5 + r4 * x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  simp only [r4, r3, r2, r1, r0] at h1
  push_cast at h1
  refine noRoot_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma noQuad_cert : ∀ u : ℕ, u < 79 → ∀ v : ℕ, v < 79 →
    ¬ (((u : ℤ) * ((-14539211744046993293953166475264) - (v : ℤ) * ((18005734368) - (u : ℤ)) - (u
      : ℤ) * ((-1942747456996431618048) - (v : ℤ) - (u : ℤ) * ((18005734368) - (u : ℤ))))
        + (v : ℤ) * ((-1942747456996431618048) - (v : ℤ) - (u : ℤ) * ((18005734368) - (u : ℤ))) -
      (613518461067953168654246762332094963122176)) % 79 = 0
      ∧ ((v : ℤ) * ((-14539211744046993293953166475264) - (v : ℤ) * ((18005734368) - (u : ℤ)) - (u
      : ℤ) * ((-1942747456996431618048) - (v : ℤ) - (u : ℤ) * ((18005734368) - (u : ℤ)))) -
      (4169744246282611427836654706819235757668276180615168)) % 79 = 0) := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 79,
    ¬ (u * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u)))
        + v * (r3 - v - u * (r4 - u)) = r1
      ∧ v * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u))) = r0) := by
  rintro u v ⟨h1, h2⟩
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq u
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq v
  simp only [r4, r3, r2, r1] at h1
  push_cast at h1
  simp only [r4, r3, r2, r0] at h2
  push_cast at h2
  refine noQuad_cert y hy z hz
    ⟨HornerCert.emod_eq_zero_of_cast ?_, HornerCert.emod_eq_zero_of_cast ?_⟩
  · push_cast
    linear_combination h1
  · push_cast
    linear_combination h2

/-- **Maeda's conjecture in weight 70** (irreducibility): the characteristic
polynomial of `T₂` on `S_70(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 79). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 79) := ⟨by norm_num⟩
  exact irreducible_quintic_of_mod (by unfold P; monicity!) 79 r4 r3 r2 r1 r0
    (by simp [P, r4, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight70

/-! ### Weight 74 (dim 5) -/

namespace MaedaWeight74

/-- `Δ^1 E₄^14 E₆^1`. -/
noncomputable def f1 : CuspForm 𝒮ℒ ((74 : ℕ) : ℤ) :=
  prodForm _ 0 14 1 (by norm_num)

lemma c1 (n : ℕ) : (qExpansion 1 f1).coeff n = seqP 0 14 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L1c : seqPLc 0 14 1 11 =
    [0, 1, 2832, 3493476,
     2328600832, 728841051750, -131504785771968, -272136456034900408,
     -158851646687243857920, -59022542225581715803347, -15858308966331960285444000] := by
  decide +kernel

lemma L1 : seqPL 0 14 1 11 =
    [0, 1, 2832, 3493476,
     2328600832, 728841051750, -131504785771968, -272136456034900408,
     -158851646687243857920, -59022542225581715803347, -15858308966331960285444000] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L1c

lemma q1_1 : (qExpansion 1 f1).coeff 1 = (1 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_2 : (qExpansion 1 f1).coeff 2 = (2832 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_3 : (qExpansion 1 f1).coeff 3 = (3493476 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_4 : (qExpansion 1 f1).coeff 4 = (2328600832 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_5 : (qExpansion 1 f1).coeff 5 = (728841051750 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_6 : (qExpansion 1 f1).coeff 6 = (-131504785771968 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_8 : (qExpansion 1 f1).coeff 8 = (-158851646687243857920 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q1_10 : (qExpansion 1 f1).coeff 10 = (-15858308966331960285444000 : ℂ) := by
  rw [c1, seqP_getD (N := 11) (by norm_num), L1]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^2 E₄^11 E₆^1`. -/
noncomputable def f2 : CuspForm 𝒮ℒ ((74 : ℕ) : ℤ) :=
  prodForm _ 1 11 1 (by norm_num)

lemma c2 (n : ℕ) : (qExpansion 1 f2).coeff n = seqP 1 11 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L2c : seqPLc 1 11 1 11 =
    [0, 0, 1, 2088,
     1743120, 599132000, -105848865180, -210003841890864,
     -109480434226528000, -34330537817134752960, -7333138605116832932250] := by
  decide +kernel

lemma L2 : seqPL 1 11 1 11 =
    [0, 0, 1, 2088,
     1743120, 599132000, -105848865180, -210003841890864,
     -109480434226528000, -34330537817134752960, -7333138605116832932250] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L2c

lemma q2_1 : (qExpansion 1 f2).coeff 1 = (0 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_2 : (qExpansion 1 f2).coeff 2 = (1 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_3 : (qExpansion 1 f2).coeff 3 = (2088 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_4 : (qExpansion 1 f2).coeff 4 = (1743120 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_5 : (qExpansion 1 f2).coeff 5 = (599132000 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_6 : (qExpansion 1 f2).coeff 6 = (-105848865180 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_8 : (qExpansion 1 f2).coeff 8 = (-109480434226528000 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q2_10 : (qExpansion 1 f2).coeff 10 = (-7333138605116832932250 : ℂ) := by
  rw [c2, seqP_getD (N := 11) (by norm_num), L2]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^3 E₄^8 E₆^1`. -/
noncomputable def f3 : CuspForm 𝒮ℒ ((74 : ℕ) : ℤ) :=
  prodForm _ 2 8 1 (by norm_num)

lemma c3 (n : ℕ) : (qExpansion 1 f3).coeff n = seqP 2 8 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L3c : seqPLc 2 8 1 11 =
    [0, 0, 0, 1,
     1344, 546300, -93421056, -173653242126,
     -75336624663552, -17732181504559032, -2503526229752678400] := by
  decide +kernel

lemma L3 : seqPL 2 8 1 11 =
    [0, 0, 0, 1,
     1344, 546300, -93421056, -173653242126,
     -75336624663552, -17732181504559032, -2503526229752678400] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L3c

lemma q3_1 : (qExpansion 1 f3).coeff 1 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_2 : (qExpansion 1 f3).coeff 2 = (0 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_3 : (qExpansion 1 f3).coeff 3 = (1 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_4 : (qExpansion 1 f3).coeff 4 = (1344 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_5 : (qExpansion 1 f3).coeff 5 = (546300 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_6 : (qExpansion 1 f3).coeff 6 = (-93421056 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_8 : (qExpansion 1 f3).coeff 8 = (-75336624663552 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q3_10 : (qExpansion 1 f3).coeff 10 = (-2503526229752678400 : ℂ) := by
  rw [c3, seqP_getD (N := 11) (by norm_num), L3]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^4 E₄^5 E₆^1`. -/
noncomputable def f4 : CuspForm 𝒮ℒ ((74 : ℕ) : ℤ) :=
  prodForm _ 3 5 1 (by norm_num)

lemma c4 (n : ℕ) : (qExpansion 1 f4).coeff n = seqP 3 5 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L4c : seqPLc 3 5 1 11 =
    [0, 0, 0, 0,
     1, 600, -96984, -160889120,
     -48617694960, -5942841129648, -209206765808800] := by
  decide +kernel

lemma L4 : seqPL 3 5 1 11 =
    [0, 0, 0, 0,
     1, 600, -96984, -160889120,
     -48617694960, -5942841129648, -209206765808800] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L4c

lemma q4_1 : (qExpansion 1 f4).coeff 1 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_2 : (qExpansion 1 f4).coeff 2 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_3 : (qExpansion 1 f4).coeff 3 = (0 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_4 : (qExpansion 1 f4).coeff 4 = (1 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_5 : (qExpansion 1 f4).coeff 5 = (600 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_6 : (qExpansion 1 f4).coeff 6 = (-96984 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_8 : (qExpansion 1 f4).coeff 8 = (-48617694960 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q4_10 : (qExpansion 1 f4).coeff 10 = (-209206765808800 : ℂ) := by
  rw [c4, seqP_getD (N := 11) (by norm_num), L4]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

/-- `Δ^5 E₄^2 E₆^1`. -/
noncomputable def f5 : CuspForm 𝒮ℒ ((74 : ℕ) : ℤ) :=
  prodForm _ 4 2 1 (by norm_num)

lemma c5 (n : ℕ) : (qExpansion 1 f5).coeff n = seqP 4 2 1 n :=
  prodForm_coeff _ _ _ _ _ n

lemma L5c : seqPLc 4 2 1 11 =
    [0, 0, 0, 0,
     0, 1, -144, -186732,
     -15102976, 1614263742, -52532895168] := by
  decide +kernel

lemma L5 : seqPL 4 2 1 11 =
    [0, 0, 0, 0,
     0, 1, -144, -186732,
     -15102976, 1614263742, -52532895168] := by
  rw [← seqPLc_eq (by norm_num)]
  exact L5c

lemma q5_1 : (qExpansion 1 f5).coeff 1 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_2 : (qExpansion 1 f5).coeff 2 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_3 : (qExpansion 1 f5).coeff 3 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_4 : (qExpansion 1 f5).coeff 4 = (0 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_5 : (qExpansion 1 f5).coeff 5 = (1 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_6 : (qExpansion 1 f5).coeff 6 = (-144 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_8 : (qExpansion 1 f5).coeff 8 = (-15102976 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma q5_10 : (qExpansion 1 f5).coeff 10 = (-52532895168 : ℂ) := by
  rw [c5, seqP_getD (N := 11) (by norm_num), L5]
  norm_num [List.getD_cons_succ, List.getD_cons_zero]

lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ ((74 : ℕ) : ℤ)) = 5 := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 62 (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h

/-- `T₂` on `S_74`. -/
noncomputable def T2 := heckeTPₗ ((74 : ℕ) : ℤ) Nat.prime_two

lemma t1_1 : (qExpansion 1 (T2 f1)).coeff 1 = (2832 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_2]

lemma t1_2 : (qExpansion 1 (T2 f1)).coeff 2 = (9444732965741619028224 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_4, q1_1]

lemma t1_3 : (qExpansion 1 (T2 f1)).coeff 3 = (-131504785771968 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_6]

lemma t1_4 : (qExpansion 1 (T2 f1)).coeff 4 = (26747324907326983246516224 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_8, q1_2]

lemma t1_5 : (qExpansion 1 (T2 f1)).coeff 5 = (-15858308966331960285444000 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q1_10]

lemma t2_1 : (qExpansion 1 (T2 f2)).coeff 1 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_2]

lemma t2_2 : (qExpansion 1 (T2 f2)).coeff 2 = (1743120 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_4, q2_1]

lemma t2_3 : (qExpansion 1 (T2 f2)).coeff 3 = (-105848865180 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_6]

lemma t2_4 : (qExpansion 1 (T2 f2)).coeff 4 = (9444623485305063899392 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_8, q2_2]

lemma t2_5 : (qExpansion 1 (T2 f2)).coeff 5 = (-7333138605116832932250 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q2_10]

lemma t3_1 : (qExpansion 1 (T2 f3)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_2]

lemma t3_2 : (qExpansion 1 (T2 f3)).coeff 2 = (1344 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_4, q3_1]

lemma t3_3 : (qExpansion 1 (T2 f3)).coeff 3 = (-93421056 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_6]

lemma t3_4 : (qExpansion 1 (T2 f3)).coeff 4 = (-75336624663552 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_8, q3_2]

lemma t3_5 : (qExpansion 1 (T2 f3)).coeff 5 = (-2503526229752678400 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q3_10]

lemma t4_1 : (qExpansion 1 (T2 f4)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_2]

lemma t4_2 : (qExpansion 1 (T2 f4)).coeff 2 = (1 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_4, q4_1]

lemma t4_3 : (qExpansion 1 (T2 f4)).coeff 3 = (-96984 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_6]

lemma t4_4 : (qExpansion 1 (T2 f4)).coeff 4 = (-48617694960 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_8, q4_2]

lemma t4_5 : (qExpansion 1 (T2 f4)).coeff 5 = (-209206765808800 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q4_10]

lemma t5_1 : (qExpansion 1 (T2 f5)).coeff 1 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_2]

lemma t5_2 : (qExpansion 1 (T2 f5)).coeff 2 = (0 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_4, q5_1]

lemma t5_3 : (qExpansion 1 (T2 f5)).coeff 3 = (-144 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_6]

lemma t5_4 : (qExpansion 1 (T2 f5)).coeff 4 = (-15102976 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_8, q5_2]

lemma t5_5 : (qExpansion 1 (T2 f5)).coeff 5 = (-52532895168 : ℂ) := by
  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [q5_10]

/-- The integer characteristic polynomial of `T₂` on `S_74`. -/
noncomputable def P : ℤ[X] :=
  X ^ 5
    + C (92089333488) * X ^ 4
    + C (-19817164982845968703488) * X ^ 3
    + C (-1377989142595747748686715833810944) * X ^ 2
    + C (11802708847432637761332792635527627366465536) * X
    + C (113628227457643966226006850359168010340399423074336768)

/-- **The characteristic polynomial of `T₂` on `S_74`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim5 finrank_eq f1 f2 f3 f4 f5
    q1_1 q1_2 q1_3 q1_4 q1_5 q2_1 q2_2 q2_3 q2_4 q2_5 q3_1 q3_2 q3_3
    q3_4 q3_5 q4_1 q4_2 q4_3 q4_4 q4_5 q5_1 q5_2 q5_3 q5_4 q5_5 T2
    t1_1 t1_2 t1_3 t1_4 t1_5 t2_1 t2_2 t2_3 t2_4 t2_5 t3_1 t3_2 t3_3
    t3_4 t3_5 t4_1 t4_2 t4_3 t4_4 t4_5 t5_1 t5_2 t5_3 t5_4 t5_5, charpoly_fin_five]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo 79. -/
def r4 : ZMod 79 := ((92089333488 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r3 : ZMod 79 := ((-19817164982845968703488 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r2 : ZMod 79 := ((-1377989142595747748686715833810944 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r1 : ZMod 79 := ((11802708847432637761332792635527627366465536 : ℤ) : ZMod 79)
/-- See `r4`. -/
def r0 : ZMod 79 := ((113628227457643966226006850359168010340399423074336768 : ℤ) : ZMod 79)

lemma noRoot_cert : ∀ x : ℕ, x < 79 →
    ((x : ℤ) ^ 5 + (92089333488) * (x : ℤ) ^ 4 + (-19817164982845968703488) * (x : ℤ) ^ 3 +
      (-1377989142595747748686715833810944) * (x : ℤ) ^ 2
      + (11802708847432637761332792635527627366465536) * (x : ℤ) +
      (113628227457643966226006850359168010340399423074336768)) % 79 ≠ 0 := by
  decide +kernel

lemma noRoot : ∀ x : ZMod 79,
    x ^ 5 + r4 * x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0 := by
  intro x h1
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq x
  simp only [r4, r3, r2, r1, r0] at h1
  push_cast at h1
  refine noRoot_cert y hy (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma noQuad_cert : ∀ u : ℕ, u < 79 → ∀ v : ℕ, v < 79 →
    ¬ (((u : ℤ) * ((-1377989142595747748686715833810944) - (v : ℤ) * ((92089333488) - (u : ℤ)) -
      (u : ℤ) * ((-19817164982845968703488) - (v : ℤ) - (u : ℤ) * ((92089333488) - (u : ℤ))))
        + (v : ℤ) * ((-19817164982845968703488) - (v : ℤ) - (u : ℤ) * ((92089333488) - (u : ℤ))) -
      (11802708847432637761332792635527627366465536)) % 79 = 0
      ∧ ((v : ℤ) * ((-1377989142595747748686715833810944) - (v : ℤ) * ((92089333488) - (u : ℤ)) -
      (u : ℤ) * ((-19817164982845968703488) - (v : ℤ) - (u : ℤ) * ((92089333488) - (u : ℤ)))) -
      (113628227457643966226006850359168010340399423074336768)) % 79 = 0) := by
  decide +kernel

lemma noQuad : ∀ u v : ZMod 79,
    ¬ (u * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u)))
        + v * (r3 - v - u * (r4 - u)) = r1
      ∧ v * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u))) = r0) := by
  rintro u v ⟨h1, h2⟩
  obtain ⟨y, hy, rfl⟩ := HornerCert.exists_natCast_eq u
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq v
  simp only [r4, r3, r2, r1] at h1
  push_cast at h1
  simp only [r4, r3, r2, r0] at h2
  push_cast at h2
  refine noQuad_cert y hy z hz
    ⟨HornerCert.emod_eq_zero_of_cast ?_, HornerCert.emod_eq_zero_of_cast ?_⟩
  · push_cast
    linear_combination h1
  · push_cast
    linear_combination h2

/-- **Maeda's conjecture in weight 74** (irreducibility): the characteristic
polynomial of `T₂` on `S_74(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod 79). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 79) := ⟨by norm_num⟩
  exact irreducible_quintic_of_mod (by unfold P; monicity!) 79 r4 r3 r2 r1 r0
    (by simp [P, r4, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight74

