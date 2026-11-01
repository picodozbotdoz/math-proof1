import MathProof.ModularForms.CharpolyDimN

namespace S4Staged

open MaedaLevelOne

def Atab : ℕ → ℕ → ℂ
  | 0, 1 => (3576 : ℂ)
  | 0, 2 => (5994252 : ℂ)
  | 0, 3 => (6253860928 : ℂ)
  | 0, 4 => (4547352810030 : ℂ)
  | 0, 5 => (2445089457205152 : ℂ)
  | 1, 2 => (2832 : ℂ)
  | 1, 3 => (3690360 : ℂ)
  | 1, 4 => (2929163840 : ℂ)
  | 1, 5 => (1579747446540 : ℂ)
  | 2, 3 => (2088 : ℂ)
  | 2, 4 => (1940004 : ℂ)
  | 2, 5 => (1053213312 : ℂ)
  | 3, 4 => (1344 : ℂ)
  | 3, 5 => (743184 : ℂ)
  | 4, 5 => (600 : ℂ)
  | _, _ => 0

def Xtab : ℕ → ℕ → ℂ
  | 0, 0 => (3576 : ℂ)
  | 0, 1 => (2361183241441076467776 : ℂ)
  | 0, 2 => (2445089457205152 : ℂ)
  | 0, 3 => (8443915394299505771478528 : ℂ)
  | 0, 4 => (16811702528582069699867280 : ℂ)
  | 0, 5 => (367927583598383519126792823552 : ℂ)
  | 1, 0 => (1 : ℂ)
  | 1, 1 => (3690360 : ℂ)
  | 1, 2 => (1579747446540 : ℂ)
  | 1, 3 => (2361357849209392303168 : ℂ)
  | 1, 4 => (5971228712258677420590 : ℂ)
  | 1, 5 => (68293583673210795775492512 : ℂ)
  | 2, 0 => (0 : ℂ)
  | 2, 1 => (2088 : ℂ)
  | 2, 2 => (1053213312 : ℂ)
  | 2, 3 => (86247927016128 : ℂ)
  | 2, 4 => (1380871844314274304 : ℂ)
  | 2, 5 => (4785804492897672149472 : ℂ)
  | 3, 0 => (0 : ℂ)
  | 3, 1 => (1 : ℂ)
  | 3, 2 => (743184 : ℂ)
  | 3, 3 => (48189551417344 : ℂ)
  | 3, 4 => (27177852984371840 : ℂ)
  | 3, 5 => (733833553621726720 : ℂ)
  | 4, 0 => (0 : ℂ)
  | 4, 1 => (0 : ℂ)
  | 4, 2 => (600 : ℂ)
  | 4, 3 => (1024000 : ℂ)
  | 4, 4 => (36879191179264 : ℂ)
  | 4, 5 => (1358954496000 : ℂ)
  | 5, 0 => (0 : ℂ)
  | 5, 1 => (0 : ℂ)
  | 5, 2 => (0 : ℂ)
  | 5, 3 => (8064 : ℂ)
  | 5, 4 => (2949120 : ℂ)
  | 5, 5 => (25165824 : ℂ)
  | _, _ => 0

theorem Lv0_1 : coordsAux Atab (fun m => Xtab 0 m) 1 = [((3576 : ℤ) : ℂ)] := by
  simp only [coordsAux, Xtab, Finset.sum_range_zero, List.nil_append]
  norm_num

theorem Lv0_2 : coordsAux Atab (fun m => Xtab 0 m) 2 = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 0 m) 1
      ++ [Xtab 0 1 - ∑ i ∈ Finset.range 1,
      Atab i 1 * (coordsAux Atab (fun m => Xtab 0 m) 1).getD i 0] = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ)]
  rw [Lv0_1]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv0_3 : coordsAux Atab (fun m => Xtab 0 m) 3 = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ), ((-6686870937316024320000000 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 0 m) 2
      ++ [Xtab 0 2 - ∑ i ∈ Finset.range 2,
      Atab i 2 * (coordsAux Atab (fun m => Xtab 0 m) 2).getD i 0] = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ), ((-6686870937316024320000000 : ℤ) : ℂ)]
  rw [Lv0_2]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv0_4 : coordsAux Atab (fun m => Xtab 0 m) 4 = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ), ((-6686870937316024320000000 : ℤ) : ℂ), ((5257014245625692160000000000 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 0 m) 3
      ++ [Xtab 0 3 - ∑ i ∈ Finset.range 3,
      Atab i 3 * (coordsAux Atab (fun m => Xtab 0 m) 3).getD i 0] = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ), ((-6686870937316024320000000 : ℤ) : ℂ), ((5257014245625692160000000000 : ℤ) : ℂ)]
  rw [Lv0_3]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv0_5 : coordsAux Atab (fun m => Xtab 0 m) 5 = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ), ((-6686870937316024320000000 : ℤ) : ℂ), ((5257014245625692160000000000 : ℤ) : ℂ), ((-1009146538984734720000000000000 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 0 m) 4
      ++ [Xtab 0 4 - ∑ i ∈ Finset.range 4,
      Atab i 4 * (coordsAux Atab (fun m => Xtab 0 m) 4).getD i 0] = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ), ((-6686870937316024320000000 : ℤ) : ℂ), ((5257014245625692160000000000 : ℤ) : ℂ), ((-1009146538984734720000000000000 : ℤ) : ℂ)]
  rw [Lv0_4]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv0_6 : coordsAux Atab (fun m => Xtab 0 m) 6 = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ), ((-6686870937316024320000000 : ℤ) : ℂ), ((5257014245625692160000000000 : ℤ) : ℂ), ((-1009146538984734720000000000000 : ℤ) : ℂ), ((11555266180939776000000000000000 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 0 m) 5
      ++ [Xtab 0 5 - ∑ i ∈ Finset.range 5,
      Atab i 5 * (coordsAux Atab (fun m => Xtab 0 m) 5).getD i 0] = [((3576 : ℤ) : ℂ), ((2361183241441063680000 : ℤ) : ℂ), ((-6686870937316024320000000 : ℤ) : ℂ), ((5257014245625692160000000000 : ℤ) : ℂ), ((-1009146538984734720000000000000 : ℤ) : ℂ), ((11555266180939776000000000000000 : ℤ) : ℂ)]
  rw [Lv0_5]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv2_1 : coordsAux Atab (fun m => Xtab 2 m) 1 = [((0 : ℤ) : ℂ)] := by
  simp only [coordsAux, Xtab, Finset.sum_range_zero, List.nil_append]
  norm_num

theorem Lv2_2 : coordsAux Atab (fun m => Xtab 2 m) 2 = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 2 m) 1
      ++ [Xtab 2 1 - ∑ i ∈ Finset.range 1,
      Atab i 1 * (coordsAux Atab (fun m => Xtab 2 m) 1).getD i 0] = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ)]
  rw [Lv2_1]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv2_3 : coordsAux Atab (fun m => Xtab 2 m) 3 = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ), ((1047300096 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 2 m) 2
      ++ [Xtab 2 2 - ∑ i ∈ Finset.range 2,
      Atab i 2 * (coordsAux Atab (fun m => Xtab 2 m) 2).getD i 0] = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ), ((1047300096 : ℤ) : ℂ)]
  rw [Lv2_2]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv2_4 : coordsAux Atab (fun m => Xtab 2 m) 4 = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ), ((1047300096 : ℤ) : ℂ), ((84053458944000 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 2 m) 3
      ++ [Xtab 2 3 - ∑ i ∈ Finset.range 3,
      Atab i 3 * (coordsAux Atab (fun m => Xtab 2 m) 3).getD i 0] = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ), ((1047300096 : ℤ) : ℂ), ((84053458944000 : ℤ) : ℂ)]
  rw [Lv2_3]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv2_5 : coordsAux Atab (fun m => Xtab 2 m) 5 = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ), ((1047300096 : ℤ) : ℂ), ((84053458944000 : ℤ) : ℂ), ((1265866113024000000 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 2 m) 4
      ++ [Xtab 2 4 - ∑ i ∈ Finset.range 4,
      Atab i 4 * (coordsAux Atab (fun m => Xtab 2 m) 4).getD i 0] = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ), ((1047300096 : ℤ) : ℂ), ((84053458944000 : ℤ) : ℂ), ((1265866113024000000 : ℤ) : ℂ)]
  rw [Lv2_4]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem Lv2_6 : coordsAux Atab (fun m => Xtab 2 m) 6 = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ), ((1047300096 : ℤ) : ℂ), ((84053458944000 : ℤ) : ℂ), ((1265866113024000000 : ℤ) : ℂ), ((3962711310336000000000 : ℤ) : ℂ)] := by
  change coordsAux Atab (fun m => Xtab 2 m) 5
      ++ [Xtab 2 5 - ∑ i ∈ Finset.range 5,
      Atab i 5 * (coordsAux Atab (fun m => Xtab 2 m) 5).getD i 0] = [((0 : ℤ) : ℂ), ((2088 : ℤ) : ℂ), ((1047300096 : ℤ) : ℂ), ((84053458944000 : ℤ) : ℂ), ((1265866113024000000 : ℤ) : ℂ), ((3962711310336000000000 : ℤ) : ℂ)]
  rw [Lv2_5]
  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append]
  norm_num

theorem e5_0 : coordN Atab (fun m => Xtab 0 m) 5 = ((11555266180939776000000000000000 : ℤ) : ℂ) := by
  simp only [coordN]
  rw [Lv0_6]
  rfl

theorem e2_0 : coordN Atab (fun m => Xtab 0 m) 2 = ((-6686870937316024320000000 : ℤ) : ℂ) := by
  simp only [coordN]
  rw [Lv0_3]
  rfl

theorem e5_2 : coordN Atab (fun m => Xtab 2 m) 5 = ((3962711310336000000000 : ℤ) : ℂ) := by
  simp only [coordN]
  rw [Lv2_6]
  rfl

end S4Staged
