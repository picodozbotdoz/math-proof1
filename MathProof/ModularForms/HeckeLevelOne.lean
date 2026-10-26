import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The Hecke operator `T_p` on level-one modular forms

For a prime `p` and an integer weight `k` we define, for `f : ℍ → ℂ`,

    T_p f (z) = p⁻¹ • Σ_{j < p} f((z + j) / p) + p ^ (k - 1) • f (p • z),

the weight-`k` Hecke operator `T_p` for the full modular group, and prove:

* `heckeTPFun_slash_invariant`: `T_p f` is again slash-invariant of weight `k`
  under `SL(2, ℤ)` whenever `f` is (T- and S-invariance; S-invariance uses the
  explicit factorization `[j, -(jj'+1)/p]; [p, -j']` of the coset
  representatives, where `j j' ≡ -1 [MOD p]`);
* `heckeTP` acts on `ModularForm 𝒮ℒ k` and on `CuspForm 𝒮ℒ k`;
* `heckeTP_qExpansion_coeff`: `(T_p f)_m = f_{p m} + p ^ (k-1) • (if p ∣ m then f_{m/p} else 0)`.

This is the operator-level input to Mordell's theorem on the Ramanujan τ
function (`MathProof/Tau/Mordell.lean`): since `S₁₂(SL(2,ℤ))` is
one-dimensional, `T_p Δ = τ(p) • Δ`, and comparing coefficients gives
`τ(p n) = τ(p) τ(n)` for `p ∤ n` and the two-term recursion for `τ(p^r)`.
-/

open UpperHalfPlane ModularForm CuspForm Filter Function Periodic CongruenceSubgroup
open scoped MatrixGroups Manifold Real

namespace HeckeLevelOne

local notation "𝕢" => Periodic.qParam

/-! ### Padding `HasSum`s along the multiples of `p` -/

section Pad

variable {p : ℕ} {u : ℕ → ℂ} {L : ℂ}

private lemma mulLeft_injective (hp : 0 < p) : Function.Injective (fun m : ℕ => p * m) :=
  fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h

/-- The family `u`, reindexed onto the multiples of `p` and extended by `0`. -/
lemma paddedEq (hp : 0 < p) :
    (fun n => if p ∣ n then u (n / p) else 0) = Function.extend (fun m => p * m) u 0 := by
  funext n
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have h1 : Function.extend (fun m => p * m) u 0 (p * m) = u m :=
      Function.Injective.extend_apply (f := fun m => p * m) (mulLeft_injective hp) u 0 m
    rw [h1, Nat.mul_div_cancel_left _ hp]
    simp [dvd_mul_right]
  · have h1 : Function.extend (fun m => p * m) u 0 n = 0 :=
      Function.extend_apply' (f := fun m => p * m) u 0 n
        (by rintro ⟨x, hx⟩; exact hpn ⟨x, hx.symm⟩)
    rw [h1]
    simp [hpn]

/-- If `u` has sum `L`, its extension by `0` off the multiples of `p` has sum `L`. -/
theorem hasSum_padMul (hp : 0 < p) (h : HasSum u L) :
    HasSum (fun n => if p ∣ n then u (n / p) else 0) L := by
  rw [paddedEq hp]
  exact hasSum_extend_zero (g := fun m => p * m) (mulLeft_injective hp) |>.mpr h

/-- Conversely, if the extension of `u` off the multiples of `p` has sum `L`, so does `u`. -/
theorem hasSum_unpadMul (hp : 0 < p) (h : HasSum (fun n => if p ∣ n then u (n / p) else 0) L) :
    HasSum u L := by
  rw [paddedEq hp] at h
  exact hasSum_extend_zero (g := fun m => p * m) (mulLeft_injective hp) |>.mp h

end Pad

/-! ### Points of ℍ and the operator `T_p` -/

section Points

variable {k : ℤ} {p : ℕ} {f : ℍ → ℂ}

lemma im_div_natCast (x : ℂ) (j : ℕ) {p : ℕ} (_hp : 0 < p) :
    Complex.im ((x + (j : ℂ)) / (p : ℂ)) = x.im / p := by
  rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]

/-- `(z + j) / p` as a point of the upper half-plane (`0 < p`). -/
noncomputable def shiftDivP {p : ℕ} (hp : 0 < p) (j : ℕ) (z : ℍ) : ℍ :=
  ⟨((z : ℂ) + j) / (p : ℂ), by
    rw [im_div_natCast (z : ℂ) j hp]
    exact div_pos z.im_pos (by exact_mod_cast hp)⟩

/-- `p • z` as a point of the upper half-plane (`0 < p`). -/
noncomputable def mulP {p : ℕ} (hp : 0 < p) (z : ℍ) : ℍ :=
  ⟨(p : ℂ) * z, by
    rw [← Complex.ofReal_natCast p, Complex.im_ofReal_mul]
    exact mul_pos (by exact_mod_cast hp) z.im_pos⟩

@[simp, norm_cast]
lemma coe_shiftDivP {p : ℕ} (hp : 0 < p) (j : ℕ) (z : ℍ) :
    ((shiftDivP hp j z : ℍ) : ℂ) = ((z : ℂ) + j) / (p : ℂ) := rfl

@[simp, norm_cast]
lemma coe_mulP {p : ℕ} (hp : 0 < p) (z : ℍ) : ((mulP hp z : ℍ) : ℂ) = (p : ℂ) * z := rfl

/-- The Hecke operator `T_p` on functions `ℍ → ℂ` (any `p ≥ 1`, any weight `k`). -/
noncomputable def heckeTPFun {p : ℕ} (hp : 0 < p) (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ := fun z =>
  (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (shiftDivP hp j z) + (p : ℂ) ^ (k - 1) * f (mulP hp z)

lemma heckeTPFun_apply {p : ℕ} (hp : 0 < p) (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    heckeTPFun hp k f z
      = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (shiftDivP hp j z)
        + (p : ℂ) ^ (k - 1) * f (mulP hp z) := rfl

lemma heckeTPFun_add {p : ℕ} (hp : 0 < p) (k : ℤ) (f g : ℍ → ℂ) :
    heckeTPFun hp k (f + g) = heckeTPFun hp k f + heckeTPFun hp k g := by
  funext z
  simp only [heckeTPFun_apply, Pi.add_apply, Finset.sum_add_distrib]
  ring

lemma heckeTPFun_smul {p : ℕ} (hp : 0 < p) (k : ℤ) (c : ℂ) (f : ℍ → ℂ) :
    heckeTPFun hp k (c • f) = c • heckeTPFun hp k f := by
  funext z
  have h1 : ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, (c * f (shiftDivP hp j z)))
      = (p : ℂ)⁻¹ * c * ∑ j ∈ Finset.range p, f (shiftDivP hp j z) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [heckeTPFun_apply, Pi.smul_apply, smul_eq_mul, h1]
  ring

end Points

/-! ### Weight-`k` invariance under `SL(2, ℤ)` -/

section Invariance

variable {k : ℤ} {p : ℕ} {f : ℍ → ℂ}

/-- Pointwise slash invariance of weight `k` under `SL(2, ℤ)`, in the form
`f (γ • z) = (γ 1 0 * z + γ 1 1) ^ k * f z`. -/
def IsSlashInvariantSL (k : ℤ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), ∀ z : ℍ, f (γ • z) = denom (γ : GL (Fin 2) ℝ) z ^ k * f z

lemma denomSL_apply (γ : SL(2, ℤ)) (z : ℍ) :
    denom (γ : GL (Fin 2) ℝ) z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := rfl

lemma coe_smul_SL_int (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) =
      (((γ 0 0 : ℤ) : ℂ) * z + (γ 0 1 : ℤ)) /
      (((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)) := by
  rw [coe_specialLinearGroup_apply]
  rfl

/-- Point formula for an `SL(2, ℤ)`-translate with entries supplied as opaque integers. -/
lemma coe_smul_SL_int' {γ : SL(2, ℤ)} {a b c d : ℤ} (w : ℍ)
    (h00 : (γ 0 0) = a) (h01 : (γ 0 1) = b) (h10 : (γ 1 0) = c) (h11 : (γ 1 1) = d) :
    ((γ • w : ℍ) : ℂ) =
      ((((a : ℤ) : ℂ)) * (w : ℂ) + ((b : ℤ) : ℂ)) /
      ((((c : ℤ) : ℂ)) * (w : ℂ) + ((d : ℤ) : ℂ)) := by
  rw [coe_smul_SL_int γ w, h00, h01, h10, h11]

lemma coe_ne_zero (z : ℍ) : (z : ℂ) ≠ 0 := by
  intro h
  apply z.im_pos.ne'
  have h2 : (z : ℂ).im = 0 := by rw [h, Complex.zero_im]
  simpa using h2

lemma coe_smul_T_zpow (n : ℤ) (w : ℍ) :
    ((ModularGroup.T ^ n • w : ℍ) : ℂ) = (w : ℂ) + n := by
  have h := congrArg UpperHalfPlane.coe (modular_T_zpow_smul w n)
  rw [coe_vadd, add_comm] at h
  exact h

lemma coe_smul_S (w : ℍ) : ((ModularGroup.S • w : ℍ) : ℂ) = -(w : ℂ)⁻¹ := by
  simpa using congrArg UpperHalfPlane.coe (modular_S_smul w)

lemma S_entries :
    ((ModularGroup.S : SL(2, ℤ)) 0 0 : ℤ) = 0 ∧ ((ModularGroup.S : SL(2, ℤ)) 0 1 : ℤ) = -1 ∧
    ((ModularGroup.S : SL(2, ℤ)) 1 0 : ℤ) = 1 ∧ ((ModularGroup.S : SL(2, ℤ)) 1 1 : ℤ) = 0 := by
  simp [ModularGroup.S]

/-- Translation invariance of a slash-invariant function. -/
lemma IsSlashInvariantSL.f_eq_of_coe_add_int (hf : IsSlashInvariantSL k f) (n : ℤ) (w w' : ℍ)
    (hcoe : (w' : ℂ) = (w : ℂ) + n) : f w' = f w := by
  have h1 : ((ModularGroup.T ^ n) • w : ℍ) = w' := by
    rw [UpperHalfPlane.ext_iff, coe_smul_T_zpow, hcoe]
  have hd : denom ((ModularGroup.T ^ n : SL(2, ℤ)) : GL (Fin 2) ℝ) w = 1 := by
    have e10 : ((ModularGroup.T ^ n : SL(2, ℤ)) 1 0 : ℤ) = 0 := by
      rw [show ((ModularGroup.T ^ n : SL(2, ℤ)) 1 0) =
        ((ModularGroup.T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl,
        ModularGroup.coe_T_zpow]
      rfl
    have e11 : ((ModularGroup.T ^ n : SL(2, ℤ)) 1 1 : ℤ) = 1 := by
      rw [show ((ModularGroup.T ^ n : SL(2, ℤ)) 1 1) =
        ((ModularGroup.T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from rfl,
        ModularGroup.coe_T_zpow]
      rfl
    rw [denomSL_apply, e10, e11]
    simp
  have h2 := hf (ModularGroup.T ^ n) w
  rw [hd, one_zpow, one_mul] at h2
  rw [← h1, h2]

/-! ### T-invariance -/

lemma sum_shift_one {p : ℕ} (hp : 0 < p) (F : ℕ → ℂ) (hF : ∀ j, F (j + p) = F j) :
    ∑ j ∈ Finset.range p, F (j + 1) = ∑ j ∈ Finset.range p, F j := by
  have key : ∑ j ∈ Finset.Ico 1 (1 + p), F j = ∑ j ∈ Finset.range p, F (1 + j) := by
    have h := Finset.sum_Ico_eq_sum_range F 1 (1 + p)
    rw [show 1 + p - 1 = p from by omega] at h
    exact h
  have h1 : ∑ j ∈ Finset.range p, F (j + 1) = ∑ j ∈ Finset.Ico 1 (1 + p), F j := by
    rw [key]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm j 1]
  have h2 : Finset.Ico 1 (1 + p) = insert p (Finset.Ico 1 p) := by
    rw [add_comm]
    exact Nat.Ico_succ_right_eq_insert_Ico (a := 1) (b := p) (by omega)
  have h3 : ∑ j ∈ Finset.Ico 1 p, F j = ∑ j ∈ Finset.range p, F j - F 0 := by
    have hmem : 0 ∈ Finset.Ico 0 p := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hI : Finset.Ico (Nat.succ 0) p = Finset.erase (Finset.Ico 0 p) 0 :=
      Nat.Ico_succ_left_eq_erase_Ico
    rw [show (1 : ℕ) = Nat.succ 0 from rfl, hI, Finset.sum_erase_eq_sub hmem, ← Finset.range_eq_Ico]
  rw [h1, h2, Finset.sum_insert (by simp), h3]
  have h5 : F p = F 0 := by rw [← hF 0, Nat.zero_add]
  rw [h5]
  abel

theorem heckeTPFun_T (hp : 0 < p) (hf : IsSlashInvariantSL k f) (z : ℍ) :
    heckeTPFun hp k f (ModularGroup.T • z) = heckeTPFun hp k f z := by
  have hTz : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    have h0 := coe_smul_T_zpow 1 z
    rwa [zpow_one, Int.cast_one] at h0
  have hsum : ∑ j ∈ Finset.range p, f (shiftDivP hp j (ModularGroup.T • z))
      = ∑ j ∈ Finset.range p, f (shiftDivP hp j z) := by
    have hshift : ∀ j ∈ Finset.range p, f (shiftDivP hp j (ModularGroup.T • z))
        = f (shiftDivP hp (j + 1) z) := by
      intro j _
      have hpt : (shiftDivP hp j (ModularGroup.T • z) : ℍ) = shiftDivP hp (j + 1) z := by
        rw [UpperHalfPlane.ext_iff, coe_shiftDivP, coe_shiftDivP, hTz,
          div_eq_div_iff (by exact_mod_cast hp.ne' : ((p : ℂ)) ≠ 0)
            (by exact_mod_cast hp.ne' : ((p : ℂ)) ≠ 0)]
        push_cast
        ring
      rw [hpt]
    rw [Finset.sum_congr rfl (fun j hj => hshift j hj)]
    refine sum_shift_one hp (fun j => f (shiftDivP hp j z)) ?_
    intro j
    refine hf.f_eq_of_coe_add_int (n := 1) (w := shiftDivP hp j z)
      (w' := shiftDivP hp (j + p) z) ?_
    rw [coe_shiftDivP, coe_shiftDivP]
    have hjp : ((j + p : ℕ) : ℂ) = (j : ℂ) + (p : ℂ) := by
      push_cast
      ring
    rw [hjp, ← add_assoc, add_div, div_self (by exact_mod_cast hp.ne' : ((p : ℂ)) ≠ 0)]
    norm_num
  have hmul : f (mulP hp (ModularGroup.T • z)) = f (mulP hp z) := by
    refine hf.f_eq_of_coe_add_int (n := (p : ℤ)) (w := mulP hp z)
      (w' := mulP hp (ModularGroup.T • z)) ?_
    rw [coe_mulP, coe_mulP, hTz]
    push_cast
    ring
  rw [heckeTPFun_apply, heckeTPFun_apply, hsum, hmul]

/-! ### The involution `j ↦ -j⁻¹` of `[1, p-1]` and the coset factorization -/

section Sigma

variable {p j : ℕ}

/-- `-j⁻¹` in `ZMod p`, as a natural number. -/
def phiInv (p j : ℕ) : ℕ := (p - ((j : ZMod p)⁻¹.val)) % p

lemma phiInv_lt {p : ℕ} (hp : 0 < p) (j : ℕ) : phiInv p j < p := Nat.mod_lt _ hp

lemma phiInv_cast (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    ((phiInv p j : ℕ) : ZMod p) = -((j : ZMod p)⁻¹) := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have : Fact p.Prime := ⟨hp⟩
  have hv : ((j : ZMod p)⁻¹.val) < p := ZMod.val_lt _
  have hv0 : ((j : ZMod p)⁻¹.val) ≠ 0 := by
    intro h0
    have huv : (((j : ZMod p)⁻¹ : ZMod p).val : ZMod p) = (j : ZMod p)⁻¹ := by
      simp [ZMod.cast_id]
    rw [h0] at huv
    have hzero : ((j : ZMod p)⁻¹) = 0 := by simpa using huv.symm
    exact hj (inv_eq_zero.mp hzero)
  have hmod : (p - ((j : ZMod p)⁻¹.val)) % p = p - ((j : ZMod p)⁻¹.val) :=
    Nat.mod_eq_of_lt (by omega)
  rw [phiInv, hmod]
  have hcast : ((p - ((j : ZMod p)⁻¹.val) : ℕ) : ZMod p)
      = ((p : ℕ) : ZMod p) - (((j : ZMod p)⁻¹.val : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (le_of_lt hv)]
  rw [hcast, ZMod.natCast_self, zero_sub]
  congr 1
  simp [ZMod.cast_id]

lemma phiInv_cast_ne_zero (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    ((phiInv p j : ℕ) : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [phiInv_cast hp hj]
  exact neg_ne_zero.mpr (inv_ne_zero hj)

lemma phiInv_ne_zero (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    phiInv p j ≠ 0 := by
  intro h
  have hc := phiInv_cast_ne_zero hp hj
  rw [h, Nat.cast_zero] at hc
  exact hc rfl

lemma phiInv_dvd (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    p ∣ j * phiInv p j + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff (j * phiInv p j + 1) p]
  push_cast
  rw [phiInv_cast hp hj, mul_neg,
    show ((j : ZMod p) * ((j : ZMod p))⁻¹) = 1 from mul_inv_cancel₀ hj]
  simp

lemma phiInv_involution (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) (hjlt : j < p) :
    phiInv p (phiInv p j) = j := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have : Fact p.Prime := ⟨hp⟩
  have h1 := phiInv_cast hp (phiInv_cast_ne_zero hp hj)
  rw [phiInv_cast hp hj, inv_neg, inv_inv, neg_neg] at h1
  have h2 := congrArg ZMod.val h1
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (phiInv_lt hp.pos _),
    Nat.mod_eq_of_lt hjlt] at h2
  exact h2

lemma phiInv_mem_Icc (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    phiInv p j ∈ Finset.Icc 1 (p - 1) := by
  have h1 := phiInv_ne_zero hp hj
  have h2 := phiInv_lt hp.pos j
  simp only [Finset.mem_Icc]
  omega

lemma eq_zero_of_zmod_cast {p j : ℕ} (hjlt : j < p) (hj : (j : ZMod p) = 0) : j = 0 := by
  have hd : p ∣ j := (ZMod.natCast_eq_zero_iff j p).mp hj
  exact Nat.eq_zero_of_dvd_of_lt hd hjlt

/-- The matrix `[[j, -(j·j'+1)/p], [p, -j']] ∈ SL(2, ℤ)` (determinant `1` when `p ∣ j·j'+1`). -/
def sigmaMatrix (p j j' : ℕ) (hdiv : p ∣ j * j' + 1) : SL(2, ℤ) :=
  ⟨!![(j : ℤ), -(((j * j' + 1) / p : ℕ) : ℤ); (p : ℤ), -(j' : ℤ)], by
    have h1 : (((j * j' + 1) / p : ℕ) : ℤ) * (p : ℤ) = (j : ℤ) * (j' : ℤ) + 1 := by
      have h := Nat.mul_div_cancel' hdiv
      rw [mul_comm] at h
      exact_mod_cast h
    rw [Matrix.det_fin_two]
    change ((j : ℤ) * (-(j' : ℤ)) - (-(((j * j' + 1) / p : ℕ) : ℤ)) * (p : ℤ)) = 1
    linarith [h1]⟩

end Sigma

/-! ### S-invariance -/

theorem heckeTPFun_S (hp : p.Prime) (hf : IsSlashInvariantSL k f) (z : ℍ) :
    heckeTPFun hp.pos k f (ModularGroup.S • z) = (z : ℂ) ^ k * heckeTPFun hp.pos k f z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hz : (z : ℂ) ≠ 0 := coe_ne_zero z
  have h1p : 1 < p := hp.one_lt
  -- split off the j = 0 term
  have hsplit : ∀ g : ℍ → ℂ, ∑ j ∈ Finset.range p, g (shiftDivP hp.pos j (ModularGroup.S • z))
      = g (shiftDivP hp.pos 0 (ModularGroup.S • z))
        + ∑ j ∈ Finset.Icc 1 (p - 1), g (shiftDivP hp.pos j (ModularGroup.S • z)) := by
    intro g
    rw [show Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) from
      (Finset.ext fun j => by
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega),
      Finset.sum_insert (by simp [Finset.mem_Icc])]
  -- the j = 0 term is governed by the S-invariance of f at the point `p • z`
  have hS0 : f (shiftDivP hp.pos 0 (ModularGroup.S • z))
      = (p : ℂ) ^ k * (z : ℂ) ^ k * f (mulP hp.pos z) := by
    have hpt : (shiftDivP hp.pos 0 (ModularGroup.S • z) : ℍ)
        = ModularGroup.S • (mulP hp.pos z) := by
      rw [UpperHalfPlane.ext_iff, coe_shiftDivP, coe_smul_S, coe_smul_S, coe_mulP]
      push_cast
      rw [add_zero, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hpt, hf ModularGroup.S (mulP hp.pos z)]
    obtain ⟨-, -, e10, e11⟩ := S_entries
    have hdS : denom ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) (mulP hp.pos z)
        = (p : ℂ) * z := by
      rw [denomSL_apply, e10, e11, coe_mulP]
      simp
    rw [hdS, mul_zpow]
  -- the j ≥ 1 terms are governed by the matrices σ_j
  have hSj : ∀ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos j (ModularGroup.S • z))
      = (z : ℂ) ^ k * f (shiftDivP hp.pos (phiInv p j) z) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hjlt : j < p := by omega
    have hjz : (j : ZMod p) ≠ 0 := by
      intro hd
      have h0 := eq_zero_of_zmod_cast hjlt hd
      omega
    have hdiv := phiInv_dvd hp hjz
    have hc2 : (((j * phiInv p j + 1) / p : ℕ) : ℂ)
        = ((j : ℂ) * (phiInv p j : ℂ) + 1) / (p : ℂ) := by
      rw [eq_comm, div_eq_iff hp0,
        mul_comm (((j * phiInv p j + 1) / p : ℕ) : ℂ) ((p : ℂ))]
      exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
    have hpt : (shiftDivP hp.pos j (ModularGroup.S • z) : ℍ)
        = (sigmaMatrix p j (phiInv p j) hdiv) • (shiftDivP hp.pos (phiInv p j) z) := by
      rw [UpperHalfPlane.ext_iff, coe_shiftDivP, coe_smul_S,
        coe_smul_SL_int' (a := (j : ℤ)) (b := -(((j * phiInv p j + 1) / p : ℕ) : ℤ))
          (c := (p : ℤ)) (d := -((phiInv p j : ℕ) : ℤ))
          (shiftDivP hp.pos (phiInv p j) z) rfl rfl rfl rfl,
        coe_shiftDivP, Int.cast_neg, Int.cast_neg,
        Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, hc2]
      -- `hw`: the denominator factor simplifies, `p • ((z + φ)/p) = z + φ`
      have hw : (p : ℂ) * (((z : ℂ) + (phiInv p j : ℂ)) / (p : ℂ))
          = (z : ℂ) + (phiInv p j : ℂ) := by
        rw [mul_comm, div_mul_cancel₀ _ hp0]
      -- `hD`: the denominator of the σ_j-translate is `z ≠ 0`
      have hD : ((p : ℂ) * (((z : ℂ) + (phiInv p j : ℂ)) / (p : ℂ))
          + -((phiInv p j : ℂ))) ≠ 0 := by
        rw [hw, add_neg_cancel_right]
        exact hz
      -- `hc'`: the numerator identity, `p • ((jφ + 1)/p) = jφ + 1`
      have hc' : (p : ℂ) * (((j : ℂ) * (phiInv p j : ℂ) + 1) / (p : ℂ))
          = (j : ℂ) * (phiInv p j : ℂ) + 1 := by
        rw [mul_comm, div_mul_cancel₀ _ hp0]
      -- `hzz1`: the unit factor `z⁻¹ z = 1`
      have hzz1 : (z : ℂ)⁻¹ * (z : ℂ) = 1 := inv_mul_cancel₀ hz
      -- the cross-multiplied point identity of `hpt`; the certificate
      -- combines the three identities above as `hc' − z⁻¹ • hw − hzz1`
      rw [div_eq_div_iff hp0 hD]
      linear_combination hc' - (z : ℂ)⁻¹ * hw - hzz1
    rw [hpt, hf (sigmaMatrix p j (phiInv p j) hdiv) (shiftDivP hp.pos (phiInv p j) z)]
    have hdσ : denom ((sigmaMatrix p j (phiInv p j) hdiv : SL(2, ℤ)) : GL (Fin 2) ℝ)
        (shiftDivP hp.pos (phiInv p j) z) = (z : ℂ) := by
      rw [denomSL_apply,
        show ((sigmaMatrix p j (phiInv p j) hdiv : SL(2, ℤ)) 1 0) = (p : ℤ) from rfl,
        show ((sigmaMatrix p j (phiInv p j) hdiv : SL(2, ℤ)) 1 1) = -((phiInv p j : ℤ)) from rfl,
        coe_shiftDivP]
      push_cast
      rw [mul_div_cancel₀ _ hp0]
      ring
    rw [hdσ]
  -- the second term is governed by the S-invariance of f at the point `z / p`
  have hS1 : (p : ℂ) ^ (k - 1) * f (mulP hp.pos (ModularGroup.S • z))
      = (z : ℂ) ^ k * (p : ℂ)⁻¹ * f (shiftDivP hp.pos 0 z) := by
    have hpt : (mulP hp.pos (ModularGroup.S • z) : ℍ)
        = ModularGroup.S • (shiftDivP hp.pos 0 z) := by
      rw [UpperHalfPlane.ext_iff, coe_mulP, coe_smul_S, coe_smul_S, coe_shiftDivP]
      push_cast
      rw [add_zero, div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    rw [hpt, hf ModularGroup.S (shiftDivP hp.pos 0 z)]
    obtain ⟨-, -, e10, e11⟩ := S_entries
    have hdS : denom ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) (shiftDivP hp.pos 0 z)
        = (z : ℂ) / p := by
      rw [denomSL_apply, e10, e11, coe_shiftDivP]
      push_cast
      simp
    have hzz : ((z : ℂ) / p) ^ k = (z : ℂ) ^ k * (p : ℂ) ^ (-k) := by
      rw [div_eq_mul_inv, mul_zpow, inv_zpow']
    have hfin : (p : ℂ) ^ (k - 1) * ((z : ℂ) ^ k * (p : ℂ) ^ (-k))
        = (z : ℂ) ^ k * (p : ℂ)⁻¹ := by
      rw [mul_comm ((z : ℂ) ^ k) ((p : ℂ) ^ (-k)), ← mul_assoc, ← zpow_add₀ hp0,
        show (k : ℤ) - 1 + -k = -1 from by ring, zpow_neg_one]
      ring
    rw [hdS, hzz, ← mul_assoc, hfin]
  -- the involution j ↦ φ j permutes [1, p-1]
  have hbij : ∑ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos (phiInv p j) z)
      = ∑ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos j z) := by
    refine Finset.sum_bij (fun j _ => phiInv p j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have hjlt : j < p := by omega
      refine phiInv_mem_Icc hp (fun hd => ?_)
      have h0 := eq_zero_of_zmod_cast hjlt hd
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      have halt : a < p := by omega
      have hblt : b < p := by omega
      have haz : (a : ZMod p) ≠ 0 := by
        intro hd
        have h0 := eq_zero_of_zmod_cast halt hd
        omega
      have hbz : (b : ZMod p) ≠ 0 := by
        intro hd
        have h0 := eq_zero_of_zmod_cast hblt hd
        omega
      have h3 := congrArg (phiInv p) hab
      rwa [phiInv_involution hp haz halt, phiInv_involution hp hbz hblt] at h3
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      have hblt : b < p := by omega
      have hbz : (b : ZMod p) ≠ 0 := by
        intro hd
        have h0 := eq_zero_of_zmod_cast hblt hd
        omega
      exact ⟨phiInv p b, phiInv_mem_Icc hp hbz, phiInv_involution hp hbz hblt⟩
    · intro a ha
      rfl
  -- assemble
  rw [heckeTPFun_apply, heckeTPFun_apply, hsplit f, hS0, hS1]
  rw [Finset.sum_congr rfl (fun j hj => hSj j hj)]
  have hmulsum : ∑ j ∈ Finset.Icc 1 (p - 1), ((z : ℂ) ^ k * f (shiftDivP hp.pos (phiInv p j) z))
      = (z : ℂ) ^ k * ∑ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos (phiInv p j) z) := by
    rw [Finset.mul_sum]
  rw [hmulsum, hbij]
  have hsplit' : ∑ j ∈ Finset.range p, f (shiftDivP hp.pos j z)
      = f (shiftDivP hp.pos 0 z) + ∑ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos j z) := by
    rw [show Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) from
      (Finset.ext fun j => by
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega),
      Finset.sum_insert (by simp [Finset.mem_Icc])]
  rw [hsplit']
  have hpow : (p : ℂ)⁻¹ * (p : ℂ) ^ k = (p : ℂ) ^ (k - 1) := by
    rw [← zpow_neg_one, ← zpow_add₀ hp0]
    congr 1
    ring
  linear_combination ((z : ℂ) ^ k * f (mulP hp.pos z)) * hpow

/-! ### Slash invariance of `T_p f` -/

theorem heckeTPFun_slash_invariant (hp : p.Prime) (hf : IsSlashInvariantSL k f) :
    ∀ γ : SL(2, ℤ), heckeTPFun hp.pos k f ∣[k] γ = heckeTPFun hp.pos k f := by
  refine SlashInvariantForm.slash_action_generators_SL2Z ?_ ?_
  · funext z
    rw [ModularForm.SL_slash_apply, heckeTPFun_S hp hf z]
    have hz : (z : ℂ) ≠ 0 := coe_ne_zero z
    obtain ⟨-, -, e10, e11⟩ := S_entries
    have hd : denom ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) z = (z : ℂ) := by
      rw [denomSL_apply, e10, e11]
      simp
    rw [hd, mul_assoc, mul_comm (heckeTPFun hp.pos k f z) ((z : ℂ) ^ (-k)), ← mul_assoc,
      ← zpow_add₀ hz, add_neg_cancel, zpow_zero, one_mul]
  · funext z
    rw [ModularForm.SL_slash_apply, heckeTPFun_T hp.pos hf z]
    have e10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℤ) = 0 := rfl
    have e11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℤ) = 1 := rfl
    have hd : denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1 := by
      rw [denomSL_apply, e10, e11]
      simp
    rw [hd, one_zpow, mul_one]

end Invariance

/-! ### From slash invariance of a level-one form to `IsSlashInvariantSL` -/

section ToInvariant

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F 𝒮ℒ k]

lemma toIsSlashInvariantSL (f : F) : IsSlashInvariantSL k f := by
  have hinst : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
  exact fun γ z => SlashInvariantForm.slash_action_eqn_SL'' f (mem_Gamma_one γ) z

end ToInvariant

/-! ### Imaginary parts, limits at `i∞`, and holomorphy of the operator -/

section Analysis

variable {k : ℤ} {p : ℕ}

lemma im_shiftDivP (hp : 0 < p) (j : ℕ) (z : ℍ) : (shiftDivP hp j z).im = z.im / p := by
  rw [← UpperHalfPlane.coe_im, coe_shiftDivP, Complex.div_natCast_im,
    Complex.add_im, Complex.natCast_im, add_zero, UpperHalfPlane.coe_im]

lemma im_mulP (hp : 0 < p) (z : ℍ) : (mulP hp z).im = p * z.im := by
  rw [← UpperHalfPlane.coe_im, coe_mulP, Complex.mul_im, Complex.natCast_im,
    zero_mul, add_zero, Complex.natCast_re, UpperHalfPlane.coe_im]

lemma tendsto_shiftDivP_atImInfty (hp : 0 < p) (j : ℕ) :
    Tendsto (shiftDivP hp j) atImInfty atImInfty := by
  suffices Tendsto (fun τ : ℍ => (p : ℝ)⁻¹ * τ.im) atImInfty atTop by
    simpa [atImInfty, Function.comp_def, im_shiftDivP hp j, div_eq_inv_mul] using this
  apply tendsto_comap.const_mul_atTop
  exact inv_pos.mpr (by exact_mod_cast hp)

lemma tendsto_mulP_atImInfty (hp : 0 < p) :
    Tendsto (mulP hp) atImInfty atImInfty := by
  suffices Tendsto (fun τ : ℍ => (p : ℝ) * τ.im) atImInfty atTop by
    simpa [atImInfty, Function.comp_def, im_mulP hp] using this
  apply tendsto_comap.const_mul_atTop
  exact_mod_cast hp

lemma differentiableOn_shiftDivP_comp {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (hp : 0 < p) (j : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => g ((z + (j : ℂ)) / (p : ℂ))) {z : ℂ | 0 < z.im} := by
  have hmap : Set.MapsTo (fun z : ℂ => (z + (j : ℂ)) / (p : ℂ)) {z : ℂ | 0 < z.im}
      {z : ℂ | 0 < z.im} := by
    intro z hz
    simp only [Set.mem_ofPred_eq]
    rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
    exact div_pos hz (by exact_mod_cast hp)
  have hd1 : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
  have hd2 : Differentiable ℂ (fun z : ℂ => (j : ℂ)) := differentiable_const _
  have hd3 : Differentiable ℂ (fun z : ℂ => (p : ℂ)) := differentiable_const _
  have hdiff : Differentiable ℂ (fun z : ℂ => (z + (j : ℂ)) / (p : ℂ)) :=
    (hd1.add hd2).div hd3 (fun _ => by exact_mod_cast hp.ne')
  exact hg.comp hdiff.differentiableOn hmap

lemma differentiableOn_mulP_comp {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (hp : 0 < p) :
    DifferentiableOn ℂ (fun z : ℂ => g ((p : ℂ) * z)) {z : ℂ | 0 < z.im} := by
  have hmap : Set.MapsTo (fun z : ℂ => (p : ℂ) * z) {z : ℂ | 0 < z.im}
      {z : ℂ | 0 < z.im} := by
    intro z hz
    simp only [Set.mem_ofPred_eq]
    rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hp) hz
  have hdiff : Differentiable ℂ (fun z : ℂ => (p : ℂ) * z) :=
    (differentiable_const _).mul differentiable_id
  exact hg.comp hdiff.differentiableOn hmap

variable {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒮ℒ k]

theorem heckeTPFun_mdiff (f : F) (hp : 0 < p) : MDiff (heckeTPFun hp k f) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  have heq : ∀ z : ℂ, 0 < z.im →
      ((heckeTPFun hp k f) ∘ UpperHalfPlane.ofComplex) z
        = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p,
            ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ((z + (j : ℂ)) / (p : ℂ))
          + (p : ℂ) ^ (k - 1) * ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ((p : ℂ) * z) := by
    intro z hz
    have e1 : ∀ j ∈ Finset.range p, shiftDivP hp j (UpperHalfPlane.ofComplex z)
        = UpperHalfPlane.ofComplex ((z + (j : ℂ)) / (p : ℂ)) := by
      intro j _
      have hpos : 0 < ((z + (j : ℂ)) / (p : ℂ)).im := by
        rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
        exact div_pos hz (by exact_mod_cast hp)
      refine UpperHalfPlane.ext_iff.mpr ?_
      rw [coe_shiftDivP, UpperHalfPlane.ofComplex_apply_of_im_pos hpos,
        UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have e2 : mulP hp (UpperHalfPlane.ofComplex z)
        = UpperHalfPlane.ofComplex ((p : ℂ) * z) := by
      have hpos : 0 < ((p : ℂ) * z).im := by
        rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
        exact mul_pos (by exact_mod_cast hp) hz
      refine UpperHalfPlane.ext_iff.mpr ?_
      rw [coe_mulP, UpperHalfPlane.ofComplex_apply_of_im_pos hpos,
        UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    rw [Function.comp_apply, heckeTPFun_apply,
      Finset.sum_congr rfl (fun j hj => by rw [e1 j hj]), e2]
    simp only [Function.comp_apply]
  have h1 : ∀ j ∈ Finset.range p, DifferentiableOn ℂ
      (fun z : ℂ => ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ((z + (j : ℂ)) / (p : ℂ)))
      {z : ℂ | 0 < z.im} := fun j _ => differentiableOn_shiftDivP_comp hf hp j
  have h2 := DifferentiableOn.sum h1
  rw [show (∑ j ∈ Finset.range p,
        fun z : ℂ => ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ((z + (j : ℂ)) / (p : ℂ)))
      = fun z : ℂ => ∑ j ∈ Finset.range p,
        ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ((z + (j : ℂ)) / (p : ℂ)) from by
    funext z
    simp [Finset.sum_apply]] at h2
  have h3 : DifferentiableOn ℂ
      (fun z : ℂ => ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ((p : ℂ) * z))
      {z : ℂ | 0 < z.im} := differentiableOn_mulP_comp hf hp
  have hc1 : DifferentiableOn ℂ (fun _ : ℂ => (p : ℂ)⁻¹) {z : ℂ | 0 < z.im} :=
    (differentiable_const _).differentiableOn
  have hc2 : DifferentiableOn ℂ (fun _ : ℂ => (p : ℂ) ^ (k - 1)) {z : ℂ | 0 < z.im} :=
    (differentiable_const ((p : ℂ) ^ (k - 1))).differentiableOn
  have hdRHS : DifferentiableOn ℂ
      (fun z : ℂ => (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p,
          ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ((z + (j : ℂ)) / (p : ℂ))
        + (p : ℂ) ^ (k - 1) * ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ((p : ℂ) * z))
      {z : ℂ | 0 < z.im} := (hc1.mul h2).add (hc2.mul h3)
  refine hdRHS.congr (fun z hz => heq z hz)

private theorem tendsto_finset_sum_zero {ι : Type*} (s : Finset ι) (u : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, Tendsto (u i) atImInfty (nhds 0)) :
    Tendsto (fun z : ℍ => ∑ i ∈ s, u i z) atImInfty (nhds 0) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      simpa using Tendsto.add (h i (Finset.mem_insert_self i s))
        (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

variable {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F 𝒮ℒ k]

theorem heckeTPFun_isZeroAtImInfty (f : F) (hp : 0 < p) :
    IsZeroAtImInfty (heckeTPFun hp k f) := by
  have hsum : Tendsto
      (fun z : ℍ => ∑ j ∈ Finset.range p, (f : ℍ → ℂ) (shiftDivP hp j z)) atImInfty (nhds 0) :=
    tendsto_finset_sum_zero _ _
      (fun j _ => (CuspFormClass.zero_at_infty f).comp (tendsto_shiftDivP_atImInfty hp j))
  have hmul : Tendsto (fun z : ℍ => (f : ℍ → ℂ) (mulP hp z)) atImInfty (nhds 0) :=
    (CuspFormClass.zero_at_infty f).comp (tendsto_mulP_atImInfty hp)
  have h1 : Tendsto (fun z : ℍ => (p : ℂ)⁻¹ *
      ∑ j ∈ Finset.range p, (f : ℍ → ℂ) (shiftDivP hp j z)) atImInfty (nhds 0) := by
    simpa [mul_zero] using hsum.const_mul (p : ℂ)⁻¹
  have h2 : Tendsto (fun z : ℍ => (p : ℂ) ^ (k - 1) *
      (f : ℍ → ℂ) (mulP hp z)) atImInfty (nhds 0) := by
    simpa [mul_zero] using hmul.const_mul ((p : ℂ) ^ (k - 1))
  refine Tendsto.congr (fun z => (heckeTPFun_apply hp k (f : ℍ → ℂ) z).symm) ?_
  simpa using h1.add h2

end Analysis

/-! ### The Hecke operator on cusp forms -/

section Bundled

variable {k : ℤ} {p : ℕ}

/-- The Hecke operator `T_p` on level-one cusp forms (`p` prime): `T_p f` is again a cusp form
of the same weight, with underlying function `heckeTPFun`. -/
noncomputable def heckeTP (hp : p.Prime) (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k where
  toFun := heckeTPFun hp.pos k (f : ℍ → ℂ)
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hg
    exact heckeTPFun_slash_invariant hp (toIsSlashInvariantSL f) γ
  holo' := heckeTPFun_mdiff f hp.pos
  zero_at_cusps' := by
    intro c hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [heckeTPFun_slash_invariant hp (toIsSlashInvariantSL f) γ]
    exact heckeTPFun_isZeroAtImInfty f hp.pos

@[simp]
lemma heckeTP_apply (hp : p.Prime) (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    heckeTP hp f z = heckeTPFun hp.pos k (f : ℍ → ℂ) z := rfl

end Bundled

/-! ### The q-expansion coefficient formula -/

section QFormula

variable {k : ℤ} {p : ℕ}

private lemma qParam_one (z : ℂ) : 𝕢 1 z = Complex.exp (2 * π * Complex.I * z) := by
  simp [Periodic.qParam]

lemma qParam_mulP (hp : 0 < p) (τ : ℍ) : 𝕢 1 (mulP hp τ) = (𝕢 1 τ) ^ p := by
  rw [qParam_one, qParam_one, coe_mulP,
    show 2 * π * Complex.I * ((p : ℂ) * τ) = (p : ℂ) * (2 * π * Complex.I * τ) from by
      ring]
  exact Complex.exp_nat_mul _ _

lemma qParam_shiftDivP (hp : 0 < p) (j : ℕ) (τ : ℍ) :
    𝕢 1 (shiftDivP hp j τ)
      = Complex.exp (2 * π * Complex.I * τ / (p : ℂ))
        * Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ j := by
  rw [qParam_one, coe_shiftDivP]
  have h1 : 2 * π * Complex.I * (((τ : ℂ) + (j : ℂ)) / (p : ℂ))
      = 2 * π * Complex.I * τ / (p : ℂ) + (j : ℂ) * (2 * π * Complex.I / (p : ℂ)) := by
    field_simp
  rw [h1, Complex.exp_add, Complex.exp_nat_mul]

lemma rho_pow_p (hp : 0 < p) (τ : ℍ) :
    Complex.exp (2 * π * Complex.I * τ / (p : ℂ)) ^ p = 𝕢 1 τ := by
  rw [← Complex.exp_nat_mul, qParam_one,
    mul_div_cancel₀ _ (by exact_mod_cast hp.ne' : ((p : ℂ)) ≠ 0)]

lemma sum_xi_pow (hp : p.Prime) (n : ℕ) :
    ∑ j ∈ Finset.range p, Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ (j * n)
      = if p ∣ n then (p : ℂ) else 0 := by
  have hξ : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / (p : ℂ))) p :=
    Complex.isPrimitiveRoot_exp p hp.pos.ne'
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    rw [ite_eq_left (dvd_mul_right p m)]
    have e : ∀ j ∈ Finset.range p,
        Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ (j * (p * m)) = 1 := by
      intro j _
      rw [show j * (p * m) = p * (j * m) from by ring, pow_mul, hξ.pow_eq_one, one_pow]
    rw [Finset.sum_congr rfl e]
    simp
  · rw [ite_eq_right hpn]
    have hcop : Nat.Coprime n p := (hp.coprime_iff_not_dvd.mpr hpn).symm
    have hprim : IsPrimitiveRoot
        (Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ n) p := hξ.pow_of_coprime n hcop
    have e : ∀ j ∈ Finset.range p,
        Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ (j * n)
          = (Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ n) ^ j := by
      intro j _
      rw [Nat.mul_comm j n, pow_mul]
    rw [Finset.sum_congr rfl e, hprim.geom_sum_eq_zero hp.one_lt]

lemma paddedEq_smul (hp : 0 < p) (u : ℕ → ℂ) (r : ℂ) :
    (fun m => if p ∣ m then u (m / p) * r ^ m else 0)
      = Function.extend (fun n => p * n) (fun n => u n * r ^ (p * n)) 0 := by
  funext m
  by_cases hpm : p ∣ m
  · obtain ⟨n, rfl⟩ := hpm
    rw [Nat.mul_div_cancel_left _ hp,
      Function.Injective.extend_apply (mulLeft_injective hp) _ _ n]
    simp [dvd_mul_right]
  · have h1 : Function.extend (fun n => p * n) (fun n => u n * r ^ (p * n)) 0 m = 0 :=
      Function.extend_apply' (f := fun n => p * n) _ _ m
        (by rintro ⟨x, hx⟩; exact hpm ⟨x, hx.symm⟩)
    rw [h1]
    simp [hpm]

theorem hasSum_padMul_smul (hp : 0 < p) (u : ℕ → ℂ) (r : ℂ) {L : ℂ}
    (h : HasSum (fun n => u n * r ^ (p * n)) L) :
    HasSum (fun m => if p ∣ m then u (m / p) * r ^ m else 0) L := by
  rw [paddedEq_smul hp u r]
  exact hasSum_extend_zero (mulLeft_injective hp) |>.mpr h

private theorem hasSum_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℂ) (a : ι → ℂ)
    (h : ∀ j ∈ s, HasSum (g j) (a j)) :
    HasSum (fun n => ∑ j ∈ s, g j n) (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact HasSum.add (h i (Finset.mem_insert_self i s))
        (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

/-- **The `T_p`- HasSum**: the q-expansion of `T_p f` at `τ` sums, coefficient-wise,
to `f_{p m} + p^(k-1) [p ∣ m] f_{m/p}`. -/
theorem heckeTP_qExpansion_hasSum {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒮ℒ k]
    (hp : p.Prime) (f : F) (τ : ℍ) :
    HasSum (fun m : ℕ => ((qExpansion 1 f).coeff (p * m)
        + (p : ℂ) ^ (k - 1) * (if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0))
        * 𝕢 1 τ ^ m)
      (heckeTPFun hp.pos k (f : ℍ → ℂ) τ) := by
  have hbase : ∀ w : ℍ,
      HasSum (fun n : ℕ => (qExpansion 1 f).coeff n * 𝕢 1 w ^ n) ((f : ℍ → ℂ) w) :=
    fun w => ModularForm.hasSum_qExpansion (f := f) one_pos one_mem_strictPeriods_SL w
  -- the `f (p • τ)` summand
  have hpz : HasSum (fun m => (if p ∣ m then (qExpansion 1 f).coeff (m / p) * 𝕢 1 τ ^ m else 0))
      ((f : ℍ → ℂ) (mulP hp.pos τ)) := by
    refine hasSum_padMul_smul hp.pos (fun n => (qExpansion 1 f).coeff n) (𝕢 1 τ) ?_
    refine HasSum.congr_fun (hbase (mulP hp.pos τ)) ?_
    intro n
    rw [qParam_mulP hp.pos τ, ← pow_mul]
  have hpz' : HasSum
      (fun m => (p : ℂ) ^ (k - 1) *
        (if p ∣ m then (qExpansion 1 f).coeff (m / p) * 𝕢 1 τ ^ m else 0))
      ((p : ℂ) ^ (k - 1) * (f : ℍ → ℂ) (mulP hp.pos τ)) := by
    simpa [smul_eq_mul] using hpz.const_smul ((p : ℂ) ^ (k - 1))
  -- the `Σ_j f((τ + j)/p)` summand
  have hj : ∀ j ∈ Finset.range p,
      HasSum (fun n : ℕ => (qExpansion 1 f).coeff n
        * (Complex.exp (2 * π * Complex.I * τ / (p : ℂ))
            * Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ j) ^ n)
        ((f : ℍ → ℂ) (shiftDivP hp.pos j τ)) := by
    intro j _
    refine HasSum.congr_fun (hbase (shiftDivP hp.pos j τ)) ?_
    intro n
    rw [qParam_shiftDivP hp.pos j τ, mul_pow]
  have hsumj : HasSum (fun n : ℕ => ∑ j ∈ Finset.range p, (qExpansion 1 f).coeff n
      * (Complex.exp (2 * π * Complex.I * τ / (p : ℂ))
          * Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ j) ^ n)
      (∑ j ∈ Finset.range p, (f : ℍ → ℂ) (shiftDivP hp.pos j τ)) :=
    hasSum_finset_sum (Finset.range p) _ _ hj
  -- reshape the j-family with the root-of-unity filter
  have hfam : (fun n : ℕ => ∑ j ∈ Finset.range p, (qExpansion 1 f).coeff n
      * (Complex.exp (2 * π * Complex.I * τ / (p : ℂ))
          * Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ j) ^ n)
      = fun n : ℕ => (qExpansion 1 f).coeff n
          * Complex.exp (2 * π * Complex.I * τ / (p : ℂ)) ^ n
          * (if p ∣ n then (p : ℂ) else 0) := by
    funext n
    have hterm : ∀ j ∈ Finset.range p,
        ((qExpansion 1 f).coeff n
          * (Complex.exp (2 * π * Complex.I * τ / (p : ℂ))
              * Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ j) ^ n)
        = (qExpansion 1 f).coeff n
            * Complex.exp (2 * π * Complex.I * τ / (p : ℂ)) ^ n
            * Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ (j * n) := by
      intro j _
      rw [mul_pow, ← pow_mul]
      ring
    have hfac : ∑ j ∈ Finset.range p,
        ((qExpansion 1 f).coeff n
          * Complex.exp (2 * π * Complex.I * τ / (p : ℂ)) ^ n
          * Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ (j * n))
        = ((qExpansion 1 f).coeff n
            * Complex.exp (2 * π * Complex.I * τ / (p : ℂ)) ^ n)
          * ∑ j ∈ Finset.range p,
            Complex.exp (2 * π * Complex.I / (p : ℂ)) ^ (j * n) := by rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl hterm, hfac, sum_xi_pow hp n]
  rw [hfam] at hsumj
  -- convert to the padded family and strip the factor `p`
  have hfam2 : (fun n : ℕ => (qExpansion 1 f).coeff n
        * Complex.exp (2 * π * Complex.I * τ / (p : ℂ)) ^ n
        * (if p ∣ n then (p : ℂ) else 0))
      = fun n : ℕ => if p ∣ n then
          ((p : ℂ) * ((qExpansion 1 f).coeff (p * (n / p)) * 𝕢 1 τ ^ (n / p))) else 0 := by
    funext n
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [ite_eq_left (dvd_mul_right p m), ite_eq_left (dvd_mul_right p m),
        Nat.mul_div_cancel_left _ hp.pos, pow_mul, rho_pow_p hp.pos τ]
      ring
    · rw [ite_eq_right hpn, ite_eq_right hpn, mul_zero]
  rw [hfam2] at hsumj
  have hu : HasSum (fun m => (p : ℂ) * ((qExpansion 1 f).coeff (p * m) * 𝕢 1 τ ^ m))
      (∑ j ∈ Finset.range p, (f : ℍ → ℂ) (shiftDivP hp.pos j τ)) :=
    hasSum_unpadMul
      (u := fun m => (p : ℂ) * ((qExpansion 1 f).coeff (p * m) * 𝕢 1 τ ^ m)) hp.pos hsumj
  have hc : HasSum (fun m => (p : ℂ)⁻¹ *
        ((p : ℂ) * ((qExpansion 1 f).coeff (p * m) * 𝕢 1 τ ^ m)))
      ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, (f : ℍ → ℂ) (shiftDivP hp.pos j τ)) := by
    simpa [smul_eq_mul] using hu.const_smul ((p : ℂ)⁻¹)
  have hu' : HasSum (fun m => (qExpansion 1 f).coeff (p * m) * 𝕢 1 τ ^ m)
      ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, (f : ℍ → ℂ) (shiftDivP hp.pos j τ)) :=
    HasSum.congr_fun hc (fun m => by
      rw [inv_mul_cancel_left₀ (by exact_mod_cast hp.pos.ne' : ((p : ℂ)) ≠ 0)])
  -- combine
  have hc2 : HasSum (fun m : ℕ => (qExpansion 1 f).coeff (p * m) * 𝕢 1 τ ^ m
      + (p : ℂ) ^ (k - 1)
        * (if p ∣ m then (qExpansion 1 f).coeff (m / p) * 𝕢 1 τ ^ m else 0))
      ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, (f : ℍ → ℂ) (shiftDivP hp.pos j τ)
        + (p : ℂ) ^ (k - 1) * (f : ℍ → ℂ) (mulP hp.pos τ)) := hu'.add hpz'
  have hval : (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, (f : ℍ → ℂ) (shiftDivP hp.pos j τ)
      + (p : ℂ) ^ (k - 1) * (f : ℍ → ℂ) (mulP hp.pos τ)
      = heckeTPFun hp.pos k (f : ℍ → ℂ) τ := rfl
  rw [← hval]
  refine HasSum.congr_fun hc2 (fun m => ?_)
  by_cases hpm : p ∣ m
  · rw [ite_eq_left hpm, ite_eq_left hpm]
    ring
  · rw [ite_eq_right hpm, ite_eq_right hpm]
    ring

/-- **Coefficient formula for `T_p`**: `(T_p f)_m = f_{p m} + p^(k-1) [p ∣ m] f_{m / p}`. -/
theorem heckeTP_qExpansion_coeff (hp : p.Prime) {k : ℤ} (f : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 (heckeTP hp f)).coeff m
      = (qExpansion 1 (f : CuspForm 𝒮ℒ k)).coeff (p * m)
        + (p : ℂ) ^ (k - 1)
          * (if p ∣ m then (qExpansion 1 (f : CuspForm 𝒮ℒ k)).coeff (m / p) else 0) := by
  have h := ModularFormClass.qExpansion_coeff_unique (f := heckeTP hp f)
    (c := fun n => (qExpansion 1 (f : CuspForm 𝒮ℒ k)).coeff (p * n)
      + (p : ℂ) ^ (k - 1)
        * (if p ∣ n then (qExpansion 1 (f : CuspForm 𝒮ℒ k)).coeff (n / p) else 0))
    one_pos one_mem_strictPeriods_SL
    (fun τ => by
      simpa [smul_eq_mul] using heckeTP_qExpansion_hasSum hp f τ) m
  exact h.symm

end QFormula

end HeckeLevelOne
