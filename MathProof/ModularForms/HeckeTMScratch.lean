import MathProof.ModularForms.HeckeCommute

/-! SCRATCH probe round 2 (NOT registered; delete before commit). -/

open UpperHalfPlane ModularForm CuspForm HeckeLevelOne HeckeCommute MaedaLevelOne

-- PowerSeries coefficient of a difference
example (F G : PowerSeries ℂ) (n : ℕ) : (F - G).coeff n = F.coeff n - G.coeff n := by
  simp

-- sub_add_cancel name
example (a b : ℂ) : a - b + b = a := sub_add_cancel a b

-- eq_sub_of_add_eq
example (a b c : ℂ) (h : a + b = c) : a = c - b := eq_sub_of_add_eq h

-- dvd_pow_iff
#check @Nat.Prime.dvd_pow_iff
#check @Nat.eq_one_of_dvd_one
#check @Nat.mul_lt_mul_of_pos_right
#check @Nat.gcd_mul_left
#check @Nat.dvd_prime

-- minFac of a prime is itself
example {p : ℕ} (hp : p.Prime) : p.minFac = p := by
  rcases (Nat.dvd_prime hp).mp (Nat.minFac_dvd p) with h1 | h2
  · exact absurd h1 (by have := (Nat.minFac_prime (show p ≠ 1 from hp.ne_one)).one_lt; omega)
  · exact h2

-- qL subtraction via elementary hom algebra
example {k : ℤ} (f g : CuspForm 𝒮ℒ k) : qL k (f - g) = qL k f - qL k g := by
  have h : qL k (f - g) + qL k g = qL k f := by
    rw [← map_add, sub_add_cancel]
  exact eq_sub_of_add_eq h

-- strongRecOn usage shape
example (P : ℕ → Prop) (hP : ∀ m, (∀ y, y < m → P y) → P m) (m : ℕ) : P m :=
  Nat.strongRecOn m hP
