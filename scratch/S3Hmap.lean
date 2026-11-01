import MathProof.ModularForms.RabinCert

open Polynomial

noncomputable def P : ℤ[X] :=
  (X : ℤ[X]) ^ 6 + - C (66157336440) * (X : ℤ[X]) ^ 5 + - C (9002758724278005040128) * (X : ℤ[X]) ^ 4 + C (500728382584538732877523640647680) * (X : ℤ[X]) ^ 3 + C (19397273510102970423350650896766446839267328) * (X : ℤ[X]) ^ 2 + - C (841390377086653548715101191193731810412939033433866240) * (X : ℤ[X]) ^ 1 + C (4171558450151166049898984513691112295971825841981859595680743424)

noncomputable def fr : List ℤ := [90, 23, 4, 83, 94, 8, 1]

example : (RabinCert.toPoly 107 fr).leadingCoeff = 1 := by
  simp only [RabinCert.toPoly_nil, RabinCert.toPoly_cons, fr]
  trace_state
  sorry

example : C ((1 : ℤ) : ZMod 107) = 1 := by
  simp only [Int.cast_ofNat]
  trace_state
  sorry
