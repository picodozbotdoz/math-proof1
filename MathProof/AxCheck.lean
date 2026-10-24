import MathProof.Tau.LehmerMod
import MathProof.Tau.CongruenceSmall
import MathProof.Tau.Bridge
import MathProof.ModularForms.Congruence691

/-!
# Axiom audit of the headline theorems

`#print axioms` for every headline theorem of the project.  The computational
theorems must depend on `propext` alone (no `Classical.choice`, no
`Quot.sound`, and of course no `sorryAx`); the analytic ones may use the
standard three.  This module exists to make the audit a one-command check:

    modal run lean_check.py --target MathProof.AxCheck
-/

#print axioms Ramanujan.deltaCoeffsMod_512_nonvanishing
#print axioms Ramanujan.tau_ne_zero_of_le_512
#print axioms Ramanujan.tau_prime_ne_zero_of_le_512
#print axioms Ramanujan.tau_even_of_ne_one_mod_eight
#print axioms Ramanujan.tau_zero_mod_three_of_ne_one_mod_three
#print axioms Ramanujan.tau_div_two_and_three_of
#print axioms Ramanujan.tau_ne_zero_of_le_128
#print axioms Ramanujan.qExpansion_discriminant_coeff
#print axioms RamanujanCongruence.tau_modEq_sigma
