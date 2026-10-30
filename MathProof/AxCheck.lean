import MathProof.Tau.LehmerMod
import MathProof.Tau.CongruenceSmall
import MathProof.Tau.Bridge
import MathProof.ModularForms.Congruence691
import MathProof.Tau.Mordell
import MathProof.Tau.LehmerSieve691

/-!
# Axiom audit of the headline theorems

`#print axioms` for the headline theorems living in the light modules (plus
`LehmerMod`, which this file already imports).  The computational theorems
must depend on `propext` alone (no `Classical.choice`, no `Quot.sound`, and of
course no `sorryAx`); the analytic ones may use the standard three.  This
module exists to make the audit a one-command check:

    modal run lean_check.py --target MathProof.AxCheck

The headline theorems of the remaining heavy modules — which it would be
prohibitively expensive to build here (`LehmerPow32` alone needs ~144 GiB of
kernel heap) — carry their own `#print axioms` lines at the end of their
files, printed whenever those modules are built on Modal:
`LehmerPacked` (`tau_ne_zero_of_le_65536`), `LehmerPow32`
(`tau_prime_pow_ne_zero_of_le_two_pow_32`), `LehmerGrand` (`tau_ne_zero_grand`).
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
#print axioms Ramanujan.tau_mul_coprime
#print axioms Ramanujan.tau_ne_zero_of_not_dvd_sigma
#print axioms Ramanujan.tau_prime_ne_zero_of_mod
#print axioms Ramanujan.tau_two_pow_ne_zero_sieve
#print axioms Ramanujan.tau_of_65537_ne_zero
#print axioms Ramanujan.tau_of_2147483647_ne_zero
