import MathProof.Basic
import MathProof.Tau.Basic
import MathProof.Tau.Lehmer
-- The heavy kernel-decide modules are deliberately NOT imported here:
-- importing the root must stay cheap for downstream consumers (LehmerMod
-- needs ~6 GB and LehmerPacked ~63 GiB of kernel heap).  Import them
-- directly when you want them; they are verified on Modal, not by default.
-- import MathProof.Tau.LehmerMod
-- import MathProof.Tau.LehmerPacked
import MathProof.Tau.CongruenceSmall
import MathProof.Tau.Bridge
import MathProof.ModularForms.HeckeLevelOne
import MathProof.ModularForms.Congruence691
import MathProof.Tau.Mordell
-- MathProof.AxCheck is also opt-in: it imports LehmerMod (heavy) to audit it.
-- import MathProof.AxCheck
