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
import MathProof.Tau.LehmerUnbounded
import MathProof.Tau.PowChain
import MathProof.Tau.LehmerSieve691
import MathProof.Tau.LehmerPrimeReduction
import MathProof.ModularForms.BernoulliHigh
import MathProof.ModularForms.EigenLevelOne
import MathProof.ModularForms.LehmerWeight16
import MathProof.ModularForms.LehmerWeight18
import MathProof.ModularForms.LehmerWeight20
import MathProof.ModularForms.LehmerWeight22
import MathProof.ModularForms.LehmerWeight26
import MathProof.ModularForms.MaedaWeight24
import MathProof.ModularForms.MaedaLevelOne
import MathProof.ModularForms.HeckeTPCoeff
import MathProof.ModularForms.MaedaSmallWeights
import MathProof.ModularForms.MaedaGalois
import MathProof.ModularForms.MaedaDim4
import MathProof.ModularForms.MaedaDim4Weights
import MathProof.ModularForms.MaedaGalois4
import MathProof.ModularForms.MaedaDim5
import MathProof.ModularForms.MaedaDim5Weights
import MathProof.ModularForms.Poly5
import MathProof.ModularForms.MaedaGalois5Defs
import MathProof.ModularForms.HornerCert
import MathProof.ModularForms.MaedaCertC
import MathProof.ModularForms.MaedaCertCExt
import MathProof.ModularForms.MaedaPermCriterion
import MathProof.ModularForms.CharpolyEngine
import MathProof.ModularForms.RabinCert
import MathProof.ModularForms.HeckeAlgebraQT2
import MathProof.ModularForms.CharpolyDimN
import MathProof.ModularForms.MaedaDim6Weights
import MathProof.ModularForms.MaedaDim7Weights
import MathProof.ModularForms.MaedaDim8Weights
import MathProof.ModularForms.MaedaDim9Weights
import MathProof.ModularForms.MaedaDim10Weights
import MathProof.ModularForms.HeckeCommute
import MathProof.ModularForms.HeckeGeneratedByT2
import MathProof.ModularForms.HeckeGeneratedByT2Weights
import MathProof.ModularForms.MaedaT3Dim6Weights
import MathProof.ModularForms.MaedaT3Dim7Weights
import MathProof.ModularForms.MaedaT3Dim8Weights
import MathProof.ModularForms.MaedaT3Dim9Weights
import MathProof.ModularForms.MaedaT3Dim10Weights
-- The T₃ stretch file (dims 2–5) is registered in the root only: it is a
-- light module (audited via AxCheckDecide) but deliberately NOT a
-- defaultTargets/CI item — see the note in lakefile.toml.
import MathProof.ModularForms.MaedaT3SmallWeights
import MathProof.ModularForms.FrobeniusCycleType
import MathProof.ModularForms.JordanPrimitive
import MathProof.ModularForms.MaedaGaloisFull
import MathProof.ModularForms.MaedaGaloisDim6Weights
import MathProof.ModularForms.MaedaGaloisDim7Weights
import MathProof.ModularForms.MaedaGaloisDim8Weights
import MathProof.ModularForms.MaedaGaloisDim9Weights
import MathProof.ModularForms.MaedaGaloisDim10Weights
-- MathProof.AxCheck is also opt-in: it imports LehmerMod (heavy) to audit it.
-- import MathProof.AxCheck
