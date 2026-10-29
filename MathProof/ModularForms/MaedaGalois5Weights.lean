import MathProof.ModularForms.MaedaGalois5
import MathProof.ModularForms.MaedaDim5Weights

/-!
# Maeda's conjecture in full for dimension 5: Galois group `S₅`

For the six level-one weights with `dim S_k = 5` (`k = 60, 64, 66, 68, 70, 74`),
`MathProof/ModularForms/MaedaDim5Weights.lean` proves the characteristic
polynomial `P` of `T₂` irreducible.  Here we prove its Galois group is all of
`S₅`, via `galActionHom_bijective_of_quintic`: for each weight the discriminant
`disc5` of `P` is a non-square (non-residue mod a small prime) and the `F₂₀`
resolvent `resolvent5` has no root mod a small prime, hence no rational root
(integral root theorem).  The integers in this file are only certificates —
Lean re-checks everything: `Dval` and `R` are *defined* as `disc5`/`resolvent5`
applied to the coefficients, so the transport lemmas close definitionally.
-/

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

-- generated certificates: the integer literals cannot be line-broken
set_option linter.style.longLine false

namespace MaedaGalois

/-! ### Weight 60 -/

namespace Weight60

/-- The discriminant of the weight-60 quintic (its characteristic polynomial
is `MaedaWeight60.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 449691864 (-2209450184054433792) (-736010060393513697870348288)
     810634763334812972416233648439689216 263222216157060824115203098902237248565018624

/-- The discriminant is not a square mod 37. -/
lemma nonsquare : ∀ x : ZMod 37, ((Dval : ℤ) : ZMod 37) ≠ x * x := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-60 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (9430258577272576717381735492236607488) * X ^ 5
    + C (20709276947369043242445796388558198383189452353467250412828656007496335360) * X ^ 4
    + C ((-15431769817168592161597256572921481244214708856825682480238360423144989851762289837651681735032835282630082560)) * X ^ 3
    + C ((-38319049059405197160991265737062502329894001952481965135478050641346106153603002988209431112189666437255520966882500287635492754761205668181442560)) * X ^ 2
    + C (20133936860857832473415338025434111286113077656122946314823747727571983044276281714499011733786363218547555050191279273957095642507875073484399588431401570468802619233588684110430208) * X ^ 1
    + C (110965647638360068980513100688992882111968319592223981110462858359454772599152392611783933949695051774999629693302724349011435262485535011793740947575862096946121722869701343880315506342856998723223255557557257764864) * X ^ 0

lemma hRint : (resolvent5 449691864 (-2209450184054433792) (-736010060393513697870348288)
     810634763334812972416233648439689216 263222216157060824115203098902237248565018624 : ℤ[X]) = R := by
  unfold resolvent5 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- `R` reduced mod 41, as a computable function (`Polynomial` is not). -/
def Rmod (y : ZMod 41) : ZMod 41 :=
  y ^ 6
    + ((9430258577272576717381735492236607488 : ℤ) : ZMod 41) * y ^ 5
    + ((20709276947369043242445796388558198383189452353467250412828656007496335360 : ℤ) : ZMod 41) * y ^ 4
    + (((-15431769817168592161597256572921481244214708856825682480238360423144989851762289837651681735032835282630082560) : ℤ) : ZMod 41) * y ^ 3
    + (((-38319049059405197160991265737062502329894001952481965135478050641346106153603002988209431112189666437255520966882500287635492754761205668181442560) : ℤ) : ZMod 41) * y ^ 2
    + ((20133936860857832473415338025434111286113077656122946314823747727571983044276281714499011733786363218547555050191279273957095642507875073484399588431401570468802619233588684110430208 : ℤ) : ZMod 41) * y ^ 1
    + ((110965647638360068980513100688992882111968319592223981110462858359454772599152392611783933949695051774999629693302724349011435262485535011793740947575862096946121722869701343880315506342856998723223255557557257764864 : ℤ) : ZMod 41) * y ^ 0

/-- The resolvent has no root mod 41. -/
lemma noRootR : ∀ y : ZMod 41, Rmod y ≠ 0 := by
  decide +kernel

lemma R_eval_cast (n : ℤ) : (((R : ℤ[X]).eval n : ℤ) : ZMod 41) = Rmod (n : ZMod 41) := by
  simp [R, Rmod]

lemma hP : MaedaWeight60.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C (449691864 : ℚ) * X ^ 4 + C ((-2209450184054433792) : ℚ) * X ^ 3
      + C ((-736010060393513697870348288) : ℚ) * X ^ 2 + C (810634763334812972416233648439689216 : ℚ) * X
      + C (263222216157060824115203098902237248565018624 : ℚ) := by
  simp [MaedaWeight60.P, map_ofNat]

lemma hR : resolvent5 (449691864 : ℚ) ((-2209450184054433792) : ℚ) ((-736010060393513697870348288) : ℚ)
       (810634763334812972416233648439689216 : ℚ)
       (263222216157060824115203098902237248565018624 : ℚ)
    = (R : ℤ[X]).map (Int.castRingHom ℚ) := by
  rw [← hRint]
  exact resolvent5_map (Int.castRingHom ℚ) _ _ _ _ _

/-- **Maeda's conjecture in weight 60, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_60` acts on its five roots as `S₅`. -/
theorem maeda_galois60 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight60.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight60.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_quintic hirr ?_ ?_
  · -- the discriminant is not a square
    intro hs
    have hD : disc5 (449691864 : ℚ) ((-2209450184054433792) : ℚ) ((-736010060393513697870348288) : ℚ)
         (810634763334812972416233648439689216 : ℚ)
         (263222216157060824115203098902237248565018624 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    have h := congrArg (fun z : ℤ => (z : ZMod 37)) hn
    push_cast at h
    exact nonsquare n h
  · -- no rational root: the integral root theorem reduces to `noRootR`
    rintro r hr
    have hr' : aeval r (R : ℤ[X]) = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, ← hR]
      exact hr
    -- evaluation over `ℚ` is the cast of the integer evaluation
    have hE : ∀ m : ℤ, aeval (m : ℚ) (R : ℤ[X]) = (((R : ℤ[X]).eval m : ℤ) : ℚ) := by
      intro m
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial b c => simp
    obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic (p := (R : ℤ[X])) R_monic hr'
    have h3 : ((R : ℤ[X]).eval n : ℤ) = 0 := by
      rw [hn, algebraMap_int_eq, eq_intCast, hE n] at hr'
      exact_mod_cast hr'
    refine noRootR (n : ZMod 41) ?_
    rw [← R_eval_cast, h3, Int.cast_zero]

end Weight60

/-! ### Weight 64 -/

namespace Weight64

/-- The discriminant of the weight-64 quintic (its characteristic polynomial
is `MaedaWeight64.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 (-507315096) (-26316207229657439232) 7816999697067374824780726272
     93356730870958242939964792647614201856 59899702063757157544982491709928053576589901824

/-- The discriminant is not a square mod 29. -/
lemma nonsquare : ∀ x : ZMod 29, ((Dval : ℤ) : ZMod 29) ≠ x * x := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-64 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (949430036516581254110454395786659627008) * X ^ 5
    + C (100273093319938546871860791724363425063451341377203003140250573624328752988160) * X ^ 4
    + C ((-64565799852377461169517516739280290429871382115895570981088944194214641482298089746082120151226506492042196822261760)) * X ^ 3
    + C (1448580039003262353999616883013020593997391333159989976641551838634136868862986390000975472536252818853451798067071056406255990730682499497949392629923840) * X ^ 2
    + C (359557238851119208761890836979577934586289785324771345362942740097047799432988830133349738553804339164725487642401734037171420763377276411943119408348770559128269407287268343291526523343863808) * X ^ 1
    + C (650365500300917812398086685816790685112871278119679279010206436698813443238395461413800423505215561711822549501478380479005729710690609858245806782957014368490108071360492595703295753944877448376560764921318060016644207855796224) * X ^ 0

lemma hRint : (resolvent5 (-507315096) (-26316207229657439232) 7816999697067374824780726272
     93356730870958242939964792647614201856 59899702063757157544982491709928053576589901824 : ℤ[X]) = R := by
  unfold resolvent5 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- `R` reduced mod 31, as a computable function (`Polynomial` is not). -/
def Rmod (y : ZMod 31) : ZMod 31 :=
  y ^ 6
    + ((949430036516581254110454395786659627008 : ℤ) : ZMod 31) * y ^ 5
    + ((100273093319938546871860791724363425063451341377203003140250573624328752988160 : ℤ) : ZMod 31) * y ^ 4
    + (((-64565799852377461169517516739280290429871382115895570981088944194214641482298089746082120151226506492042196822261760) : ℤ) : ZMod 31) * y ^ 3
    + ((1448580039003262353999616883013020593997391333159989976641551838634136868862986390000975472536252818853451798067071056406255990730682499497949392629923840 : ℤ) : ZMod 31) * y ^ 2
    + ((359557238851119208761890836979577934586289785324771345362942740097047799432988830133349738553804339164725487642401734037171420763377276411943119408348770559128269407287268343291526523343863808 : ℤ) : ZMod 31) * y ^ 1
    + ((650365500300917812398086685816790685112871278119679279010206436698813443238395461413800423505215561711822549501478380479005729710690609858245806782957014368490108071360492595703295753944877448376560764921318060016644207855796224 : ℤ) : ZMod 31) * y ^ 0

/-- The resolvent has no root mod 31. -/
lemma noRootR : ∀ y : ZMod 31, Rmod y ≠ 0 := by
  decide +kernel

lemma R_eval_cast (n : ℤ) : (((R : ℤ[X]).eval n : ℤ) : ZMod 31) = Rmod (n : ZMod 31) := by
  simp [R, Rmod]

lemma hP : MaedaWeight64.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C ((-507315096) : ℚ) * X ^ 4 + C ((-26316207229657439232) : ℚ) * X ^ 3
      + C (7816999697067374824780726272 : ℚ) * X ^ 2 + C (93356730870958242939964792647614201856 : ℚ) * X
      + C (59899702063757157544982491709928053576589901824 : ℚ) := by
  simp [MaedaWeight64.P, map_ofNat]

lemma hR : resolvent5 ((-507315096) : ℚ) ((-26316207229657439232) : ℚ) (7816999697067374824780726272 : ℚ)
       (93356730870958242939964792647614201856 : ℚ)
       (59899702063757157544982491709928053576589901824 : ℚ)
    = (R : ℤ[X]).map (Int.castRingHom ℚ) := by
  rw [← hRint]
  exact resolvent5_map (Int.castRingHom ℚ) _ _ _ _ _

/-- **Maeda's conjecture in weight 64, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_64` acts on its five roots as `S₅`. -/
theorem maeda_galois64 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight64.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight64.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_quintic hirr ?_ ?_
  · -- the discriminant is not a square
    intro hs
    have hD : disc5 ((-507315096) : ℚ) ((-26316207229657439232) : ℚ) (7816999697067374824780726272 : ℚ)
         (93356730870958242939964792647614201856 : ℚ)
         (59899702063757157544982491709928053576589901824 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    have h := congrArg (fun z : ℤ => (z : ZMod 29)) hn
    push_cast at h
    exact nonsquare n h
  · -- no rational root: the integral root theorem reduces to `noRootR`
    rintro r hr
    have hr' : aeval r (R : ℤ[X]) = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, ← hR]
      exact hr
    -- evaluation over `ℚ` is the cast of the integer evaluation
    have hE : ∀ m : ℤ, aeval (m : ℚ) (R : ℤ[X]) = (((R : ℤ[X]).eval m : ℤ) : ℚ) := by
      intro m
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial b c => simp
    obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic (p := (R : ℤ[X])) R_monic hr'
    have h3 : ((R : ℤ[X]).eval n : ℤ) = 0 := by
      rw [hn, algebraMap_int_eq, eq_intCast, hE n] at hr'
      exact_mod_cast hr'
    refine noRootR (n : ZMod 31) ?_
    rw [← R_eval_cast, h3, Int.cast_zero]

end Weight64

/-! ### Weight 66 -/

namespace Weight66

/-- The discriminant of the weight-66 quintic (its characteristic polynomial
is `MaedaWeight66.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 3959709648 (-142850166119005483008) (-339986038308627409973683421184)
     4888759358323485530147825225712235708416
     6737365607750178848535412403321340119893376237568

/-- The discriminant is not a square mod 29. -/
lemma nonsquare : ∀ x : ZMod 29, ((Dval : ℤ) : ZMod 29) ≠ x * x := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-66 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (54272577567538733529118434932962086617088) * X ^ 5
    + C (892509037830012827776151690407180213554054922980238436359133205227230222205583360) * X ^ 4
    + C (1902270111904090294310450143388878718892815724452536589331690281399605228662495317137508199589168590149408194058193469440) * X ^ 3
    + C ((-57256600183689842383308535892157700209659715742463437418794754024962759386873156050690432739965293122347426926517749034463904121239269989725491919106628711874560)) * X ^ 2
    + C ((-181948856407546688304108149727104184114072418529223099376846665445236801454040971977180095252707288443235065964417086343246916688060483226354467453999430858023286524504200121472277137523457029195169792)) * X ^ 1
    + C (1361000594318003296062432712399101317439022778798317296562110586198553485488280059725025097525358619245650480633982688983651659702657435823932715227731903877291962776003078642845226164665996129797067241754185650978706091479849695846454001664) * X ^ 0

lemma hRint : (resolvent5 3959709648 (-142850166119005483008) (-339986038308627409973683421184)
     4888759358323485530147825225712235708416
     6737365607750178848535412403321340119893376237568 : ℤ[X]) = R := by
  unfold resolvent5 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- `R` reduced mod 29, as a computable function (`Polynomial` is not). -/
def Rmod (y : ZMod 29) : ZMod 29 :=
  y ^ 6
    + ((54272577567538733529118434932962086617088 : ℤ) : ZMod 29) * y ^ 5
    + ((892509037830012827776151690407180213554054922980238436359133205227230222205583360 : ℤ) : ZMod 29) * y ^ 4
    + ((1902270111904090294310450143388878718892815724452536589331690281399605228662495317137508199589168590149408194058193469440 : ℤ) : ZMod 29) * y ^ 3
    + (((-57256600183689842383308535892157700209659715742463437418794754024962759386873156050690432739965293122347426926517749034463904121239269989725491919106628711874560) : ℤ) : ZMod 29) * y ^ 2
    + (((-181948856407546688304108149727104184114072418529223099376846665445236801454040971977180095252707288443235065964417086343246916688060483226354467453999430858023286524504200121472277137523457029195169792) : ℤ) : ZMod 29) * y ^ 1
    + ((1361000594318003296062432712399101317439022778798317296562110586198553485488280059725025097525358619245650480633982688983651659702657435823932715227731903877291962776003078642845226164665996129797067241754185650978706091479849695846454001664 : ℤ) : ZMod 29) * y ^ 0

/-- The resolvent has no root mod 29. -/
lemma noRootR : ∀ y : ZMod 29, Rmod y ≠ 0 := by
  decide +kernel

lemma R_eval_cast (n : ℤ) : (((R : ℤ[X]).eval n : ℤ) : ZMod 29) = Rmod (n : ZMod 29) := by
  simp [R, Rmod]

lemma hP : MaedaWeight66.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C (3959709648 : ℚ) * X ^ 4 + C ((-142850166119005483008) : ℚ) * X ^ 3
      + C ((-339986038308627409973683421184) : ℚ) * X ^ 2 + C (4888759358323485530147825225712235708416 : ℚ) * X
      + C (6737365607750178848535412403321340119893376237568 : ℚ) := by
  simp [MaedaWeight66.P, map_ofNat]

lemma hR : resolvent5 (3959709648 : ℚ) ((-142850166119005483008) : ℚ) ((-339986038308627409973683421184) : ℚ)
       (4888759358323485530147825225712235708416 : ℚ)
       (6737365607750178848535412403321340119893376237568 : ℚ)
    = (R : ℤ[X]).map (Int.castRingHom ℚ) := by
  rw [← hRint]
  exact resolvent5_map (Int.castRingHom ℚ) _ _ _ _ _

/-- **Maeda's conjecture in weight 66, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_66` acts on its five roots as `S₅`. -/
theorem maeda_galois66 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight66.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight66.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_quintic hirr ?_ ?_
  · -- the discriminant is not a square
    intro hs
    have hD : disc5 (3959709648 : ℚ) ((-142850166119005483008) : ℚ) ((-339986038308627409973683421184) : ℚ)
         (4888759358323485530147825225712235708416 : ℚ)
         (6737365607750178848535412403321340119893376237568 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    have h := congrArg (fun z : ℤ => (z : ZMod 29)) hn
    push_cast at h
    exact nonsquare n h
  · -- no rational root: the integral root theorem reduces to `noRootR`
    rintro r hr
    have hr' : aeval r (R : ℤ[X]) = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, ← hR]
      exact hr
    -- evaluation over `ℚ` is the cast of the integer evaluation
    have hE : ∀ m : ℤ, aeval (m : ℚ) (R : ℤ[X]) = (((R : ℤ[X]).eval m : ℤ) : ℚ) := by
      intro m
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial b c => simp
    obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic (p := (R : ℤ[X])) R_monic hr'
    have h3 : ((R : ℤ[X]).eval n : ℤ) = 0 := by
      rw [hn, algebraMap_int_eq, eq_intCast, hE n] at hr'
      exact_mod_cast hr'
    refine noRootR (n : ZMod 29) ?_
    rw [← R_eval_cast, h3, Int.cast_zero]

end Weight66

/-! ### Weight 68 -/

namespace Weight68

/-- The discriminant of the weight-68 quintic (its characteristic polynomial
is `MaedaWeight68.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 (-5554901256) (-528742419683384143872) 1360506199877236618906967212032
     50978026392314038029857853615859298205696
     (-224135116306806567372209572838489759238644853374976)

/-- The discriminant is not a square mod 23. -/
lemma nonsquare : ∀ x : ZMod 23, ((Dval : ℤ) : ZMod 23) ≠ x * x := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-68 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (540010174317115775259280558211662482505728) * X ^ 5
    + C (62431736396141564726798423846943759927700553161853325328288331326037639299659202560) * X ^ 4
    + C ((-3447497440845213159165157910100052365765617799916151434185462619099521282739416541007865969891410140501614504956940527861760)) * X ^ 3
    + C ((-140065886232592677043671325067029615376742349875753272562320272627801009118879697661278289126708296063428762709110636211721831904708662993484998610636933459985039360)) * X ^ 2
    + C (4376459184079064598188422343708243372874431854361431570736326867297043672045897286703891440076132167877997958857300951630261234247210756547751693156825777404716767027407330518568014530131082368227326558208) * X ^ 1
    + C (17274108755047250638277854906027597969915316394132666195461712876523440821593328568123169770247211744608476612469804419196128480785433247534951563793623687983736209955337222719880800200344983929659328153076828953379978458129479666391515643510784) * X ^ 0

lemma hRint : (resolvent5 (-5554901256) (-528742419683384143872) 1360506199877236618906967212032
     50978026392314038029857853615859298205696
     (-224135116306806567372209572838489759238644853374976) : ℤ[X]) = R := by
  unfold resolvent5 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- `R` reduced mod 23, as a computable function (`Polynomial` is not). -/
def Rmod (y : ZMod 23) : ZMod 23 :=
  y ^ 6
    + ((540010174317115775259280558211662482505728 : ℤ) : ZMod 23) * y ^ 5
    + ((62431736396141564726798423846943759927700553161853325328288331326037639299659202560 : ℤ) : ZMod 23) * y ^ 4
    + (((-3447497440845213159165157910100052365765617799916151434185462619099521282739416541007865969891410140501614504956940527861760) : ℤ) : ZMod 23) * y ^ 3
    + (((-140065886232592677043671325067029615376742349875753272562320272627801009118879697661278289126708296063428762709110636211721831904708662993484998610636933459985039360) : ℤ) : ZMod 23) * y ^ 2
    + ((4376459184079064598188422343708243372874431854361431570736326867297043672045897286703891440076132167877997958857300951630261234247210756547751693156825777404716767027407330518568014530131082368227326558208 : ℤ) : ZMod 23) * y ^ 1
    + ((17274108755047250638277854906027597969915316394132666195461712876523440821593328568123169770247211744608476612469804419196128480785433247534951563793623687983736209955337222719880800200344983929659328153076828953379978458129479666391515643510784 : ℤ) : ZMod 23) * y ^ 0

/-- The resolvent has no root mod 23. -/
lemma noRootR : ∀ y : ZMod 23, Rmod y ≠ 0 := by
  decide +kernel

lemma R_eval_cast (n : ℤ) : (((R : ℤ[X]).eval n : ℤ) : ZMod 23) = Rmod (n : ZMod 23) := by
  simp [R, Rmod]

lemma hP : MaedaWeight68.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C ((-5554901256) : ℚ) * X ^ 4 + C ((-528742419683384143872) : ℚ) * X ^ 3
      + C (1360506199877236618906967212032 : ℚ) * X ^ 2 + C (50978026392314038029857853615859298205696 : ℚ) * X
      + C ((-224135116306806567372209572838489759238644853374976) : ℚ) := by
  simp [MaedaWeight68.P, map_ofNat]

lemma hR : resolvent5 ((-5554901256) : ℚ) ((-528742419683384143872) : ℚ) (1360506199877236618906967212032 : ℚ)
       (50978026392314038029857853615859298205696 : ℚ)
       ((-224135116306806567372209572838489759238644853374976) : ℚ)
    = (R : ℤ[X]).map (Int.castRingHom ℚ) := by
  rw [← hRint]
  exact resolvent5_map (Int.castRingHom ℚ) _ _ _ _ _

/-- **Maeda's conjecture in weight 68, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_68` acts on its five roots as `S₅`. -/
theorem maeda_galois68 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight68.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight68.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_quintic hirr ?_ ?_
  · -- the discriminant is not a square
    intro hs
    have hD : disc5 ((-5554901256) : ℚ) ((-528742419683384143872) : ℚ) (1360506199877236618906967212032 : ℚ)
         (50978026392314038029857853615859298205696 : ℚ)
         ((-224135116306806567372209572838489759238644853374976) : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    have h := congrArg (fun z : ℤ => (z : ZMod 23)) hn
    push_cast at h
    exact nonsquare n h
  · -- no rational root: the integral root theorem reduces to `noRootR`
    rintro r hr
    have hr' : aeval r (R : ℤ[X]) = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, ← hR]
      exact hr
    -- evaluation over `ℚ` is the cast of the integer evaluation
    have hE : ∀ m : ℤ, aeval (m : ℚ) (R : ℤ[X]) = (((R : ℤ[X]).eval m : ℤ) : ℚ) := by
      intro m
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial b c => simp
    obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic (p := (R : ℤ[X])) R_monic hr'
    have h3 : ((R : ℤ[X]).eval n : ℤ) = 0 := by
      rw [hn, algebraMap_int_eq, eq_intCast, hE n] at hr'
      exact_mod_cast hr'
    refine noRootR (n : ZMod 23) ?_
    rw [← R_eval_cast, h3, Int.cast_zero]

end Weight68

/-! ### Weight 70 -/

namespace Weight70

/-- The discriminant of the weight-70 quintic (its characteristic polynomial
is `MaedaWeight70.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 18005734368 (-1942747456996431618048) (-14539211744046993293953166475264)
     613518461067953168654246762332094963122176
     4169744246282611427836654706819235757668276180615168

/-- The discriminant is not a square mod 41. -/
lemma nonsquare : ∀ x : ZMod 41, ((Dval : ℤ) : ZMod 41) ≠ x * x := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-70 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (7182341349013196352782459848065295337914368) * X ^ 5
    + C (9547304319448198081194130040243580392814837337134174801164375485551582253779423068160) * X ^ 4
    + C ((-15982750311160439715578111086197635772565299340551278074125130821697764702958022664669382397685038165009430996403337944010588160)) * X ^ 3
    + C ((-11399482095673377290982965523085558970212942199125788113545559170902853337981388458989039228203047081667476378270474651976320998289529292375205177875457654425800734146560)) * X ^ 2
    + C (11277031384205476494445034182234775198638821398979664022197219060098493456037798652880228099969091563094706980485909760549293433695846738789081314030971440762221656048775104784234594053711170358578331139239313408) * X ^ 1
    + C ((-480153623837779254224761386272125320881275879242685931679424216212025820180946307231338467291018759410682631652251207154932891230638864408996822840411877860769345530291842949890012084956777040751725550704471471655859320162987595155796569908253814685696)) * X ^ 0

lemma hRint : (resolvent5 18005734368 (-1942747456996431618048) (-14539211744046993293953166475264)
     613518461067953168654246762332094963122176
     4169744246282611427836654706819235757668276180615168 : ℤ[X]) = R := by
  unfold resolvent5 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- `R` reduced mod 41, as a computable function (`Polynomial` is not). -/
def Rmod (y : ZMod 41) : ZMod 41 :=
  y ^ 6
    + ((7182341349013196352782459848065295337914368 : ℤ) : ZMod 41) * y ^ 5
    + ((9547304319448198081194130040243580392814837337134174801164375485551582253779423068160 : ℤ) : ZMod 41) * y ^ 4
    + (((-15982750311160439715578111086197635772565299340551278074125130821697764702958022664669382397685038165009430996403337944010588160) : ℤ) : ZMod 41) * y ^ 3
    + (((-11399482095673377290982965523085558970212942199125788113545559170902853337981388458989039228203047081667476378270474651976320998289529292375205177875457654425800734146560) : ℤ) : ZMod 41) * y ^ 2
    + ((11277031384205476494445034182234775198638821398979664022197219060098493456037798652880228099969091563094706980485909760549293433695846738789081314030971440762221656048775104784234594053711170358578331139239313408 : ℤ) : ZMod 41) * y ^ 1
    + (((-480153623837779254224761386272125320881275879242685931679424216212025820180946307231338467291018759410682631652251207154932891230638864408996822840411877860769345530291842949890012084956777040751725550704471471655859320162987595155796569908253814685696) : ℤ) : ZMod 41) * y ^ 0

/-- The resolvent has no root mod 41. -/
lemma noRootR : ∀ y : ZMod 41, Rmod y ≠ 0 := by
  decide +kernel

lemma R_eval_cast (n : ℤ) : (((R : ℤ[X]).eval n : ℤ) : ZMod 41) = Rmod (n : ZMod 41) := by
  simp [R, Rmod]

lemma hP : MaedaWeight70.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C (18005734368 : ℚ) * X ^ 4 + C ((-1942747456996431618048) : ℚ) * X ^ 3
      + C ((-14539211744046993293953166475264) : ℚ) * X ^ 2 + C (613518461067953168654246762332094963122176 : ℚ) * X
      + C (4169744246282611427836654706819235757668276180615168 : ℚ) := by
  simp [MaedaWeight70.P, map_ofNat]

lemma hR : resolvent5 (18005734368 : ℚ) ((-1942747456996431618048) : ℚ) ((-14539211744046993293953166475264) : ℚ)
       (613518461067953168654246762332094963122176 : ℚ)
       (4169744246282611427836654706819235757668276180615168 : ℚ)
    = (R : ℤ[X]).map (Int.castRingHom ℚ) := by
  rw [← hRint]
  exact resolvent5_map (Int.castRingHom ℚ) _ _ _ _ _

/-- **Maeda's conjecture in weight 70, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_70` acts on its five roots as `S₅`. -/
theorem maeda_galois70 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight70.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight70.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_quintic hirr ?_ ?_
  · -- the discriminant is not a square
    intro hs
    have hD : disc5 (18005734368 : ℚ) ((-1942747456996431618048) : ℚ) ((-14539211744046993293953166475264) : ℚ)
         (613518461067953168654246762332094963122176 : ℚ)
         (4169744246282611427836654706819235757668276180615168 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    have h := congrArg (fun z : ℤ => (z : ZMod 41)) hn
    push_cast at h
    exact nonsquare n h
  · -- no rational root: the integral root theorem reduces to `noRootR`
    rintro r hr
    have hr' : aeval r (R : ℤ[X]) = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, ← hR]
      exact hr
    -- evaluation over `ℚ` is the cast of the integer evaluation
    have hE : ∀ m : ℤ, aeval (m : ℚ) (R : ℤ[X]) = (((R : ℤ[X]).eval m : ℤ) : ℚ) := by
      intro m
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial b c => simp
    obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic (p := (R : ℤ[X])) R_monic hr'
    have h3 : ((R : ℤ[X]).eval n : ℤ) = 0 := by
      rw [hn, algebraMap_int_eq, eq_intCast, hE n] at hr'
      exact_mod_cast hr'
    refine noRootR (n : ZMod 41) ?_
    rw [← R_eval_cast, h3, Int.cast_zero]

end Weight70

/-! ### Weight 74 -/

namespace Weight74

/-- The discriminant of the weight-74 quintic (its characteristic polynomial
is `MaedaWeight74.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 92089333488 (-19817164982845968703488) (-1377989142595747748686715833810944)
     11802708847432637761332792635527627366465536
     113628227457643966226006850359168010340399423074336768

/-- The discriminant is not a square mod 41. -/
lemma nonsquare : ∀ x : ZMod 41, ((Dval : ℤ) : ZMod 41) ≠ x * x := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-74 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (625619495255698379211472680176500305505026048) * X ^ 5
    + C (49063871621174392225559322379087901901252892447961094186983284320127665063990951212482560) * X ^ 4
    + C ((-18804377585718950451945283027912693686771925285166918228116986964167838042927821768379538471837349012800495153885030625793974793666560)) * X ^ 3
    + C ((-513458932188859174934048803652382615050226471620451523413566237938446486368833852994812908590718439945403608455443334115468721605096644315829634838455327276174919982156779356160)) * X ^ 2
    + C (141012553335931918676071598865557424036480313255179612876614339311647101187247594789003363990038857465558167959155470502170606419291264942891037002578615265947385891181112701614830032581840797939279973795754139895786897408) * X ^ 1
    + C ((-2218656573348070592506340079388943884379447422569910790970096047028640045510675214151418268459476340569369698799628024217945791565989412476469697210183270001603806333788414668984868645700067134027894166135334549967115860590031307110061307301304930993658498442592256)) * X ^ 0

lemma hRint : (resolvent5 92089333488 (-19817164982845968703488) (-1377989142595747748686715833810944)
     11802708847432637761332792635527627366465536
     113628227457643966226006850359168010340399423074336768 : ℤ[X]) = R := by
  unfold resolvent5 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- `R` reduced mod 37, as a computable function (`Polynomial` is not). -/
def Rmod (y : ZMod 37) : ZMod 37 :=
  y ^ 6
    + ((625619495255698379211472680176500305505026048 : ℤ) : ZMod 37) * y ^ 5
    + ((49063871621174392225559322379087901901252892447961094186983284320127665063990951212482560 : ℤ) : ZMod 37) * y ^ 4
    + (((-18804377585718950451945283027912693686771925285166918228116986964167838042927821768379538471837349012800495153885030625793974793666560) : ℤ) : ZMod 37) * y ^ 3
    + (((-513458932188859174934048803652382615050226471620451523413566237938446486368833852994812908590718439945403608455443334115468721605096644315829634838455327276174919982156779356160) : ℤ) : ZMod 37) * y ^ 2
    + ((141012553335931918676071598865557424036480313255179612876614339311647101187247594789003363990038857465558167959155470502170606419291264942891037002578615265947385891181112701614830032581840797939279973795754139895786897408 : ℤ) : ZMod 37) * y ^ 1
    + (((-2218656573348070592506340079388943884379447422569910790970096047028640045510675214151418268459476340569369698799628024217945791565989412476469697210183270001603806333788414668984868645700067134027894166135334549967115860590031307110061307301304930993658498442592256) : ℤ) : ZMod 37) * y ^ 0

/-- The resolvent has no root mod 37. -/
lemma noRootR : ∀ y : ZMod 37, Rmod y ≠ 0 := by
  decide +kernel

lemma R_eval_cast (n : ℤ) : (((R : ℤ[X]).eval n : ℤ) : ZMod 37) = Rmod (n : ZMod 37) := by
  simp [R, Rmod]

lemma hP : MaedaWeight74.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C (92089333488 : ℚ) * X ^ 4 + C ((-19817164982845968703488) : ℚ) * X ^ 3
      + C ((-1377989142595747748686715833810944) : ℚ) * X ^ 2 + C (11802708847432637761332792635527627366465536 : ℚ) * X
      + C (113628227457643966226006850359168010340399423074336768 : ℚ) := by
  simp [MaedaWeight74.P, map_ofNat]

lemma hR : resolvent5 (92089333488 : ℚ) ((-19817164982845968703488) : ℚ)
       ((-1377989142595747748686715833810944) : ℚ)
       (11802708847432637761332792635527627366465536 : ℚ)
       (113628227457643966226006850359168010340399423074336768 : ℚ)
    = (R : ℤ[X]).map (Int.castRingHom ℚ) := by
  rw [← hRint]
  exact resolvent5_map (Int.castRingHom ℚ) _ _ _ _ _

/-- **Maeda's conjecture in weight 74, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_74` acts on its five roots as `S₅`. -/
theorem maeda_galois74 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight74.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight74.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_quintic hirr ?_ ?_
  · -- the discriminant is not a square
    intro hs
    have hD : disc5 (92089333488 : ℚ) ((-19817164982845968703488) : ℚ)
         ((-1377989142595747748686715833810944) : ℚ)
         (11802708847432637761332792635527627366465536 : ℚ)
         (113628227457643966226006850359168010340399423074336768 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    have h := congrArg (fun z : ℤ => (z : ZMod 41)) hn
    push_cast at h
    exact nonsquare n h
  · -- no rational root: the integral root theorem reduces to `noRootR`
    rintro r hr
    have hr' : aeval r (R : ℤ[X]) = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, ← hR]
      exact hr
    -- evaluation over `ℚ` is the cast of the integer evaluation
    have hE : ∀ m : ℤ, aeval (m : ℚ) (R : ℤ[X]) = (((R : ℤ[X]).eval m : ℤ) : ℚ) := by
      intro m
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial b c => simp
    obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic (p := (R : ℤ[X])) R_monic hr'
    have h3 : ((R : ℤ[X]).eval n : ℤ) = 0 := by
      rw [hn, algebraMap_int_eq, eq_intCast, hE n] at hr'
      exact_mod_cast hr'
    refine noRootR (n : ZMod 37) ?_
    rw [← R_eval_cast, h3, Int.cast_zero]

end Weight74

end MaedaGalois

#print axioms MaedaGalois.Weight60.maeda_galois60
#print axioms MaedaGalois.Weight64.maeda_galois64
#print axioms MaedaGalois.Weight66.maeda_galois66
#print axioms MaedaGalois.Weight68.maeda_galois68
#print axioms MaedaGalois.Weight70.maeda_galois70
#print axioms MaedaGalois.Weight74.maeda_galois74
