import MathProof.ModularForms.MaedaGalois5
import MathProof.ModularForms.MaedaDim5Weights
import MathProof.ModularForms.HornerCert

/-!
# Maeda's conjecture in full for dimension 5: Galois group `S₅`

For the six level-one weights with `dim S_k = 5` (`k = 60, 64, 66, 68, 70, 74`),
`MathProof/ModularForms/MaedaDim5Weights.lean` proves the characteristic
polynomial `P` of `T₂` irreducible.  Here we prove its Galois group is all of
`S₅`, via `galActionHom_bijective_of_quintic`: for each weight the discriminant
`disc5` of `P` is a non-square (non-residue mod a small prime) and the `F₂₀`
resolvent `resolvent5` has no root mod a small prime, hence no rational root
(integral root theorem).  The integers in this file are only certificates —
Lean re-checks everything: `Dval_eq` re-derives the discriminant literal from
`disc5`, `hRint` the resolvent coefficients from `resolvent5`.  The residue
certificates are stated over `ℤ` / bounded `ℕ` (`HornerCert`), so they depend
on no axioms (`MaedaGalois5AxCheck`).
-/

open Polynomial HornerCert

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

namespace MaedaGalois

/-! ### Weight 60 -/

namespace Weight60

/-- The discriminant of the weight-60 quintic (its characteristic polynomial
is `MaedaWeight60.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 449691864 (-2209450184054433792) (-736010060393513697870348288)
     810634763334812972416233648439689216 263222216157060824115203098902237248565018624

/-- The discriminant as an explicit integer (`Dval_eq` re-derives it). -/
def Dlit : ℤ := (((13850994331161420 * 10 ^ 55 +
          1871352906681963940501765622699352191824151318148551212) * 10 ^ 55 +
          7247430049838892596241390653317287635205657706487912405) * 10 ^ 55 +
          8196907708695943315818020106135402362586110361600000000)

lemma Dval_eq : Dval = Dlit := by decide +kernel

/-- The discriminant is not a square mod 37: `Dlit − y²` has no root mod 37
(plain `ℤ` arithmetic, no axioms). -/
lemma nonsquare : ∀ y : ℕ, y < 37 → hornerZ [Dlit, 0, -1] y % 37 ≠ 0 := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-60 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (9430258577272576717381735492236607488) * X ^ 5
    + C (20709276947369043242445796388558198383189452353467250412828656007496335360) * X ^ 4
    + C ((-(1543176981716859216159725657292148124421470885682568248 * 10 ^ 55 +
          238360423144989851762289837651681735032835282630082560))) * X ^ 3
    + C ((-((383190490594051971609912657370625023 * 10 ^ 55 +
          2989400195248196513547805064134610615360300298820943111) * 10 ^ 55 +
          2189666437255520966882500287635492754761205668181442560))) * X ^ 2
    + C ((((20133936860857832 * 10 ^ 55 +
          4734153380254341112861130776561229463148237477275719830) * 10 ^ 55 +
          4427628171449901173378636321854755505019127927395709564) * 10 ^ 55 +
          2507875073484399588431401570468802619233588684110430208)) * X ^ 1
    + C ((((110965647638360068980513100688992882111968319592223 * 10 ^ 55 +
          9811104628583594547725991523926117839339496950517749996) * 10 ^ 55 +
          2969330272434901143526248553501179374094757586209694612) * 10 ^ 55 +
          1722869701343880315506342856998723223255557557257764864)) * X ^ 0

lemma hRint : (resolvent5 449691864 (-2209450184054433792) (-736010060393513697870348288)
     810634763334812972416233648439689216 263222216157060824115203098902237248565018624 : ℤ[X])
          = R := by
  unfold resolvent5 r5c5 r5c4 r5c3 r5c2 r5c2p0 r5c2p1 r5c1 r5c1p0 r5c1p1 r5c1p2
    r5c0 r5c0p0 r5c0p1 r5c0p2 r5c0p3 r5c0p4 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- The coefficients of `R`, constant term first (`Polynomial` is not
computable; `R_eval_eq` links the two). -/
def Rcs : List ℤ :=
  [(((110965647638360068980513100688992882111968319592223 * 10 ^ 55 +
          9811104628583594547725991523926117839339496950517749996) * 10 ^ 55 +
          2969330272434901143526248553501179374094757586209694612) * 10 ^ 55 +
          1722869701343880315506342856998723223255557557257764864),
    (((20133936860857832 * 10 ^ 55 + 4734153380254341112861130776561229463148237477275719830) *
          10 ^ 55 + 4427628171449901173378636321854755505019127927395709564) * 10 ^ 55 +
          2507875073484399588431401570468802619233588684110430208),
    (-((383190490594051971609912657370625023 * 10 ^ 55 +
          2989400195248196513547805064134610615360300298820943111) * 10 ^ 55 +
          2189666437255520966882500287635492754761205668181442560)),
    (-(1543176981716859216159725657292148124421470885682568248 * 10 ^ 55 +
          238360423144989851762289837651681735032835282630082560)),
    20709276947369043242445796388558198383189452353467250412828656007496335360,
    9430258577272576717381735492236607488,
    1]

/-- The resolvent has no root mod 41 (plain `ℤ` arithmetic, no axioms). -/
lemma noRootR : ∀ y : ℕ, y < 41 → hornerZ Rcs y % 41 ≠ 0 := by
  decide +kernel

lemma R_eval_eq (n : ℤ) : (R : ℤ[X]).eval n = hornerZ Rcs n := by
  simp only [R, Rcs, hornerZ, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

lemma hP : MaedaWeight60.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C (449691864 : ℚ) * X ^ 4 + C ((-2209450184054433792) : ℚ) * X ^ 3
      + C ((-736010060393513697870348288) : ℚ) * X ^ 2 + C (810634763334812972416233648439689216
          : ℚ) * X
      + C (263222216157060824115203098902237248565018624 : ℚ) := by
  simp [MaedaWeight60.P, map_ofNat]

lemma hR : resolvent5 (449691864 : ℚ) ((-2209450184054433792) : ℚ)
          ((-736010060393513697870348288) : ℚ)
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
    have hD : disc5 (449691864 : ℚ) ((-2209450184054433792) : ℚ) ((-736010060393513697870348288)
          : ℚ)
         (810634763334812972416233648439689216 : ℚ)
         (263222216157060824115203098902237248565018624 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    exact ne_sq_of_cert (by norm_num) nonsquare n (Dval_eq.symm.trans hn)
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
    exact no_root_of_cert (by norm_num) noRootR n (by rw [← R_eval_eq]; exact h3)

end Weight60

/-! ### Weight 64 -/

namespace Weight64

/-- The discriminant of the weight-64 quintic (its characteristic polynomial
is `MaedaWeight64.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 (-507315096) (-26316207229657439232) 7816999697067374824780726272
     93356730870958242939964792647614201856 59899702063757157544982491709928053576589901824

/-- The discriminant as an explicit integer (`Dval_eq` re-derives it). -/
def Dlit : ℤ := (((35105875914926122425957420 * 10 ^ 55 +
          4078355539820192504513072209513675138286471855047917825) * 10 ^ 55 +
          7322750046151528173317137103091052972698845124741126660) * 10 ^ 55 +
          5628437284376427352449960329584425088419731865600000000)

lemma Dval_eq : Dval = Dlit := by decide +kernel

/-- The discriminant is not a square mod 29: `Dlit − y²` has no root mod 29
(plain `ℤ` arithmetic, no axioms). -/
lemma nonsquare : ∀ y : ℕ, y < 29 → hornerZ [Dlit, 0, -1] y % 29 ≠ 0 := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-64 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (949430036516581254110454395786659627008) * X ^ 5
    + C (100273093319938546871860791724363425063451341377203003140250573624328752988160) * X ^ 4
    + C ((-((645657 * 10 ^ 55 + 9985237746116951751673928029042987138211589557098108894) * 10 ^
          55 + 4194214641482298089746082120151226506492042196822261760))) * X ^ 3
    + C (((14485800390032623539996168830130205939973913 * 10 ^ 55 +
          3315998997664155183863413686886298639000097547253625281) * 10 ^ 55 +
          8853451798067071056406255990730682499497949392629923840)) * X ^ 2
    + C ((((359557238851119208761890836 * 10 ^ 55 +
          9795779345862897853247713453629427400970477994329888301) * 10 ^ 55 +
          3334973855380433916472548764240173403717142076337727641) * 10 ^ 55 +
          1943119408348770559128269407287268343291526523343863808)) * X ^ 1
    + C (((((65036550 * 10 ^ 55 + 300917812398086685816790685112871278119679279010206436) * 10 ^
          55 + 6988134432383954614138004235052155617118225495014783804) * 10 ^ 55 +
          7900572971069060985824580678295701436849010807136049259) * 10 ^ 55 +
          5703295753944877448376560764921318060016644207855796224)) * X ^ 0

lemma hRint : (resolvent5 (-507315096) (-26316207229657439232) 7816999697067374824780726272
     93356730870958242939964792647614201856 59899702063757157544982491709928053576589901824 :
          ℤ[X]) = R := by
  unfold resolvent5 r5c5 r5c4 r5c3 r5c2 r5c2p0 r5c2p1 r5c1 r5c1p0 r5c1p1 r5c1p2
    r5c0 r5c0p0 r5c0p1 r5c0p2 r5c0p3 r5c0p4 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- The coefficients of `R`, constant term first (`Polynomial` is not
computable; `R_eval_eq` links the two). -/
def Rcs : List ℤ :=
  [((((65036550 * 10 ^ 55 + 300917812398086685816790685112871278119679279010206436) * 10 ^ 55 +
          6988134432383954614138004235052155617118225495014783804) * 10 ^ 55 +
          7900572971069060985824580678295701436849010807136049259) * 10 ^ 55 +
          5703295753944877448376560764921318060016644207855796224),
    (((359557238851119208761890836 * 10 ^ 55 +
          9795779345862897853247713453629427400970477994329888301) * 10 ^ 55 +
          3334973855380433916472548764240173403717142076337727641) * 10 ^ 55 +
          1943119408348770559128269407287268343291526523343863808),
    ((14485800390032623539996168830130205939973913 * 10 ^ 55 +
          3315998997664155183863413686886298639000097547253625281) * 10 ^ 55 +
          8853451798067071056406255990730682499497949392629923840),
    (-((645657 * 10 ^ 55 + 9985237746116951751673928029042987138211589557098108894) * 10 ^ 55 +
          4194214641482298089746082120151226506492042196822261760)),
    100273093319938546871860791724363425063451341377203003140250573624328752988160,
    949430036516581254110454395786659627008,
    1]

/-- The resolvent has no root mod 31 (plain `ℤ` arithmetic, no axioms). -/
lemma noRootR : ∀ y : ℕ, y < 31 → hornerZ Rcs y % 31 ≠ 0 := by
  decide +kernel

lemma R_eval_eq (n : ℤ) : (R : ℤ[X]).eval n = hornerZ Rcs n := by
  simp only [R, Rcs, hornerZ, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

lemma hP : MaedaWeight64.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C ((-507315096) : ℚ) * X ^ 4 + C ((-26316207229657439232) : ℚ) * X ^ 3
      + C (7816999697067374824780726272 : ℚ) * X ^ 2 + C (93356730870958242939964792647614201856
          : ℚ) * X
      + C (59899702063757157544982491709928053576589901824 : ℚ) := by
  simp [MaedaWeight64.P, map_ofNat]

lemma hR : resolvent5 ((-507315096) : ℚ) ((-26316207229657439232) : ℚ)
          (7816999697067374824780726272 : ℚ)
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
    have hD : disc5 ((-507315096) : ℚ) ((-26316207229657439232) : ℚ)
          (7816999697067374824780726272 : ℚ)
         (93356730870958242939964792647614201856 : ℚ)
         (59899702063757157544982491709928053576589901824 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    exact ne_sq_of_cert (by norm_num) nonsquare n (Dval_eq.symm.trans hn)
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
    exact no_root_of_cert (by norm_num) noRootR n (by rw [← R_eval_eq]; exact h3)

end Weight64

/-! ### Weight 66 -/

namespace Weight66

/-- The discriminant of the weight-66 quintic (its characteristic polynomial
is `MaedaWeight66.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 3959709648 (-142850166119005483008) (-339986038308627409973683421184)
     4888759358323485530147825225712235708416
     6737365607750178848535412403321340119893376237568

/-- The discriminant as an explicit integer (`Dval_eq` re-derives it). -/
def Dlit : ℤ := (((298197294692034368447976680932938 * 10 ^ 55 +
          9930933916314548247795184860612478723170293278287434630) * 10 ^ 55 +
          4815455798443938064654807264700376075992490463205241696) * 10 ^ 55 +
          6943718993320168308015403505061701540447361433600000000)

lemma Dval_eq : Dval = Dlit := by decide +kernel

/-- The discriminant is not a square mod 29: `Dlit − y²` has no root mod 29
(plain `ℤ` arithmetic, no axioms). -/
lemma nonsquare : ∀ y : ℕ, y < 29 → hornerZ [Dlit, 0, -1] y % 29 ≠ 0 := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-66 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (54272577567538733529118434932962086617088) * X ^ 5
    + C (892509037830012827776151690407180213554054922980238436359133205227230222205583360) * X ^ 4
    + C (((19022701119 * 10 ^ 55 + 409029431045014338887871889281572445253658933169028139) * 10
          ^ 55 + 9605228662495317137508199589168590149408194058193469440)) * X ^ 3
    + C ((-((572566001836898423833085358921577002096597157424634 * 10 ^ 55 +
          3741879475402496275938687315605069043273996529312234742) * 10 ^ 55 +
          6926517749034463904121239269989725491919106628711874560))) * X ^ 2
    + C ((-(((181948856407546688304108149727104184 * 10 ^ 55 +
          1140724185292230993768466654452368014540409719771800952) * 10 ^ 55 +
          5270728844323506596441708634324691668806048322635446745) * 10 ^ 55 +
          3999430858023286524504200121472277137523457029195169792))) * X ^ 1
    + C (((((136100059431800329606 * 10 ^ 55 +
          2432712399101317439022778798317296562110586198553485488) * 10 ^ 55 +
          2800597250250975253586192456504806339826889836516597026) * 10 ^ 55 +
          5743582393271522773190387729196277600307864284522616466) * 10 ^ 55 +
          5996129797067241754185650978706091479849695846454001664)) * X ^ 0

lemma hRint : (resolvent5 3959709648 (-142850166119005483008) (-339986038308627409973683421184)
     4888759358323485530147825225712235708416
     6737365607750178848535412403321340119893376237568 : ℤ[X]) = R := by
  unfold resolvent5 r5c5 r5c4 r5c3 r5c2 r5c2p0 r5c2p1 r5c1 r5c1p0 r5c1p1 r5c1p2
    r5c0 r5c0p0 r5c0p1 r5c0p2 r5c0p3 r5c0p4 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- The coefficients of `R`, constant term first (`Polynomial` is not
computable; `R_eval_eq` links the two). -/
def Rcs : List ℤ :=
  [((((136100059431800329606 * 10 ^ 55 +
          2432712399101317439022778798317296562110586198553485488) * 10 ^ 55 +
          2800597250250975253586192456504806339826889836516597026) * 10 ^ 55 +
          5743582393271522773190387729196277600307864284522616466) * 10 ^ 55 +
          5996129797067241754185650978706091479849695846454001664),
    (-(((181948856407546688304108149727104184 * 10 ^ 55 +
          1140724185292230993768466654452368014540409719771800952) * 10 ^ 55 +
          5270728844323506596441708634324691668806048322635446745) * 10 ^ 55 +
          3999430858023286524504200121472277137523457029195169792)),
    (-((572566001836898423833085358921577002096597157424634 * 10 ^ 55 +
          3741879475402496275938687315605069043273996529312234742) * 10 ^ 55 +
          6926517749034463904121239269989725491919106628711874560)),
    ((19022701119 * 10 ^ 55 + 409029431045014338887871889281572445253658933169028139) * 10 ^ 55
          + 9605228662495317137508199589168590149408194058193469440),
    892509037830012827776151690407180213554054922980238436359133205227230222205583360,
    54272577567538733529118434932962086617088,
    1]

/-- The resolvent has no root mod 29 (plain `ℤ` arithmetic, no axioms). -/
lemma noRootR : ∀ y : ℕ, y < 29 → hornerZ Rcs y % 29 ≠ 0 := by
  decide +kernel

lemma R_eval_eq (n : ℤ) : (R : ℤ[X]).eval n = hornerZ Rcs n := by
  simp only [R, Rcs, hornerZ, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

lemma hP : MaedaWeight66.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C (3959709648 : ℚ) * X ^ 4 + C ((-142850166119005483008) : ℚ) * X ^ 3
      + C ((-339986038308627409973683421184) : ℚ) * X ^ 2 + C
          (4888759358323485530147825225712235708416 : ℚ) * X
      + C (6737365607750178848535412403321340119893376237568 : ℚ) := by
  simp [MaedaWeight66.P, map_ofNat]

lemma hR : resolvent5 (3959709648 : ℚ) ((-142850166119005483008) : ℚ)
          ((-339986038308627409973683421184) : ℚ)
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
    have hD : disc5 (3959709648 : ℚ) ((-142850166119005483008) : ℚ)
          ((-339986038308627409973683421184) : ℚ)
         (4888759358323485530147825225712235708416 : ℚ)
         (6737365607750178848535412403321340119893376237568 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    exact ne_sq_of_cert (by norm_num) nonsquare n (Dval_eq.symm.trans hn)
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
    exact no_root_of_cert (by norm_num) noRootR n (by rw [← R_eval_eq]; exact h3)

end Weight66

/-! ### Weight 68 -/

namespace Weight68

/-- The discriminant of the weight-68 quintic (its characteristic polynomial
is `MaedaWeight68.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 (-5554901256) (-528742419683384143872) 1360506199877236618906967212032
     50978026392314038029857853615859298205696
     (-224135116306806567372209572838489759238644853374976)

/-- The discriminant as an explicit integer (`Dval_eq` re-derives it). -/
def Dlit : ℤ := (((1129025552320560851415506865630777002106 * 10 ^ 55 +
          4473286523022234569223181261743434406196019542753077320) * 10 ^ 55 +
          520418608469788285073862503944407354226788470702180333) * 10 ^ 55 +
          5321517463109449422860891279699907643713781760000000000)

lemma Dval_eq : Dval = Dlit := by decide +kernel

/-- The discriminant is not a square mod 23: `Dlit − y²` has no root mod 23
(plain `ℤ` arithmetic, no axioms). -/
lemma nonsquare : ∀ y : ℕ, y < 23 → hornerZ [Dlit, 0, -1] y % 23 ≠ 0 := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-68 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (540010174317115775259280558211662482505728) * X ^ 5
    + C ((6243173639614156472679842384 * 10 ^ 55 +
          6943759927700553161853325328288331326037639299659202560)) * X ^ 4
    + C ((-((34474974408452 * 10 ^ 55 + 1315916515791010005236576561779991615143418546261909952)
          * 10 ^ 55 + 1282739416541007865969891410140501614504956940527861760))) * X ^ 3
    + C ((-((1400658862325926770436713250670296153767423498757532725 * 10 ^ 55 +
          6232027262780100911887969766127828912670829606342876270) * 10 ^ 55 +
          9110636211721831904708662993484998610636933459985039360))) * X ^ 2
    + C ((((4376459184079064598188422343708243372874 * 10 ^ 55 +
          4318543614315707363268672970436720458972867038914400761) * 10 ^ 55 +
          3216787799795885730095163026123424721075654775169315682) * 10 ^ 55 +
          5777404716767027407330518568014530131082368227326558208)) * X ^ 1
    + C (((((1727410875504725063827785 * 10 ^ 55 +
          4906027597969915316394132666195461712876523440821593328) * 10 ^ 55 +
          5681231697702472117446084766124698044191961284807854332) * 10 ^ 55 +
          4753495156379362368798373620995533722271988080020034498) * 10 ^ 55 +
          3929659328153076828953379978458129479666391515643510784)) * X ^ 0

lemma hRint : (resolvent5 (-5554901256) (-528742419683384143872) 1360506199877236618906967212032
     50978026392314038029857853615859298205696
     (-224135116306806567372209572838489759238644853374976) : ℤ[X]) = R := by
  unfold resolvent5 r5c5 r5c4 r5c3 r5c2 r5c2p0 r5c2p1 r5c1 r5c1p0 r5c1p1 r5c1p2
    r5c0 r5c0p0 r5c0p1 r5c0p2 r5c0p3 r5c0p4 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- The coefficients of `R`, constant term first (`Polynomial` is not
computable; `R_eval_eq` links the two). -/
def Rcs : List ℤ :=
  [((((1727410875504725063827785 * 10 ^ 55 +
          4906027597969915316394132666195461712876523440821593328) * 10 ^ 55 +
          5681231697702472117446084766124698044191961284807854332) * 10 ^ 55 +
          4753495156379362368798373620995533722271988080020034498) * 10 ^ 55 +
          3929659328153076828953379978458129479666391515643510784),
    (((4376459184079064598188422343708243372874 * 10 ^ 55 +
          4318543614315707363268672970436720458972867038914400761) * 10 ^ 55 +
          3216787799795885730095163026123424721075654775169315682) * 10 ^ 55 +
          5777404716767027407330518568014530131082368227326558208),
    (-((1400658862325926770436713250670296153767423498757532725 * 10 ^ 55 +
          6232027262780100911887969766127828912670829606342876270) * 10 ^ 55 +
          9110636211721831904708662993484998610636933459985039360)),
    (-((34474974408452 * 10 ^ 55 + 1315916515791010005236576561779991615143418546261909952) * 10
          ^ 55 + 1282739416541007865969891410140501614504956940527861760)),
    62431736396141564726798423846943759927700553161853325328288331326037639299659202560,
    540010174317115775259280558211662482505728,
    1]

/-- The resolvent has no root mod 23 (plain `ℤ` arithmetic, no axioms). -/
lemma noRootR : ∀ y : ℕ, y < 23 → hornerZ Rcs y % 23 ≠ 0 := by
  decide +kernel

lemma R_eval_eq (n : ℤ) : (R : ℤ[X]).eval n = hornerZ Rcs n := by
  simp only [R, Rcs, hornerZ, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

lemma hP : MaedaWeight68.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C ((-5554901256) : ℚ) * X ^ 4 + C ((-528742419683384143872) : ℚ) * X ^ 3
      + C (1360506199877236618906967212032 : ℚ) * X ^ 2 + C
          (50978026392314038029857853615859298205696 : ℚ) * X
      + C ((-224135116306806567372209572838489759238644853374976) : ℚ) := by
  simp [MaedaWeight68.P, map_ofNat]

lemma hR : resolvent5 ((-5554901256) : ℚ) ((-528742419683384143872) : ℚ)
          (1360506199877236618906967212032 : ℚ)
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
    have hD : disc5 ((-5554901256) : ℚ) ((-528742419683384143872) : ℚ)
          (1360506199877236618906967212032 : ℚ)
         (50978026392314038029857853615859298205696 : ℚ)
         ((-224135116306806567372209572838489759238644853374976) : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    exact ne_sq_of_cert (by norm_num) nonsquare n (Dval_eq.symm.trans hn)
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
    exact no_root_of_cert (by norm_num) noRootR n (by rw [← R_eval_eq]; exact h3)

end Weight68

/-! ### Weight 70 -/

namespace Weight70

/-- The discriminant of the weight-70 quintic (its characteristic polynomial
is `MaedaWeight70.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 18005734368 (-1942747456996431618048) (-14539211744046993293953166475264)
     613518461067953168654246762332094963122176
     4169744246282611427836654706819235757668276180615168

/-- The discriminant as an explicit integer (`Dval_eq` re-derives it). -/
def Dlit : ℤ := (((4653661038408060497923465868056338614856767474 * 10 ^ 55 +
          3324388455949029358009865675538162444814229839778978104) * 10 ^ 55 +
          7403215159667914689402405011456932972907118227770113011) * 10 ^ 55 +
          7829901502814174272231013213969964363793039360000000000)

lemma Dval_eq : Dval = Dlit := by decide +kernel

/-- The discriminant is not a square mod 41: `Dlit − y²` has no root mod 41
(plain `ℤ` arithmetic, no axioms). -/
lemma nonsquare : ∀ y : ℕ, y < 41 → hornerZ [Dlit, 0, -1] y % 41 ≠ 0 := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-70 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (7182341349013196352782459848065295337914368) * X ^ 5
    + C ((954730431944819808119413004024 * 10 ^ 55 +
          3580392814837337134174801164375485551582253779423068160)) * X ^ 4
    + C ((-((159827503111604397 * 10 ^ 55 +
          1557811108619763577256529934055127807412513082169776470) * 10 ^ 55 +
          2958022664669382397685038165009430996403337944010588160))) * X ^ 3
    + C ((-(((11399 * 10 ^ 55 + 4820956733772909829655230855589702129421991257881135455) * 10 ^
          55 + 5917090285333798138845898903922820304708166747637827047) * 10 ^ 55 +
          4651976320998289529292375205177875457654425800734146560))) * X ^ 2
    + C ((((11277031384205476494445034182234775198638821398 * 10 ^ 55 +
          9796640221972190600984934560377986528802280999690915630) * 10 ^ 55 +
          9470698048590976054929343369584673878908131403097144076) * 10 ^ 55 +
          2221656048775104784234594053711170358578331139239313408)) * X ^ 1
    + C ((-((((48015362383777925422476138627212 * 10 ^ 55 +
          5320881275879242685931679424216212025820180946307231338) * 10 ^ 55 +
          4672910187594106826316522512071549328912306388644089968) * 10 ^ 55 +
          2284041187786076934553029184294989001208495677704075172) * 10 ^ 55 +
          5550704471471655859320162987595155796569908253814685696))) * X ^ 0

lemma hRint : (resolvent5 18005734368 (-1942747456996431618048) (-14539211744046993293953166475264)
     613518461067953168654246762332094963122176
     4169744246282611427836654706819235757668276180615168 : ℤ[X]) = R := by
  unfold resolvent5 r5c5 r5c4 r5c3 r5c2 r5c2p0 r5c2p1 r5c1 r5c1p0 r5c1p1 r5c1p2
    r5c0 r5c0p0 r5c0p1 r5c0p2 r5c0p3 r5c0p4 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- The coefficients of `R`, constant term first (`Polynomial` is not
computable; `R_eval_eq` links the two). -/
def Rcs : List ℤ :=
  [(-((((48015362383777925422476138627212 * 10 ^ 55 +
          5320881275879242685931679424216212025820180946307231338) * 10 ^ 55 +
          4672910187594106826316522512071549328912306388644089968) * 10 ^ 55 +
          2284041187786076934553029184294989001208495677704075172) * 10 ^ 55 +
          5550704471471655859320162987595155796569908253814685696)),
    (((11277031384205476494445034182234775198638821398 * 10 ^ 55 +
          9796640221972190600984934560377986528802280999690915630) * 10 ^ 55 +
          9470698048590976054929343369584673878908131403097144076) * 10 ^ 55 +
          2221656048775104784234594053711170358578331139239313408),
    (-(((11399 * 10 ^ 55 + 4820956733772909829655230855589702129421991257881135455) * 10 ^ 55 +
          5917090285333798138845898903922820304708166747637827047) * 10 ^ 55 +
          4651976320998289529292375205177875457654425800734146560)),
    (-((159827503111604397 * 10 ^ 55 + 1557811108619763577256529934055127807412513082169776470)
          * 10 ^ 55 + 2958022664669382397685038165009430996403337944010588160)),
    9547304319448198081194130040243580392814837337134174801164375485551582253779423068160,
    7182341349013196352782459848065295337914368,
    1]

/-- The resolvent has no root mod 41 (plain `ℤ` arithmetic, no axioms). -/
lemma noRootR : ∀ y : ℕ, y < 41 → hornerZ Rcs y % 41 ≠ 0 := by
  decide +kernel

lemma R_eval_eq (n : ℤ) : (R : ℤ[X]).eval n = hornerZ Rcs n := by
  simp only [R, Rcs, hornerZ, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

lemma hP : MaedaWeight70.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C (18005734368 : ℚ) * X ^ 4 + C ((-1942747456996431618048) : ℚ) * X ^ 3
      + C ((-14539211744046993293953166475264) : ℚ) * X ^ 2 + C
          (613518461067953168654246762332094963122176 : ℚ) * X
      + C (4169744246282611427836654706819235757668276180615168 : ℚ) := by
  simp [MaedaWeight70.P, map_ofNat]

lemma hR : resolvent5 (18005734368 : ℚ) ((-1942747456996431618048) : ℚ)
          ((-14539211744046993293953166475264) : ℚ)
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
    have hD : disc5 (18005734368 : ℚ) ((-1942747456996431618048) : ℚ)
          ((-14539211744046993293953166475264) : ℚ)
         (613518461067953168654246762332094963122176 : ℚ)
         (4169744246282611427836654706819235757668276180615168 : ℚ)
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    exact ne_sq_of_cert (by norm_num) nonsquare n (Dval_eq.symm.trans hn)
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
    exact no_root_of_cert (by norm_num) noRootR n (by rw [← R_eval_eq]; exact h3)

end Weight70

/-! ### Weight 74 -/

namespace Weight74

/-- The discriminant of the weight-74 quintic (its characteristic polynomial
is `MaedaWeight74.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 92089333488 (-19817164982845968703488) (-1377989142595747748686715833810944)
     11802708847432637761332792635527627366465536
     113628227457643966226006850359168010340399423074336768

/-- The discriminant as an explicit integer (`Dval_eq` re-derives it). -/
def Dlit : ℤ := ((((5 * 10 ^ 55 + 4572902739043989902938152780721180698611446175483062499) * 10
          ^ 55 + 351390842629834164145918165916078655526419328615868561) * 10 ^ 55 +
          7293633085142353854518807992806229536454685856569809291) * 10 ^ 55 +
          4727401888412827843986302671897757896146944000000000000)

lemma Dval_eq : Dval = Dlit := by decide +kernel

/-- The discriminant is not a square mod 41: `Dlit − y²` has no root mod 41
(plain `ℤ` arithmetic, no axioms). -/
lemma nonsquare : ∀ y : ℕ, y < 41 → hornerZ [Dlit, 0, -1] y % 41 ≠ 0 := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-74 quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  X ^ 6
    + C (625619495255698379211472680176500305505026048) * X ^ 5
    + C ((4906387162117439222555932237908790 * 10 ^ 55 +
          1901252892447961094186983284320127665063990951212482560)) * X ^ 4
    + C ((-((188043775857189504519452 * 10 ^ 55 +
          8302791269368677192528516691822811698696416783804292782) * 10 ^ 55 +
          1768379538471837349012800495153885030625793974793666560))) * X ^ 3
    + C ((-(((513458932188 * 10 ^ 55 + 8591749340488036523826150502264716204515234135662379384)
          * 10 ^ 55 + 4648636883385299481290859071843994540360845544333411546) * 10 ^ 55 +
          8721605096644315829634838455327276174919982156779356160))) * X ^ 2
    + C (((((14 * 10 ^ 55 + 1012553335931918676071598865557424036480313255179612876) * 10 ^ 55 +
          6143393116471011872475947890033639900388574655581679591) * 10 ^ 55 +
          5547050217060641929126494289103700257861526594738589118) * 10 ^ 55 +
          1112701614830032581840797939279973795754139895786897408)) * X ^ 1
    + C ((-((((221865657334807059250634007938894388437944742 * 10 ^ 55 +
          2569910790970096047028640045510675214151418268459476340) * 10 ^ 55 +
          5693696987996280242179457915659894124764696972101832700) * 10 ^ 55 +
          160380633378841466898486864570006713402789416613533454) * 10 ^ 55 +
          9967115860590031307110061307301304930993658498442592256))) * X ^ 0

lemma hRint : (resolvent5 92089333488 (-19817164982845968703488)
          (-1377989142595747748686715833810944)
     11802708847432637761332792635527627366465536
     113628227457643966226006850359168010340399423074336768 : ℤ[X]) = R := by
  unfold resolvent5 r5c5 r5c4 r5c3 r5c2 r5c2p0 r5c2p1 r5c1 r5c1p0 r5c1p1 r5c1p2
    r5c0 r5c0p0 r5c0p1 r5c0p2 r5c0p3 r5c0p4 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- The coefficients of `R`, constant term first (`Polynomial` is not
computable; `R_eval_eq` links the two). -/
def Rcs : List ℤ :=
  [(-((((221865657334807059250634007938894388437944742 * 10 ^ 55 +
          2569910790970096047028640045510675214151418268459476340) * 10 ^ 55 +
          5693696987996280242179457915659894124764696972101832700) * 10 ^ 55 +
          160380633378841466898486864570006713402789416613533454) * 10 ^ 55 +
          9967115860590031307110061307301304930993658498442592256)),
    ((((14 * 10 ^ 55 + 1012553335931918676071598865557424036480313255179612876) * 10 ^ 55 +
          6143393116471011872475947890033639900388574655581679591) * 10 ^ 55 +
          5547050217060641929126494289103700257861526594738589118) * 10 ^ 55 +
          1112701614830032581840797939279973795754139895786897408),
    (-(((513458932188 * 10 ^ 55 + 8591749340488036523826150502264716204515234135662379384) * 10
          ^ 55 + 4648636883385299481290859071843994540360845544333411546) * 10 ^ 55 +
          8721605096644315829634838455327276174919982156779356160)),
    (-((188043775857189504519452 * 10 ^ 55 +
          8302791269368677192528516691822811698696416783804292782) * 10 ^ 55 +
          1768379538471837349012800495153885030625793974793666560)),
    49063871621174392225559322379087901901252892447961094186983284320127665063990951212482560,
    625619495255698379211472680176500305505026048,
    1]

/-- The resolvent has no root mod 37 (plain `ℤ` arithmetic, no axioms). -/
lemma noRootR : ∀ y : ℕ, y < 37 → hornerZ Rcs y % 37 ≠ 0 := by
  decide +kernel

lemma R_eval_eq (n : ℤ) : (R : ℤ[X]).eval n = hornerZ Rcs n := by
  simp only [R, Rcs, hornerZ, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

lemma hP : MaedaWeight74.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C (92089333488 : ℚ) * X ^ 4 + C ((-19817164982845968703488) : ℚ) * X ^ 3
      + C ((-1377989142595747748686715833810944) : ℚ) * X ^ 2 + C
          (11802708847432637761332792635527627366465536 : ℚ) * X
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
    exact ne_sq_of_cert (by norm_num) nonsquare n (Dval_eq.symm.trans hn)
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
    exact no_root_of_cert (by norm_num) noRootR n (by rw [← R_eval_eq]; exact h3)

end Weight74

end MaedaGalois

#print axioms MaedaGalois.Weight60.maeda_galois60
#print axioms MaedaGalois.Weight64.maeda_galois64
#print axioms MaedaGalois.Weight66.maeda_galois66
#print axioms MaedaGalois.Weight68.maeda_galois68
#print axioms MaedaGalois.Weight70.maeda_galois70
#print axioms MaedaGalois.Weight74.maeda_galois74
