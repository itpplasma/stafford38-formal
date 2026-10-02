import Stafford38.Geometry.ActualOptionCoordinateEtale
import Stafford38.Geometry.DVRUniformizerNumerator
import Stafford38.Geometry.LocalizationStageFractionCoefficients
import Stafford38.Geometry.NormalizationHeightOne

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 5000000

noncomputable section

namespace Stafford38.Geometry.ActualNormalizationDivisorEtale

open IsLocalRing Polynomial

universe u v w x

/-- The actual option-coordinate map at a height-one center of a normal model
is formally etale when the selected coefficient fraction field is realized
inside the coefficient localization and the divisor numerator generates the
center's local maximal ideal.  The local equivalence and the coefficient map
are constructed from the same localization-stage data. -/
theorem formallyEtale_at_actual_normalization_center_of_specified_parameter
    {k : Type u} [Field k] [CharZero k] {σ : Type v} [Fintype σ]
    {B : Type w} [CommRing B] [IsDomain B] [Algebra k B]
    [IsNoetherianRing B] [IsIntegrallyClosed B]
    {M : Submonoid B}
    [Algebra k (Localization M)] [IsScalarTower k B (Localization M)]
    [IsDomain (Localization M)]
    [Algebra (FractionRing (MvPolynomial σ k)) (Localization M)]
    [IsScalarTower k (FractionRing (MvPolynomial σ k)) (Localization M)]
    (p : Ideal (Localization M)) [hpPrime : p.IsPrime] [hpMax : p.IsMaximal]
    {κ : Type u} [Field κ]
    (rhoL : Localization M →+* κ) (rhoB : B →+* κ)
    (hp : p = RingHom.ker rhoL)
    (hLoc : rhoL.comp (algebraMap B (Localization M)) = rhoB)
    (f : MvPolynomial σ k →ₐ[k] B)
    (hinj : Function.Injective (rhoB.comp f.toRingHom))
    (hcoeffL : (algebraMap (FractionRing (MvPolynomial σ k)) (Localization M)).comp
        (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))) =
      (algebraMap B (Localization M)).comp f.toRingHom)
    (hfinite : Algebra.FiniteType (FractionRing (MvPolynomial σ k)) (Localization M))
    (hheight : (p.comap (algebraMap B (Localization M))).height = 1)
    (a : B) (ha0 : a ≠ 0) (_haP : a ∈ p.comap (algebraMap B (Localization M)))
    (hspan : Ideal.span {algebraMap B
      (Localization.AtPrime (p.comap (algebraMap B (Localization M)))) a} =
        maximalIdeal (Localization.AtPrime (p.comap (algebraMap B (Localization M)))))
    (fOption : MvPolynomial (Option σ) k →ₐ[k] B)
    (hnoneB : fOption (MvPolynomial.X none) = a)
    (hsomeB : ∀ i : σ,
      fOption (MvPolynomial.X (some i)) = f (MvPolynomial.X i)) :
    let P := p.comap (algebraMap B (Localization M))
    let actualMap : MvPolynomial (Option σ) k →ₐ[k]
        Localization.AtPrime P :=
      (IsScalarTower.toAlgHom k B (Localization.AtPrime P)).comp fOption
    letI : Algebra (MvPolynomial (Option σ) k) (Localization.AtPrime P) :=
      actualMap.toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial (Option σ) k) (Localization.AtPrime P) := by
  classical
  let L := Localization M
  let E := FractionRing (MvPolynomial σ k)
  let P : Ideal B := p.comap (algebraMap B L)
  letI : P.IsPrime := Ideal.comap_isPrime (algebraMap B L) p
  have hPker : P = RingHom.ker rhoB := by
    have hcenter :
        p.comap (algebraMap B L) = RingHom.ker rhoB := by
      ext b
      rw [Ideal.mem_comap, hp, RingHom.mem_ker]
      change rhoL (algebraMap B L b) = 0 ↔ rhoB b = 0
      have heq : rhoL (algebraMap B L b) = rhoB b := by
        simpa only [RingHom.comp_apply] using
        congrArg (fun g : B →+* κ => g b) hLoc
      rw [heq]
    exact hcenter
  let fRing : MvPolynomial σ k →+* B := f.toRingHom
  let coeffRing : E →+* L := algebraMap E L
  obtain ⟨e, hcenter, hcoeff⟩ :=
    LocalizationStageFractionCoefficients.stageFractionCoefficientMap_commutes
      M p rhoL rhoB hp hLoc fRing hinj coeffRing hcoeffL
  have hcenterP : P = RingHom.ker rhoB := by
    exact hPker
  have hDVR : IsDiscreteValuationRing (Localization.AtPrime P) :=
    NormalizationHeightOne.isDiscreteValuationRing_localization_of_height_eq_one P hheight
  letI : IsDiscreteValuationRing (Localization.AtPrime P) := hDVR
  letI : Algebra.FiniteType E L := hfinite
  letI : PerfectField E := inferInstance
  let hsep : Algebra.IsSeparable E p.ResidueField :=
    DVRParameterSmoothness.residueField_isSeparable_of_maximal_finiteType p

  let Lp := Localization.AtPrime p
  let Bp := Localization.AtPrime P
  let aL : L := algebraMap B L a
  let aLp : Lp := algebraMap L Lp aL
  let aBp : Bp := algebraMap B Bp a
  let evalL : Polynomial E →ₐ[E] L := Polynomial.aeval aL
  letI : Algebra (Polynomial E) L := evalL.toRingHom.toAlgebra
  have hscalarEL : algebraMap E L =
      (algebraMap (Polynomial E) L).comp (algebraMap E (Polynomial E)) := by
    ext c
    change algebraMap E L c = evalL (algebraMap E (Polynomial E) c)
    calc
      algebraMap E L c = evalL (Polynomial.C c) := (Polynomial.aeval_C aL c).symm
      _ = evalL (algebraMap E (Polynomial E) c) := rfl
  letI : IsScalarTower E (Polynomial E) L :=
    IsScalarTower.of_algebraMap_eq' hscalarEL
  have hmapa : e aLp = aBp := by
    change e (algebraMap B Lp a) = algebraMap B Bp a
    exact e.commutes a

  let coeffLpRing : E →+* Lp := algebraMap E Lp
  have hcoeffScalar (c : k) : coeffLpRing (algebraMap k E c) =
      algebraMap B Lp (algebraMap k B c) := by
    change algebraMap L Lp (algebraMap E L (algebraMap k E c)) = _
    have hcoeffBase : algebraMap E L (algebraMap k E c) =
        algebraMap B L (algebraMap k B c) := by
      have hconst := congrArg (fun g : MvPolynomial σ k →+* L =>
        g (MvPolynomial.C c)) hcoeffL
      have hC : algebraMap (MvPolynomial σ k) E (MvPolynomial.C c) =
          algebraMap k E c := by
        calc
          _ = algebraMap (MvPolynomial σ k) E
              (algebraMap k (MvPolynomial σ k) c) := rfl
          _ = _ := IsScalarTower.algebraMap_apply k (MvPolynomial σ k) E c
      have hfC : f (MvPolynomial.C c) = algebraMap k B c := f.commutes c
      change algebraMap E L (algebraMap (MvPolynomial σ k) E (MvPolynomial.C c)) =
        algebraMap B L (f (MvPolynomial.C c)) at hconst
      calc
        algebraMap E L (algebraMap k E c) =
            algebraMap E L (algebraMap (MvPolynomial σ k) E (MvPolynomial.C c)) := by rw [hC]
        _ = algebraMap B L (f (MvPolynomial.C c)) := hconst
        _ = algebraMap B L (algebraMap k B c) := by rw [hfC]
    calc
      algebraMap L Lp (algebraMap E L (algebraMap k E c)) =
          algebraMap L Lp (algebraMap B L (algebraMap k B c)) :=
            congrArg (algebraMap L Lp) hcoeffBase
      _ = algebraMap B Lp (algebraMap k B c) :=
        (IsScalarTower.algebraMap_apply B L Lp _).symm
  letI : Algebra k Lp := Algebra.compHom Lp (algebraMap k E)
  letI : SMul k Lp := Algebra.toSMul
  letI : IsScalarTower k E Lp := IsScalarTower.of_algebraMap_eq' rfl
  let cLp : E →ₐ[k] Lp := {
    toRingHom := coeffLpRing
    commutes' := by intro c; rfl
  }
  let evalLp : Polynomial E →ₐ[E] Lp := Polynomial.aeval aLp
  letI : IsScalarTower E (Polynomial E) Lp := inferInstance
  letI : IsScalarTower (Polynomial E) L Lp := inferInstance
  have hEvalLp (z : Polynomial E) :
      algebraMap (Polynomial E) Lp z = Polynomial.aeval aLp z := by
    have hXlp : algebraMap (Polynomial E) Lp Polynomial.X = aLp := by
      rw [IsScalarTower.algebraMap_apply (Polynomial E) L Lp Polynomial.X]
      change algebraMap L Lp (evalL Polynomial.X) = aLp
      simp only [evalL, Polynomial.aeval_X]
      rfl
    have hAlg : IsScalarTower.toAlgHom E (Polynomial E) Lp = evalLp := by
      apply Polynomial.algHom_ext
      rw [IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
      exact hXlp
    have hz := congrArg (fun g : Polynomial E →ₐ[E] Lp => g z) hAlg
    simpa only [IsScalarTower.toAlgHom_apply, evalLp] using hz

  let cBpRing : E →+* Bp := e.toRingEquiv.toRingHom.comp cLp.toRingHom
  letI : Algebra E Bp := cBpRing.toAlgebra
  letI : SMul E Bp := Algebra.toSMul
  have hscalar_kE : algebraMap k Bp =
      cBpRing.comp (algebraMap k E) := by
    ext c
    calc
      algebraMap k Bp c = algebraMap B Bp (algebraMap k B c) :=
        (IsScalarTower.algebraMap_apply k B Bp c).symm
      _ = e (algebraMap B Lp (algebraMap k B c)) := by rw [e.commutes]
      _ = e (coeffLpRing (algebraMap k E c)) := congrArg e (hcoeffScalar c).symm
      _ = cBpRing (algebraMap k E c) := rfl
  letI : IsScalarTower k E Bp := IsScalarTower.of_algebraMap_eq' hscalar_kE
  let evalBp : Polynomial E →ₐ[E] Bp := Polynomial.aeval aBp
  letI : Algebra (Polynomial E) Bp := evalBp.toRingHom.toAlgebra
  letI : SMul (Polynomial E) Bp := Algebra.toSMul
  have hscalarEBp : algebraMap E Bp =
      (algebraMap (Polynomial E) Bp).comp (algebraMap E (Polynomial E)) := by
    ext c
    change cBpRing c = evalBp (algebraMap E (Polynomial E) c)
    rw [evalBp.commutes]
    rfl
  letI : IsScalarTower E (Polynomial E) Bp := IsScalarTower.of_algebraMap_eq' hscalarEBp
  have hscalar_kPolyBp : algebraMap k Bp =
      (algebraMap (Polynomial E) Bp).comp (algebraMap k (Polynomial E)) := by
    ext c
    change algebraMap k Bp c =
      algebraMap (Polynomial E) Bp (algebraMap k (Polynomial E) c)
    rw [IsScalarTower.algebraMap_apply k E (Polynomial E) c]
    change algebraMap k Bp c = evalBp
      (algebraMap E (Polynomial E) (algebraMap k E c))
    rw [evalBp.commutes]
    exact congrArg (fun h : k →+* Bp => h c) hscalar_kE
  letI : IsScalarTower k (Polynomial E) Bp :=
    IsScalarTower.of_algebraMap_eq' hscalar_kPolyBp
  let ePoly : Lp ≃ₐ[Polynomial E] Bp :=
    LocalizationStageFractionCoefficients.polynomialAlgEquivOfCompatibleEvaluation
      e.toRingEquiv
      (fun c => rfl)
      aLp aBp hmapa
      hEvalLp
      (fun z => by
        rfl)

  have haLp0 : aLp ≠ 0 := by
    intro hz
    have hloc : Function.Injective (algebraMap B Bp) :=
      IsLocalization.injective Bp P.primeCompl_le_nonZeroDivisors
    have hz' : e aLp = 0 := by rw [hz]; simp
    have hzero : algebraMap B Bp a = algebraMap B Bp 0 := by
      calc
        algebraMap B Bp a = e aLp := hmapa.symm
        _ = 0 := hz'
        _ = algebraMap B Bp 0 := by simp
    exact ha0 (hloc hzero)
  have hparam :
      (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
        (algebraMap (Polynomial E) Lp) = maximalIdeal Lp := by
    have hmapSpan :
        Ideal.map (e : Lp →+* Bp)
          ((Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
            (algebraMap (Polynomial E) Lp)) = maximalIdeal Bp := by
      rw [Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime,
        Ideal.map_span, Ideal.map_span]
      simp only [Set.image_singleton]
      rw [hEvalLp, Polynomial.aeval_X]
      change Ideal.span {e aLp} = maximalIdeal Bp
      rw [hmapa]
      change Ideal.span {algebraMap B Bp a} = maximalIdeal Bp
      exact hspan
    have hmaxMap : (maximalIdeal Lp).map (e : Lp →+* Bp) = maximalIdeal Bp :=
      IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
    have hmapEq :
        ((Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
          (algebraMap (Polynomial E) Lp)).map (e : Lp →+* Bp) =
        (maximalIdeal Lp).map (e : Lp →+* Bp) := by
      rw [hmapSpan, hmaxMap]
    have hsups := (Ideal.map_eq_iff_sup_ker_eq_of_surjective
      (e : Lp →+* Bp) e.surjective).mp hmapEq
    have hker : RingHom.ker (e : Lp →+* Bp) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp e.injective
    simpa [hker] using hsups

  let q : Option σ → B := fun i => match i with
    | none => a
    | some j => f (MvPolynomial.X j)
  let ρ : B →ₐ[k] Bp := IsScalarTower.toAlgHom k B Bp
  have hnone : ePoly (algebraMap (Polynomial E) Lp (Polynomial.X : Polynomial E)) =
      ρ a := by
    have hX : algebraMap (Polynomial E) Lp Polynomial.X = aLp := by
      simpa [Polynomial.aeval_X] using hEvalLp Polynomial.X
    rw [hX]
    change ePoly aLp = algebraMap B Bp a
    have hePoly : ∀ x : Lp, ePoly x = e x := fun _ => rfl
    rw [hePoly]
    rw [hmapa]
  have hsome : ∀ i : σ,
      ePoly (algebraMap (Polynomial E) Lp
        (Polynomial.C (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)))) =
          ρ (f (MvPolynomial.X i)) := by
    intro i
    rw [ePoly.commutes]
    change evalBp (Polynomial.C (algebraMap (MvPolynomial σ k) E
        (MvPolynomial.X i))) =
      algebraMap B Bp (f (MvPolynomial.X i))
    have hval := congrArg (fun g : E →+* Bp =>
      g (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i))) hcoeff
    have hval' : cBpRing (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)) =
        LocalizationStageFractionCoefficients.fractionRingToAtPrime fRing rhoB P
          hcenter hinj (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)) := by
      change (e.toRingEquiv.toRingHom.comp
        ((algebraMap L Lp).comp coeffRing))
        (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)) = _ at hval
      exact hval
    have hcoeffImage : cBpRing (algebraMap (MvPolynomial σ k) E
        (MvPolynomial.X i)) = algebraMap B Bp (f (MvPolynomial.X i)) := by
      calc
        cBpRing (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)) =
            LocalizationStageFractionCoefficients.fractionRingToAtPrime fRing rhoB P
              hcenter hinj (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)) := hval'
        _ = algebraMap B Bp (f (MvPolynomial.X i)) :=
          LocalizationStageFractionCoefficients.fractionRingToAtPrime_algebraMap
            fRing rhoB P hcenter hinj (MvPolynomial.X i)
    change Polynomial.aeval aBp (Polynomial.C
      (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i))) = _
    rw [Polynomial.aeval_C]
    change cBpRing (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)) = _
    exact hcoeffImage

  let fActual : MvPolynomial (Option σ) k →ₐ[k] Bp := ρ.comp fOption
  letI : Algebra (MvPolynomial (Option σ) k) Bp := fActual.toRingHom.toAlgebra
  have hX0 : algebraMap (Polynomial E) L Polynomial.X ≠ 0 := by
    have hX : algebraMap (Polynomial E) L Polynomial.X = aL := by
      change Polynomial.aeval aL Polynomial.X = aL
      simp
    intro h
    have hmap : algebraMap L Lp (algebraMap (Polynomial E) L Polynomial.X) = aLp := by
      rw [hX]
    apply haLp0
    have := congrArg (algebraMap L Lp) h
    simpa [hmap] using this
  have hmodel : Algebra.FormallyEtale (Polynomial E) Lp :=
    DVRParameterSmoothness.formallyEtale_localization_of_polynomial_uniformizer
      (S := L) p hX0 hparam hsep
  letI : Algebra.FormallyEtale (Polynomial E) Lp := hmodel
  have htarget : Algebra.FormallyEtale (Polynomial E) Bp :=
    Algebra.FormallyEtale.of_equiv ePoly
  have hnone' : fActual (MvPolynomial.X none) =
      algebraMap (Polynomial E) Bp (Polynomial.X : Polynomial E) := by
    have hf : fActual (MvPolynomial.X none) = ρ a := by
      change ρ (fOption (MvPolynomial.X none)) = ρ a
      rw [hnoneB]
    calc
      fActual (MvPolynomial.X none) = ρ (q none) := hf
      _ = ePoly (algebraMap (Polynomial E) Lp Polynomial.X) := hnone.symm
      _ = _ := ePoly.commutes Polynomial.X
  have hsome' : ∀ i : σ,
      fActual (MvPolynomial.X (some i)) =
        algebraMap (Polynomial E) Bp
          (Polynomial.C (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i))) := by
    intro i
    have hf : fActual (MvPolynomial.X (some i)) = ρ (f (MvPolynomial.X i)) := by
      change ρ (fOption (MvPolynomial.X (some i))) = ρ (f (MvPolynomial.X i))
      rw [hsomeB i]
    calc
      fActual (MvPolynomial.X (some i)) = ρ (q (some i)) := hf
      _ = ePoly (algebraMap (Polynomial E) Lp
          (Polynomial.C (algebraMap (MvPolynomial σ k) E (MvPolynomial.X i)))) :=
            (hsome i).symm
      _ = _ := ePoly.commutes _
  have hformal :=
    OptionCoordinateEtaleComposition.formallyEtale_of_optionCoordinate_generator_images
      fActual hnone' hsome' htarget
  exact hformal

/-- The existential convenience wrapper chooses a local numerator once and
then delegates to the specified-parameter theorem. The actual chart producer
uses the stronger theorem directly to preserve its chosen divisor parameter. -/
theorem formallyEtale_at_actual_normalization_center
    {k : Type u} [Field k] [CharZero k] {σ : Type v} [Fintype σ]
    {B : Type w} [CommRing B] [IsDomain B] [Algebra k B]
    [IsNoetherianRing B] [IsIntegrallyClosed B]
    {M : Submonoid B}
    [Algebra k (Localization M)] [IsScalarTower k B (Localization M)]
    [IsDomain (Localization M)]
    [Algebra (FractionRing (MvPolynomial σ k)) (Localization M)]
    [IsScalarTower k (FractionRing (MvPolynomial σ k)) (Localization M)]
    (p : Ideal (Localization M)) [hpPrime : p.IsPrime] [hpMax : p.IsMaximal]
    {κ : Type u} [Field κ]
    (rhoL : Localization M →+* κ) (rhoB : B →+* κ)
    (hp : p = RingHom.ker rhoL)
    (hLoc : rhoL.comp (algebraMap B (Localization M)) = rhoB)
    (f : MvPolynomial σ k →ₐ[k] B)
    (hinj : Function.Injective (rhoB.comp f.toRingHom))
    (hcoeffL : (algebraMap (FractionRing (MvPolynomial σ k)) (Localization M)).comp
        (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))) =
      (algebraMap B (Localization M)).comp f.toRingHom)
    (hfinite : Algebra.FiniteType (FractionRing (MvPolynomial σ k)) (Localization M))
    (hheight : (p.comap (algebraMap B (Localization M))).height = 1) :
    let P := p.comap (algebraMap B (Localization M))
    ∃ a : B, a ≠ 0 ∧ a ∈ P ∧
      Ideal.span {algebraMap B (Localization.AtPrime P) a} =
        maximalIdeal (Localization.AtPrime P) ∧
      let q : Option σ → B := fun i => match i with
        | none => a
        | some j => f (MvPolynomial.X j)
      let fOption : MvPolynomial (Option σ) k →ₐ[k] B :=
        MvPolynomial.aeval q
      let actualMap : MvPolynomial (Option σ) k →ₐ[k]
          Localization.AtPrime P :=
        (IsScalarTower.toAlgHom k B (Localization.AtPrime P)).comp fOption
      letI : Algebra (MvPolynomial (Option σ) k) (Localization.AtPrime P) :=
        actualMap.toRingHom.toAlgebra
      Algebra.FormallyEtale (MvPolynomial (Option σ) k) (Localization.AtPrime P) := by
  classical
  let L := Localization M
  let P : Ideal B := p.comap (algebraMap B L)
  letI : P.IsPrime := Ideal.comap_isPrime (algebraMap B L) p
  have hDVR : IsDiscreteValuationRing (Localization.AtPrime P) :=
    NormalizationHeightOne.isDiscreteValuationRing_localization_of_height_eq_one P hheight
  letI : IsDiscreteValuationRing (Localization.AtPrime P) := hDVR
  obtain ⟨_π, _hπ, a, _b, ha0, haP, _hrep, hspan⟩ :=
    DVRUniformizerNumerator.exists_numerator_of_dvr_localization P
  refine ⟨a, ha0, haP, hspan, ?_⟩
  let q : Option σ → B := fun i => match i with
    | none => a
    | some j => f (MvPolynomial.X j)
  let fOption : MvPolynomial (Option σ) k →ₐ[k] B := MvPolynomial.aeval q
  have hnoneB : fOption (MvPolynomial.X none) = a := by
    simp [fOption, q]
  have hsomeB : ∀ i : σ,
      fOption (MvPolynomial.X (some i)) = f (MvPolynomial.X i) := by
    intro i
    simp [fOption, q]
  have hcore :=
    formallyEtale_at_actual_normalization_center_of_specified_parameter
      p rhoL rhoB hp hLoc f hinj hcoeffL hfinite hheight a ha0 haP hspan
      fOption hnoneB hsomeB
  simpa [q, fOption] using hcore

end Stafford38.Geometry.ActualNormalizationDivisorEtale
