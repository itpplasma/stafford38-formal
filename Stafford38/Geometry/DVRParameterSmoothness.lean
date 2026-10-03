module
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Stafford38.Geometry.AsymptoticDivisorExistence
public import Stafford38.Geometry.RelativeCoefficientDVRPlace

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.DVRParameterSmoothness

open IsLocalRing
open Polynomial

universe u v

/-- A nonzero algebraic element of a local domain over a field is a unit:
its minimal polynomial has nonzero constant coefficient, which expresses a
unit as a multiple of the element. -/
theorem not_isAlgebraic_of_nonzero_mem_maximalIdeal
    {E : Type u} {S : Type v} [Field E] [CommRing S] [IsDomain S]
    [Algebra E S] [IsLocalRing S] {x : S}
    (hx0 : x ≠ 0) (hxM : x ∈ maximalIdeal S) : ¬ IsAlgebraic E x := by
  intro halg
  have hInt : IsIntegral E x := (isAlgebraic_iff_isIntegral).mp halg
  let f : Polynomial E := minpoly E x
  have hf0 : f.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hInt hx0
  have hroot : Polynomial.aeval x f = 0 := minpoly.aeval E x
  have hprod : x * Polynomial.eval₂ (algebraMap E S) x f.divX =
      - algebraMap E S (f.coeff 0) := by
    have hrootEval : Polynomial.eval₂ (algebraMap E S) x f = 0 := by
      simpa only [Polynomial.aeval_def] using hroot
    have hEq : f = Polynomial.X * f.divX + Polynomial.C (f.coeff 0) :=
      (Polynomial.X_mul_divX_add f).symm
    have hrootExpanded : Polynomial.eval₂ (algebraMap E S) x
        (Polynomial.X * f.divX + Polynomial.C (f.coeff 0)) = 0 := by
      rw [← hEq]
      exact hrootEval
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at hrootExpanded
    exact eq_neg_iff_add_eq_zero.mpr hrootExpanded
  have hcunit : IsUnit (algebraMap E S (f.coeff 0)) :=
    (isUnit_iff_ne_zero.mpr hf0).map (algebraMap E S)
  have hnegunit : IsUnit (-algebraMap E S (f.coeff 0)) := hcunit.neg
  rcases hnegunit with ⟨u, hu⟩
  have hxi : x * (Polynomial.eval₂ (algebraMap E S) x f.divX * ↑u⁻¹) = 1 := by
    rw [← mul_assoc, hprod, ← hu]
    simp
  have hix : (Polynomial.eval₂ (algebraMap E S) x f.divX * ↑u⁻¹) * x = 1 := by
    rw [mul_comm _ x]
    exact hxi
  have hxunit : IsUnit x := ⟨⟨x, Polynomial.eval₂ (algebraMap E S) x f.divX * ↑u⁻¹,
    hxi, hix⟩, rfl⟩
  exact (IsLocalRing.notMem_maximalIdeal).mpr hxunit hxM


/-- At a maximal point of a finite-type algebra over a perfect field, the
residue extension is finite and therefore separable. -/
theorem residueField_isSeparable_of_maximal_finiteType
    {E : Type u} {S : Type v} [Field E] [PerfectField E]
    [CommRing S] [Algebra E S] [Algebra.FiniteType E S]
    (p : Ideal S) [p.IsPrime] [p.IsMaximal] :
    Algebra.IsSeparable E p.ResidueField := by
  letI : Algebra.FiniteType E p.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom E S p.ResidueField)
      (Ideal.algebraMap_residueField_surjective p)
  have hfin : Module.Finite E p.ResidueField :=
    finite_of_finite_type_of_isJacobsonRing E p.ResidueField
  letI : Module.Finite E p.ResidueField := hfin
  letI : Algebra.IsAlgebraic E p.ResidueField :=
    Algebra.isAlgebraic_def.mpr fun x => IsAlgebraic.of_finite E x
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- A finite-type curve is smooth at a DVR point when a nonzero global
parameter cuts out the local maximal ideal and the residue extension is
separable. Injectivity of the polynomial parameter map is proved from the
local parameter: a nonzero element of the local maximal ideal cannot be
algebraic over the coefficient field. -/
theorem isEtaleAt_of_polynomial_uniformizer
    {E : Type u} {S : Type v}
    [Field E] [CommRing S] [IsDomain S]
    [Algebra E S] [Algebra (Polynomial E) S]
    [IsScalarTower E (Polynomial E) S]
    [Algebra.FiniteType E S]
    (p : Ideal S) [p.IsPrime]
    (hX0 : algebraMap (Polynomial E) S Polynomial.X ≠ 0)
    (hparam : (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
        (algebraMap (Polynomial E) (Localization.AtPrime p)) =
          maximalIdeal (Localization.AtPrime p))
    (hsepE : Algebra.IsSeparable E p.ResidueField) :
    Algebra.IsEtaleAt (Polynomial E) p := by
  let A := Polynomial E
  let x : S := algebraMap A S Polynomial.X
  let xloc : Localization.AtPrime p := algebraMap S (Localization.AtPrime p) x
  have hXloc : algebraMap A (Localization.AtPrime p) Polynomial.X ∈
      maximalIdeal (Localization.AtPrime p) := by
    rw [← hparam]
    apply Ideal.mem_map_of_mem
    change Polynomial.X ∈ Ideal.span {Polynomial.X}
    exact Ideal.subset_span (Set.mem_singleton _)
  have hmapX : algebraMap A (Localization.AtPrime p) Polynomial.X = xloc := by
    change algebraMap A (Localization.AtPrime p) Polynomial.X =
      algebraMap S (Localization.AtPrime p) (algebraMap A S Polynomial.X)
    exact (IsScalarTower.algebraMap_apply A S (Localization.AtPrime p) Polynomial.X).symm
  have hXlocMem : xloc ∈ maximalIdeal (Localization.AtPrime p) := by
    rw [← hmapX]
    exact hXloc
  have hlocalizeInjective : Function.Injective (algebraMap S (Localization.AtPrime p)) :=
    IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  have hxloc0 : xloc ≠ 0 := by
    intro h
    apply hX0
    apply hlocalizeInjective
    simpa [xloc, x] using h
  have htrans : Transcendental E xloc := by
    change ¬ IsAlgebraic E xloc
    exact not_isAlgebraic_of_nonzero_mem_maximalIdeal hxloc0 hXlocMem
  have hlocalAeInjective : Function.Injective (Polynomial.aeval xloc :
      Polynomial E →ₐ[E] Localization.AtPrime p) :=
    (transcendental_iff_injective).mp htrans
  have hlocalAlg : IsScalarTower.toAlgHom E A (Localization.AtPrime p) =
      Polynomial.aeval xloc := by
    apply Polynomial.algHom_ext
    rw [IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
    exact hmapX
  have hinj : Function.Injective (algebraMap A S) := by
    intro f g hfg
    have hcomp := congrArg (algebraMap S (Localization.AtPrime p)) hfg
    have hcomp' : algebraMap A (Localization.AtPrime p) f =
        algebraMap A (Localization.AtPrime p) g := by
      simpa only [IsScalarTower.algebraMap_apply A S (Localization.AtPrime p)] using hcomp
    have hEval : (Polynomial.aeval xloc) f = (Polynomial.aeval xloc) g := by
      rw [← hlocalAlg]
      exact hcomp'
    exact hlocalAeInjective hEval
  have hp0max :
      (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).IsMaximal := by
    change (Ideal.span {(Polynomial.X : Polynomial E)}).IsMaximal
    exact PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  have hcontract :
      Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E ≤
        p.comap (algebraMap (Polynomial E) S) := by
    intro r hr
    have hm : algebraMap (Polynomial E) (Localization.AtPrime p) r ∈
        maximalIdeal (Localization.AtPrime p) := by
      rw [← hparam]
      exact Ideal.mem_map_of_mem _ hr
    have htower : algebraMap (Polynomial E) (Localization.AtPrime p) r =
        algebraMap S (Localization.AtPrime p) (algebraMap (Polynomial E) S r) :=
      (IsScalarTower.algebraMap_apply (Polynomial E) S (Localization.AtPrime p) r).symm
    rw [htower] at hm
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime p) p (algebraMap (Polynomial E) S r)).mp hm
  have hcomapPrime :
      (p.comap (algebraMap (Polynomial E) S)).IsPrime := Ideal.comap_isPrime _ p
  have hcomapNe : p.comap (algebraMap (Polynomial E) S) ≠ ⊤ := hcomapPrime.ne_top
  have hcomapEq :
      Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E =
        p.comap (algebraMap (Polynomial E) S) := hp0max.eq_of_le hcomapNe hcontract
  letI : p.LiesOver
      (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E) := ⟨hcomapEq⟩
  have hfiniteA : Algebra.FiniteType A S :=
    Algebra.FiniteType.of_restrictScalars_finiteType E A S
  letI : Algebra.FiniteType A S := hfiniteA
  letI : Algebra.FinitePresentation A S :=
    Algebra.FinitePresentation.of_finiteType.mp hfiniteA
  have htorsion : Module.IsTorsionFree A S := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r x hrx
    rw [Algebra.smul_def] at hrx
    rcases mul_eq_zero.mp hrx with hr | hx
    · exact Or.inl (hinj (by simpa using hr))
    · exact Or.inr hx
  letI : Module.IsTorsionFree A S := htorsion
  have hflat : Module.Flat A S := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp htorsion
  letI : Module.Flat A S := hflat
  letI : Algebra
    (Localization.AtPrime
      (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E))
    (Localization.AtPrime p) :=
      Localization.AtPrime.algebraOfLiesOver
        (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E) p
  letI : Localization.AtPrime.IsLiesOverAlgebra
    (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E) p := inferInstance
  have hsep : Algebra.IsSeparable
      (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).ResidueField
      p.ResidueField := by
    let e := (Stafford38.Geometry.RelativeCoefficientDVR.coordinateResidueEquiv E).symm
    have hcompat :
        RingHom.comp
          (algebraMap
          (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).ResidueField
            p.ResidueField)
          e.toRingHom =
        RingHom.comp (RingEquiv.refl _).toRingHom (algebraMap E p.ResidueField) := by
      ext x
      change algebraMap
          (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).ResidueField
          p.ResidueField (e x) = algebraMap E p.ResidueField x
      have hx : e x = algebraMap E
          (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).ResidueField x := by
        apply (Stafford38.Geometry.RelativeCoefficientDVR.coordinateResidueEquiv E).injective
        simp [e]
      rw [hx]
      exact (IsScalarTower.algebraMap_apply E
        (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).ResidueField
        p.ResidueField x).symm
    exact Algebra.IsSeparable.of_equiv_equiv e
      (RingEquiv.refl _) hcompat
  letI : Algebra.IsSeparable
    (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).ResidueField
    p.ResidueField := hsep
  have hunram : Algebra.IsUnramifiedAt A p := by
    rw [Algebra.isUnramifiedAt_iff_map_eq A
      (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E) p]
    exact ⟨hsep, hparam⟩
  letI : Algebra.IsUnramifiedAt A p := hunram
  have hetale : Algebra.IsEtaleAt A p :=
    Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat p
  exact hetale

/-- Explicit spelling of `IsEtaleAt` as the corresponding local formal-etale
map. It preserves the coefficient variable used by the uniformizer. -/
theorem formallyEtale_localization_of_polynomial_uniformizer
    {E : Type u} {S : Type v}
    [Field E] [CommRing S] [IsDomain S]
    [Algebra E S] [Algebra (Polynomial E) S]
    [IsScalarTower E (Polynomial E) S]
    [Algebra.FiniteType E S]
    (p : Ideal S) [p.IsPrime]
    (hX0 : algebraMap (Polynomial E) S Polynomial.X ≠ 0)
    (hparam : (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
        (algebraMap (Polynomial E) (Localization.AtPrime p)) =
          maximalIdeal (Localization.AtPrime p))
    (hsepE : Algebra.IsSeparable E p.ResidueField) :
    Algebra.FormallyEtale (Polynomial E) (Localization.AtPrime p) :=
  isEtaleAt_of_polynomial_uniformizer p hX0 hparam hsepE

/-- Smoothness follows by composing the polynomial algebra's formal smoothness
with the local formal-etale map. -/
theorem isSmoothAt_of_polynomial_uniformizer
    {E : Type u} {S : Type v}
    [Field E] [CommRing S] [IsDomain S]
    [Algebra E S] [Algebra (Polynomial E) S]
    [IsScalarTower E (Polynomial E) S]
    [Algebra.FiniteType E S]
    (p : Ideal S) [p.IsPrime]
    (hX0 : algebraMap (Polynomial E) S Polynomial.X ≠ 0)
    (hparam : (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
        (algebraMap (Polynomial E) (Localization.AtPrime p)) =
          maximalIdeal (Localization.AtPrime p))
    (hsepE : Algebra.IsSeparable E p.ResidueField) :
    Algebra.IsSmoothAt E p := by
  letI : Algebra.FormallyEtale (Polynomial E) (Localization.AtPrime p) :=
    formallyEtale_localization_of_polynomial_uniformizer p hX0 hparam hsepE
  have hpoly : Algebra.FormallySmooth E (Polynomial E) := inferInstance
  exact Algebra.FormallySmooth.comp E (Polynomial E) (Localization.AtPrime p)

/-- Version requiring only that the divisor point be maximal over a perfect
coefficient field; residue separability is then supplied by Zariski's lemma. -/
theorem isEtaleAt_of_polynomial_uniformizer_of_maximal
    {E : Type u} {S : Type v}
    [Field E] [PerfectField E] [CommRing S] [IsDomain S]
    [Algebra E S] [Algebra (Polynomial E) S]
    [IsScalarTower E (Polynomial E) S]
    [Algebra.FiniteType E S]
    (p : Ideal S) [p.IsPrime] [p.IsMaximal]
    (hX0 : algebraMap (Polynomial E) S Polynomial.X ≠ 0)
    (hparam : (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
        (algebraMap (Polynomial E) (Localization.AtPrime p)) =
          maximalIdeal (Localization.AtPrime p)) :
    Algebra.IsEtaleAt (Polynomial E) p :=
  isEtaleAt_of_polynomial_uniformizer p hX0 hparam
    (residueField_isSeparable_of_maximal_finiteType p)

/-- Smoothness follows for maximal points over a perfect coefficient field. -/
theorem isSmoothAt_of_polynomial_uniformizer_of_maximal
    {E : Type u} {S : Type v}
    [Field E] [PerfectField E] [CommRing S] [IsDomain S]
    [Algebra E S] [Algebra (Polynomial E) S]
    [IsScalarTower E (Polynomial E) S]
    [Algebra.FiniteType E S]
    (p : Ideal S) [p.IsPrime] [p.IsMaximal]
    (hX0 : algebraMap (Polynomial E) S Polynomial.X ≠ 0)
    (hparam : (Stafford38.Geometry.AsymptoticDivisorExistence.coordinateZeroPrime E).map
        (algebraMap (Polynomial E) (Localization.AtPrime p)) =
          maximalIdeal (Localization.AtPrime p)) :
    Algebra.IsSmoothAt E p :=
  isSmoothAt_of_polynomial_uniformizer p hX0 hparam
    (residueField_isSeparable_of_maximal_finiteType p)


end Stafford38.Geometry.DVRParameterSmoothness
