module
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u v w

noncomputable section

namespace Stafford38.Geometry.FiniteTypeCurveNormalization

theorem exists_injective_integral_polynomial_of_ring_trdeg_one
    {E : Type u} {A : Type v} [Field E] [CommRing A] [IsDomain A] [Algebra E A]
    [Algebra.FiniteType E A]
    (htrdeg : Algebra.trdeg E A = 1) :
    ∃ f : Polynomial E →ₐ[E] A, Function.Injective f ∧ f.IsIntegral := by
  obtain ⟨s, g, hg, hgi⟩ := exists_integral_inj_algHom_of_fg E A
  let P := MvPolynomial (Fin s) E
  letI : Algebra P A := g.toRingHom.toAlgebra
  letI : IsScalarTower E P A := IsScalarTower.of_algHom g
  letI : FaithfulSMul E P :=
    (faithfulSMul_iff_algebraMap_injective E P).mpr <| by
      change Function.Injective (MvPolynomial.C : E → P)
      exact MvPolynomial.C_injective _ _
  letI : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective P A).mpr <| by
      change Function.Injective (g : P →+* A)
      exact hg
  have hInt : Algebra.IsIntegral P A := by
    refine ⟨fun x => ?_⟩
    exact hgi x
  letI : Algebra.IsIntegral P A := hInt
  letI : Algebra.IsAlgebraic P A := Algebra.IsIntegral.isAlgebraic
  have hPA : Algebra.trdeg P A = 0 := trdeg_eq_zero
  have hEq : Cardinal.lift.{v} (Algebra.trdeg E P) =
      Cardinal.lift.{u} (Algebra.trdeg E A) := by
    have h : Cardinal.lift.{v} (Algebra.trdeg E P) +
        Cardinal.lift.{u} (Algebra.trdeg P A) =
        Cardinal.lift.{u} (Algebra.trdeg E A) := lift_trdeg_add_eq E P A
    simpa [hPA] using h
  have hsCard : Cardinal.lift.{v} (Algebra.trdeg E P) = 1 := by
    calc
      _ = Cardinal.lift.{u} (Algebra.trdeg E A) := hEq
      _ = 1 := by rw [htrdeg]; simp
  have hs : s = 1 := by
    simpa [P, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_mk_fin] using hsCard
  subst s
  let e : MvPolynomial (Fin 1) E ≃ₐ[E] Polynomial E :=
    MvPolynomial.uniqueAlgEquiv E (Fin 1)
  let f : Polynomial E →ₐ[E] A := g.comp e.symm.toAlgHom
  refine ⟨f, ?_, ?_⟩
  · exact hg.comp e.symm.injective
  · have he : (e.symm : Polynomial E →+* MvPolynomial (Fin 1) E).IsIntegral :=
      RingHom.isIntegral_of_surjective _ e.symm.surjective
    change (f : Polynomial E →+* A).IsIntegral
    exact RingHom.IsIntegral.trans _ _ he hgi

/-- A domain and its fraction field have the same transcendence degree over the base field. -/
theorem trdeg_fractionRing_eq_trdeg
    {E : Type u} {A : Type v} [Field E] [CommRing A] [IsDomain A] [Algebra E A] :
    Algebra.trdeg E (FractionRing A) = Algebra.trdeg E A := by
  letI : Algebra.IsAlgebraic A (FractionRing A) :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := A) (K := FractionRing A) (C := FractionRing A)).2 inferInstance
  have hzero : Algebra.trdeg A (FractionRing A) = 0 := trdeg_eq_zero
  have h : Algebra.trdeg E A + Algebra.trdeg A (FractionRing A) =
      Algebra.trdeg E (FractionRing A) := trdeg_add_eq E A
  rw [hzero, add_zero] at h
  exact h.symm

/-- The same equality for any chosen realization of the fraction field. -/
theorem lift_trdeg_isFractionRing_eq
    {E : Type u} {A : Type v} {L : Type w} [Field E] [CommRing A] [IsDomain A]
    [Algebra E A] [Field L] [Algebra A L] [IsFractionRing A L]
    [Algebra E L] [IsScalarTower E A L] :
    Cardinal.lift.{w} (Algebra.trdeg E A) =
      Cardinal.lift.{v} (Algebra.trdeg E L) := by
  letI : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := L) (C := L)).2 inferInstance
  have hzero : Algebra.trdeg A L = 0 := trdeg_eq_zero
  have h : Cardinal.lift.{w} (Algebra.trdeg E A) +
      Cardinal.lift.{v} (Algebra.trdeg A L) =
      Cardinal.lift.{v} (Algebra.trdeg E L) := lift_trdeg_add_eq E A L
  simpa [hzero] using h

/-- Noether normalization for an affine domain whose fraction field has transcendence degree one. -/
theorem exists_injective_integral_polynomial_of_fractionRing_trdeg_one
    {E : Type u} {A : Type v} [Field E] [CommRing A] [IsDomain A] [Algebra E A]
    [Algebra.FiniteType E A]
    (htrdeg : Algebra.trdeg E (FractionRing A) = 1) :
    ∃ f : Polynomial E →ₐ[E] A, Function.Injective f ∧ f.IsIntegral := by
  have hA : Algebra.trdeg E A = 1 :=
    (trdeg_fractionRing_eq_trdeg (E := E) (A := A)).symm.trans htrdeg
  exact exists_injective_integral_polynomial_of_ring_trdeg_one hA

/-- Noether normalization when the fraction field is given by an arbitrary fraction-ring model. -/
theorem exists_injective_integral_polynomial_of_isFractionRing_trdeg_one
    {E : Type u} {A : Type v} {L : Type w} [Field E] [CommRing A] [IsDomain A]
    [Algebra E A] [Algebra.FiniteType E A] [Field L] [Algebra A L]
    [IsFractionRing A L] [Algebra E L] [IsScalarTower E A L]
    (htrdeg : Algebra.trdeg E L = 1) :
    ∃ f : Polynomial E →ₐ[E] A, Function.Injective f ∧ f.IsIntegral := by
  have hLift : Cardinal.lift.{w} (Algebra.trdeg E A) = 1 := by
    calc
      _ = Cardinal.lift.{v} (Algebra.trdeg E L) :=
        lift_trdeg_isFractionRing_eq (E := E) (A := A) (L := L)
      _ = 1 := by rw [htrdeg]; simp
  have hA : Algebra.trdeg E A = 1 := Cardinal.lift_eq_one.mp hLift
  exact exists_injective_integral_polynomial_of_ring_trdeg_one hA

end Stafford38.Geometry.FiniteTypeCurveNormalization
