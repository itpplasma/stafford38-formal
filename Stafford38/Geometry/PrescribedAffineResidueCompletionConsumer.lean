module
public import Stafford38.Geometry.PrescribedAffineResidueCompletion
public import Stafford38.Geometry.SmoothLocalParameterCompletion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.PrescribedAffineResidueCompletionConsumer

open Stafford38.Geometry.PrescribedAffineResidueCompletion

/-- Independent coordinate check: the quotient equivalence built from the actual
residue map sends each polynomial generator to the value of that same generator
at the selected ground point. -/
theorem residueQuotient_generator_value
    {k σ B : Type*} [Field k] [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B]
    [IsScalarTower k (MvPolynomial σ k) B]
    (M : Ideal B) (eM : (B ⧸ M) ≃ₐ[k] k) [Fintype σ] (i : σ) :
    residuePointQuotientEquiv (σ := σ) M eM
      (Ideal.Quotient.mk
        (Stafford38.Geometry.AffinePointCompletion.pointIdeal
          (residueCoordinates (σ := σ) M eM))
        (MvPolynomial.X i)) = residueCoordinates (σ := σ) M eM i := by
  rw [residuePointQuotientEquiv_apply]
  simp [residueEvaluation, residueCoordinates]

/-- The completed map sends the formal variable to the centered original
polynomial coordinate in the completion at the actual local point. This checks
that the selected residue point and the original coordinate map share one chart. -/
theorem prescribedCompletion_centeredGenerator
    {k σ B : Type*} [Field k] [Fintype σ] [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B]
    [IsScalarTower k (MvPolynomial σ k) B]
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.EssFiniteType (MvPolynomial σ k) B]
    [Algebra.FormallyEtale (MvPolynomial σ k) (Localization.AtPrime M)] (i : σ) :
    Stafford38.Geometry.PrescribedAffineResidueCompletion.powerSeriesCompletionAtGroundPoint
      M eM (MvPowerSeries.X i) =
    AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime M))
      (Localization.AtPrime M)
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime M)
        (MvPolynomial.X i - MvPolynomial.C
          (residueCoordinates (σ := σ) M eM i))) := by
  let x := residueCoordinates (σ := σ) M eM
  let q := Stafford38.Geometry.AffinePointCompletion.pointIdeal x
  letI : q.IsMaximal :=
    Stafford38.Geometry.PrescribedAffineResidueCompletion.residuePoint_isMaximal
      (σ := σ) M eM
  letI : q.IsPrime := inferInstance
  let ρ := residueEvaluation (σ := σ) M eM
  letI : Algebra (MvPolynomial σ k) k := ρ.toRingHom.toAlgebra
  letI : IsScalarTower (MvPolynomial σ k) k k :=
    IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  let eQ := residuePointQuotientEquiv (σ := σ) M eM
  letI : IsScalarTower (MvPolynomial σ k) k (B ⧸ M) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      apply eM.injective
      rw [← Ideal.Quotient.mk_algebraMap (MvPolynomial σ k) M a, eM.commutes]
      change eM (Ideal.Quotient.mk M (algebraMap (MvPolynomial σ k) B a)) = ρ a
      rfl)
  letI : IsScalarTower (MvPolynomial σ k) k
      (MvPolynomial σ k ⧸ q) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      apply eQ.injective
      calc
        eQ (algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ q) a) = ρ a := by
          change eQ (Ideal.Quotient.mk q a) = ρ a
          simpa [ρ] using
            Stafford38.Geometry.PrescribedAffineResidueCompletion.residuePointQuotientEquiv_apply
              (σ := σ) M eM a
        _ = eQ (algebraMap k (MvPolynomial σ k ⧸ q) (ρ a)) := by
          rw [eQ.commutes]
          rfl)
  have hq : Ideal.under (MvPolynomial σ k) M = q := by
    simpa [x, q] using
      Stafford38.Geometry.PrescribedAffineResidueCompletion.residuePoint_under_eq
        (σ := σ) M eM
  let e :=
    Stafford38.Geometry.PrescribedAffineResidueCompletion.residueEquivOverCoordinates
      (σ := σ) M eM
  have hAffine :
      Stafford38.Geometry.AffinePointCompletion.powerSeriesCompletionAtPoint x
          (MvPowerSeries.X i) =
        AdicCompletion.of q (MvPolynomial σ k)
          (MvPolynomial.X i - MvPolynomial.C (x i)) := by
    simpa [Stafford38.Geometry.AffinePointCompletion.powerSeriesCompletionAtPoint] using
      Stafford38.Geometry.SmoothLocalParameterCompletion.affinePointCompletion_variable_explicit
        x i
  change (Stafford38.Geometry.EtalePointCompletion.completionEquivOfEtaleResidue
    q M hq e)
      (Stafford38.Geometry.AffinePointCompletion.powerSeriesCompletionAtPoint x
        (MvPowerSeries.X i)) = _
  rw [hAffine]
  exact Stafford38.Geometry.PrescribedAffineResidueCompletion.etaleCompletion_apply_of
    q M hq e (MvPolynomial.X i - MvPolynomial.C (x i))

#print axioms residueQuotient_generator_value
#print axioms prescribedCompletion_centeredGenerator
#print axioms Stafford38.Geometry.PrescribedAffineResidueCompletion.powerSeriesCompletionAtGroundPoint

end Stafford38.Geometry.PrescribedAffineResidueCompletionConsumer
