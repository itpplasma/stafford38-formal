module
public import Stafford38.Geometry.ActualCommonOpenCompletionDerivation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Stafford38.Geometry.ActualCommonOpenCompletionDerivationConsumer

open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.EtaleCotangentBasis

noncomputable section

universe u v w
variable {k : Type u} [Field k] {d : ℕ}
local notation "R" => MvPolynomial (Option (Fin d)) k
variable {A : Type v} [CommRing A] [Algebra k A]
  [Algebra (MvPolynomial (Option (Fin d)) k) A]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]
variable {Q : Type w} [CommRing Q] [Algebra Q A]

/-- Literal consumer at an original polynomial coordinate, using the actual
common-open map and the actual local ring map. -/
theorem originalParameter_derivation_bridge
    {L : Type*} [Field L]
    (M : Ideal A) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    (ρ : A →+* L)
    (hf : IsUnit (ρ (algebraMap Q A f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b))
    (hg : IsUnit (ρ (algebraMap Q A g)))
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (j : Option (Fin d)) (a : A) :
    let T := Localization.AtPrime M
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra A T := inferInstance
    letI : Algebra R T := inferInstance
    letI : Algebra R Cq :=
      ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    letI : IsScalarTower k R T := by infer_instance
    letI : Algebra k U := Algebra.compHom U (algebraMap k R)
    letI : SMul R U := (inferInstance : Algebra R U).toSMul
    letI : SMul k U := (inferInstance : Algebra k U).toSMul
    letI : IsScalarTower k R U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      rfl
    let θ := pointLocalToCommonOpenAlg (k := k) (d := d) (A := A) M f e g
    letI : Algebra T U := θ.toRingHom.toAlgebra' (fun x y => mul_comm (θ x) y)
    letI : SMul T U := (inferInstance : Algebra T U).toSMul
    letI : SMul U U := (inferInstance : Algebra U U).toSMul
    letI : IsScalarTower k T U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      change algebraMap k U c = algebraMap T U (algebraMap k T c)
      rw [RingHom.algebraMap_toAlgebra' _ (fun x y => mul_comm (θ x) y)]
      exact (θ.commutes c).symm
    letI : IsScalarTower T U U := ⟨fun t u₁ u₂ => by
      change (algebraMap T U t * u₁) * u₂ =
        algebraMap T U t * (u₁ * u₂)
      exact mul_assoc _ _ _⟩
    letI : Algebra.FormallyEtale R U :=
      formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
    genericArcToGenericOpenExtraAwayB M f e ρ hf hunitM g hg
      (EtaleCotangentBasis.coordinateDerivation (k := k)
        (σ := Option (Fin d)) (B := U) (L := U) j
        (pointLocalToCommonOpen (A := A) M f e g
          (algebraMap A T a))) =
    localPointToField (B := A) M ρ hunitM
      (EtaleCotangentBasis.coordinateDerivation (k := k)
        (σ := Option (Fin d)) (B := T) (L := T) j
        (algebraMap A T a)) := by
  exact genericArc_coordinateDerivation_on_pointLocal
    (k := k) (d := d) (A := A) M f e g ρ hf hunitM hg j
      (algebraMap A (Localization.AtPrime M) a)

/-- The actual common-open map preserves the ground field for the canonical
Laurent-series arc; this checks the coefficient map used by the tangent
ideal consumer. -/
theorem canonicalLaurentArc_preserves_ground
    (M : Ideal A) [M.IsMaximal] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q A f)) (g : Q)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (eM : (A ⧸ M) ≃ₐ[k] k) (α : Fin d → k)
    (hf : IsUnit (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α (algebraMap Q A f)))
    (hunitM : ∀ b, b ∉ M → IsUnit
      (originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := A) M eM α b))
    (hg : IsUnit (originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := A) M eM α (algebraMap Q A g))) (c : k) :
    let T := Localization.AtPrime M
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Algebra A T := inferInstance
    letI : Algebra R T := inferInstance
    letI : Algebra R Cq :=
      ((algebraMap A Cq).comp (algebraMap R A)).toAlgebra
    letI : Algebra R U := Algebra.compHom U (algebraMap R Cq)
    letI : IsScalarTower k R T := by infer_instance
    letI : Algebra k U := Algebra.compHom U (algebraMap k R)
    letI : SMul R U := (inferInstance : Algebra R U).toSMul
    letI : SMul k U := (inferInstance : Algebra k U).toSMul
    letI : IsScalarTower k R U := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro c
      rfl
    genericArcToGenericOpenExtraAwayB M f e
      (originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := A) M eM α) hf hunitM g hg
      (algebraMap k U c) = algebraMap k (LaurentSeries k) c := by
  exact genericArcToPointLocalLaurentSeries_base
    (k := k) (d := d) (A := A) M f e g eM α hf hunitM hg c

#print axioms originalParameter_derivation_bridge
#print axioms canonicalLaurentArc_preserves_ground

end
end Stafford38.Geometry.ActualCommonOpenCompletionDerivationConsumer
