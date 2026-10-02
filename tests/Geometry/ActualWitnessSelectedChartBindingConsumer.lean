import Stafford38.Geometry.ActualWitnessSelectedChartBinding

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Stafford38.Geometry.ActualWitnessSelectedChartBindingConsumer

open Stafford38.Geometry.A0NormalizedProjectiveCoordinates
open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.ActualWitnessSelectedChartBinding
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.EtaleGenericOpenTransport

universe u v w

/-- Independent literal consumer: the actual witness tuple maps to the same
common-open coordinates used by the canonical quotient argument, so it obeys
the original-generator multiplication identities in that exact ring. -/
theorem actual_retained_witness_projective_relation
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (j : Fin m) (hchart : w.column.chart = Fin.succ j)
    {B : Type w} [CommRing B]
    [Algebra (Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))) B]
    (M : Ideal B) [M.IsPrime]
    (f : Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j))))
    (e : Localization.Away f ≃ₐ[
      Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))]
      Localization.Away (algebraMap _ B f)) :
    let hxj := actualWitness_selected_coordinate_ne_zero hm P w j hchart
    let F := ComponentFractionField P
    let W := w.column.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : Algebra V F := V.subtype.toAlgebra
    let Cactual := w.column
    let Q := Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
        (SelectedAffineCoordinateEquiv j) (by
          simpa [componentProjectivePoint] using hxj)
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    let φ := originalAffineChartToCommonOpen P j hxj hsel M f e
    let qC : Fin (m + 1) → C := Fin.cases
      (algebraMap Cq C (algebraMap Q Cq g))
      (fun i => if hij : i = j then 1 else
        algebraMap Cq C (algebraMap Q Cq
          (hsel (selectedAffineChartVariableClass P j i hij))))
    ∃ qQ : Fin (m + 1) → Q,
      qQ (Fin.succ j) = 1 ∧
      (∀ a, ((qQ a : Q) : F) =
        ((Cactual.q a : Cactual.W.place.valuation.toSubring) : F)) ∧
      qQ 0 = hsel (selectedAffineChartDenominator P j) ∧
      (∀ i : Fin m, ∀ hij : i ≠ j,
        qQ (Fin.succ i) = hsel (selectedAffineChartVariableClass P j i hij)) ∧
      (∀ a, algebraMap Q C (qQ a) = qC a) ∧
      ∀ i : Fin m,
        algebraMap Q C (qQ (Fin.succ i)) =
          algebraMap Q C (qQ 0) *
            φ (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := by
  classical
  dsimp only
  have hxj := actualWitness_selected_coordinate_ne_zero hm P w j hchart
  let Q := Algebra.adjoin k (Set.range
    (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
    componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
      (SelectedAffineCoordinateEquiv j) (by
        simpa [componentProjectivePoint] using hxj)
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  let φ := originalAffineChartToCommonOpen P j hxj hsel M f e
  let qC : Fin (m + 1) → C := Fin.cases
    (algebraMap Cq C (algebraMap Q Cq g))
    (fun i => if hij : i = j then 1 else
      algebraMap Cq C (algebraMap Q Cq
        (hsel (selectedAffineChartVariableClass P j i hij))))
  obtain ⟨qQ, hqchart, hqcoe, hq0, hqvars, hmap⟩ :=
    actualWitness_commonOpen_q_coordinates (B := B) hm P w j hchart M f e
  have hcanonical := canonicalChart_all_normalized_projective_coordinates
    (B := B) P j hxj M f e
  refine ⟨qQ, hqchart, hqcoe, hq0, hqvars, hmap, ?_⟩
  intro i
  rw [hmap (Fin.succ i), hmap 0]
  exact hcanonical.2 i

#print axioms actual_retained_witness_projective_relation

end Stafford38.Geometry.ActualWitnessSelectedChartBindingConsumer
end
