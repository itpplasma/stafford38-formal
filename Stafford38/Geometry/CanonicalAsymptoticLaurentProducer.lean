module
public import Stafford38.CanonicalSupportVanishingReduction
public import Stafford38.Geometry.ProjectiveDivisorOrderGap
public import Stafford38.Geometry.ProjectiveEquationFormalChart
public import Stafford38.Geometry.ProjectiveTangentInclusion
public import Stafford38.Geometry.LaurentConormalResidueExtension

@[expose] public section

/-!
# Completed-chart conormal consumer

The base-field chart is an alias of the shared residue-extension certificate.
Its homogeneous equations, divisor-tangent columns, order gap, and fixed
compatible tangent witness give a Laurent conormal covector with axis residue.
The global adapter uses chart production for the canonical reduced base ideal
as its input.
-/

namespace Stafford38.Geometry.CanonicalAsymptoticLaurentProducer

open Stafford38
open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.Characteristic
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.ProjectiveTangentInclusion
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.GeometryRetractionSpecialization
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

/-! ## The exact local certificate -/

/-- Base-field compatibility name for the shared residue-extension chart.
The case `K = k` has the same fields and ground coefficient map, so the
residue-extension record is the sole owner. -/
abbrev CompletedProjectiveBoundaryChart
    (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) :=
  Stafford38.Geometry.LaurentConormalResidueExtension.CompletedProjectiveBoundaryChartOver
    (k := k) (K := k) m hm I

/-! ## Local consumer theorem -/

/--
The completed-DVR/projective certificate supplies the Laurent conormal axis.

The proof has four explicit interfaces: the projective order-gap theorem
constructs the formal annihilating row; homogeneous equation vanishing gives
the base-equation condition after dehomogenization; tangent inclusion feeds
the weaker Laurent conormal bridge; and the axis equation identifies the
regular fibre residue with the pure first momentum direction.
-/
theorem exists_conormalAxis_of_completedProjectiveBoundaryChart
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChart k m hm I) :
    ∃ (y : Fin m → LaurentSeries k)
      (xi : Fin m → PowerSeries k),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈
        equationConormalLocus
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin m))) ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  simpa [Stafford38.Geometry.LaurentConormalResidueExtension.groundEquationConormalLocus,
    Stafford38.Geometry.LaurentConormalResidueExtension.groundPolynomialMap,
    Stafford38.Geometry.ScalarExtensionPoints.scalarPolynomialMap] using
    Stafford38.Geometry.LaurentConormalResidueExtension.exists_conormalAxis_of_completedProjectiveBoundaryChartOver
      (k := k) (K := k) hm I W

/-! ## Global chart-production interface -/

/-- Global production of a completed chart for the canonical reduced base
ideal. The chart stores the geometric construction and tangent inclusion;
it has no support-vanishing conclusion as a field. -/
def CanonicalBoundaryChartProduction : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N →
    IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
    Disjoint
      (orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) →
    (orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N)).Nonempty →
    Nonempty (CompletedProjectiveBoundaryChart k (n + 1) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)))

/--
The exact adapter from global boundary-chart production to the canonical
Laurent producer.  All support hypotheses are used only to request a chart;
the chart-to-conormal proof itself has no support-vanishing premise.
-/
theorem canonicalAsymptoticLaurentProducer_of_boundaryChartProduction
    (hproduction : CanonicalBoundaryChartProduction.{u}) :
    CanonicalAsymptoticLaurentProducer.{u} := by
  intro k _ _ _ n N d hN hd hdisjoint hnonempty
  obtain ⟨W⟩ :=
    hproduction k n N d hN hd hdisjoint hnonempty
  obtain ⟨y, xi, hmem, haxis⟩ :=
    exists_conormalAxis_of_completedProjectiveBoundaryChart
      (k := k) (m := n + 1) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)) W
  exact ⟨y, xi, hmem, haxis⟩

#print axioms exists_conormalAxis_of_completedProjectiveBoundaryChart
#print axioms canonicalAsymptoticLaurentProducer_of_boundaryChartProduction

end

end Stafford38.Geometry.CanonicalAsymptoticLaurentProducer
