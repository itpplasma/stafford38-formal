import Mathlib.RingTheory.SimpleRing.Principal
import Stafford38.Geometry.AsymptoticDivisorExistence
import Stafford38.Geometry.AffineComponentCoordinateSplit
import Stafford38.Geometry.ComponentFunctionFieldBoundary
import Stafford38.Geometry.ComponentProjectiveClosure
import Stafford38.Geometry.ComponentProjectiveClosureNormalization
import Stafford38.Geometry.CompletedDVRPowerSeriesEquiv
import Stafford38.Geometry.DivisorTangentLattice
import Stafford38.Geometry.RelativeRetainedBoundaryPlace
import Stafford38.Geometry.RetainedGroundMapIdentification

set_option autoImplicit false

/-!
# Divisorial visible frames for arbitrary prime affine components

An invertible, transcendental coordinate on a prime affine component gives
a normalized visible divisor frame. This removes the canonical Weyl-support
hypotheses from the boundary producer. Identification of the resulting Laurent
direction with the smooth projective conormal closure is performed downstream
in the general asymptotic-conormal construction.
-/

namespace Stafford38.Geometry.GeneralDivisorialVisibleFrame

open IsLocalRing Polynomial
open Stafford38
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.DivisorTangentLattice
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

universe u

/-- Transport residue algebraicity across an equality of ground algebra
structures. -/
theorem algebraic_adjoin_transfer_of_algebra_eq
    {k L : Type u} [Field k] [Field L]
    (A B : Algebra k L) (hAB : A = B) (s : Set L)
    (hA : letI : Algebra k L := A;
      Algebra.IsAlgebraic (IntermediateField.adjoin k s : IntermediateField k L) L) :
    letI : Algebra k L := B;
      Algebra.IsAlgebraic (IntermediateField.adjoin k s : IntermediateField k L) L := by
  cases hAB
  exact hA

/-- The normalized Lane-C projective column and the actual retained ground
coefficient map. -/
structure GeneralDivisorialVisibleFrameColumn
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) where
  W : Data k (ComponentFractionField P) (componentCoordinate P ⟨0, hm⟩)
  chart : Fin (m + 1)
  q :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    Fin (m + 1) → W.place.valuation.toSubring
  scale : ComponentFractionField P
  scale_ne : scale ≠ 0
  chart_one :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    q chart = 1
  q0_ne :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    q 0 ≠ 0
  q_commonScale : ∀ a,
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    (q a : ComponentFractionField P) = scale * componentProjectivePoint P a
  q_parameter :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    q (Fin.succ ⟨0, hm⟩) = q 0 * W.place.parameter
  groundCoeff :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    k →+* W.place.valuation.toSubring
  groundCoeff_commutes :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    W.place.valuation.toSubring.subtype.comp groundCoeff =
      algebraMap k (ComponentFractionField P)
  groundCoeff_eq_retained :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    groundCoeff = retainedComponentCoefficientMap P ⟨0, hm⟩ W
  groundTower :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : Algebra k V := groundCoeff.toAlgebra
    letI : Algebra V (ComponentFractionField P) := V.subtype.toAlgebra
    IsScalarTower k V (ComponentFractionField P)

set_option maxHeartbeats 4000000


end

end Stafford38.Geometry.GeneralDivisorialVisibleFrame
