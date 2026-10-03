module
public import Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Stafford38.Geometry.PrescribedGroundPointPowerSeriesMapConsumer

open Stafford38.Geometry.PrescribedAffineResidueCompletion
open Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap

noncomputable section

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial (Fin 2) k) B]
  [IsScalarTower k (MvPolynomial (Fin 2) k) B]
  [Algebra.EssFiniteType (MvPolynomial (Fin 2) k) B]
variable (M : Ideal B) (eM : (B ⧸ M) ≃ₐ[k] k) [M.IsMaximal]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) k) (Localization.AtPrime M)]

/-- Independent behavior check: on a two-coordinate chart, the prescribed map
sends `X₀ + c X₁` to its residue value plus the expected tilted linear term.
This checks the coordinate order, scalar preservation, and the `t`-axis sign. -/
theorem twoCoordinateLinearCombination (α : Fin 1 → k) (c : k) :
    originalAlgebraToPowerSeriesArc (M := M) (B := B) α eM
      (algebraMap (MvPolynomial (Fin 2) k) B (MvPolynomial.X 0) +
        algebraMap k B c * algebraMap (MvPolynomial (Fin 2) k) B (MvPolynomial.X 1)) =
      PowerSeries.C
          (residueCoordinates (σ := Fin 2) M eM 0 +
            c * residueCoordinates (σ := Fin 2) M eM 1) +
        PowerSeries.C (1 + c * α 0) * PowerSeries.X := by
  let F := originalAlgebraToPowerSeriesArc (M := M) (B := B) α eM
  change F (algebraMap (MvPolynomial (Fin 2) k) B (MvPolynomial.X 0) +
      algebraMap k B c * algebraMap (MvPolynomial (Fin 2) k) B (MvPolynomial.X 1)) = _
  rw [map_add, map_mul]
  rw [originalAlgebraToPowerSeriesArc_coordinate (M := M) (B := B) α eM 0]
  rw [originalAlgebraToPowerSeriesArc_coordinate (M := M) (B := B) α eM 1]
  rw [F.commutes]
  simp
  ring

#print axioms twoCoordinateLinearCombination

end
end Stafford38.Geometry.PrescribedGroundPointPowerSeriesMapConsumer

#print axioms Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.localToPowerSeries

#print axioms Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.originalAlgebraToPowerSeries_coordinate

#print axioms Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.originalAlgebraToPowerSeriesArc_coordinate
