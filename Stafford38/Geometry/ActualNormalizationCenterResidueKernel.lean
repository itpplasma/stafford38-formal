import Stafford38.Geometry.ProjectiveChartNormalizationCenter

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.ActualNormalizationCenterResidueKernel

open IsLocalRing

universe u

/-- A ring map from the integral closure into the retained valuation ring that
preserves the ambient-field value induces exactly the canonical contracted
residue-kernel center. -/
theorem residue_kernel_eq_canonical_center_comap
    {F : Type u} [Field F]
    (R : Subring F) (U : ValuationSubring F)
    [IsLocalRing U.toSubring]
    (hRV : R ≤ U.toSubring)
    (eB : (integralClosure R F) ≃+* (integralClosure R F).toSubring)
    (fB : (integralClosure R F) →+* U.toSubring)
    (heB : ∀ b, ((eB b : (integralClosure R F).toSubring) : F) = b)
    (hfB : ∀ b, ((fB b : U.toSubring) : F) = b) :
    RingHom.ker ((residue U.toSubring).comp fB) =
      (ProjectiveChartNormalizationCenter.integralClosureCenter R U hRV).comap
        eB.toRingHom := by
  let hBV :=
    ProjectiveChartNormalizationCenter.integralClosure_subring_le_valuationSubring
      R U hRV
  let center := ProjectiveChartNormalizationCenter.integralClosureCenter R U hRV
  ext b
  change residue U.toSubring (fB b) = 0 ↔ eB b ∈ center
  rw [IsLocalRing.residue_eq_zero_iff]
  have hmap : Subring.inclusion hBV (eB b) = fB b := by
    apply Subtype.ext
    calc
      ((eB b : (integralClosure R F).toSubring) : F) = b := heB b
      _ = ((fB b : U.toSubring) : F) := (hfB b).symm
  rw [← hmap]
  change Subring.inclusion hBV (eB b) ∈ maximalIdeal U.toSubring ↔
      eB b ∈ (maximalIdeal U.toLocalSubring.toSubring).comap
        (Subring.inclusion hBV)
  change Subring.inclusion hBV (eB b) ∈ maximalIdeal U.toSubring ↔
      Subring.inclusion hBV (eB b) ∈ maximalIdeal U.toLocalSubring.toSubring
  rfl

end Stafford38.Geometry.ActualNormalizationCenterResidueKernel
