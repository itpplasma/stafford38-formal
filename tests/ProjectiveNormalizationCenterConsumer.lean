import Stafford38.Geometry.ProjectiveChartNormalizationFinite
import Stafford38.Geometry.ProjectiveChartNormalizationCenter

set_option autoImplicit false

universe u

open Stafford38.Geometry.ProjectiveChartNormalizationCenter
open IsLocalRing

theorem normalization_center_nonzero_consumer {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) (r : R) (hr0 : (r : K) ≠ 0)
    (hrmax : (Subring.inclusion hRV r) ∈ maximalIdeal V.toLocalSubring.toSubring) :
    integralClosureCenter R V hRV ≠ ⊥ :=
  integralClosureCenter_ne_bot_of_nonzero_maximal R V hRV r hr0 hrmax

theorem normalization_center_prime_consumer {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) :
    (integralClosureCenter R V hRV).IsPrime :=
  integralClosureCenter_isPrime R V hRV

theorem normalization_center_residue_kernel_consumer {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) :
    integralClosureCenter R V hRV =
      RingHom.ker
        ((Ideal.Quotient.mk (maximalIdeal V.toLocalSubring.toSubring)).comp
          (Subring.inclusion (integralClosure_subring_le_valuationSubring R V hRV))) :=
  integralClosureCenter_eq_residueKernel R V hRV

theorem normalization_center_domination_consumer {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) :
    letI : (integralClosureCenter R V hRV).IsPrime :=
      integralClosureCenter_isPrime R V hRV
    LocalSubring.ofPrime (integralClosure R K).toSubring
      (integralClosureCenter R V hRV) ≤ V.toLocalSubring := by
  exact localRing_at_integralClosureCenter_le_valuationSubring R V hRV
    (integralClosureCenter_isPrime R V hRV)

#print axioms integralClosureCenter_ne_bot_of_nonzero_maximal
#print axioms localRing_at_integralClosureCenter_le_valuationSubring
#print axioms Stafford38.Geometry.ProjectiveChartNormalizationFinite.finite_integralClosure_in_fractionField

#print axioms normalization_center_nonzero_consumer
#print axioms normalization_center_prime_consumer
#print axioms normalization_center_residue_kernel_consumer
#print axioms normalization_center_domination_consumer
