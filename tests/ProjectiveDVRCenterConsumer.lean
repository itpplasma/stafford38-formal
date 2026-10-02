import Stafford38.Geometry.ProjectiveDVRCenter

/-!
# Consumer for the center-to-DVR uniqueness lemma

This literal consumer retains the full same-field and local-domination
hypotheses. The theorem's own `#print axioms` is checked by the audit runner.
-/

open IsLocalRing

universe u

section

variable {K : Type u} [Field K] (R : Subring K)
local instance : Algebra R K := R.subtype.toAlgebra

theorem dvr_center_consumer [IsDiscreteValuationRing R] [IsFractionRing R K]
    (V : ValuationSubring K)
    (hdom : (LocalSubring.mk R : LocalSubring K) ≤ V.toLocalSubring) :
    R = V.toSubring :=
  Stafford38.Geometry.ProjectiveDVRCenter.dvr_eq_of_dominated_by_valuationSubring
    R V hdom

#print axioms dvr_center_consumer

end

#print axioms Stafford38.Geometry.ProjectiveDVRCenter.dvr_eq_of_dominated_by_valuationSubring
