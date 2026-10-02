import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Equality of a centered DVR with a dominating valuation ring

This is the final local-algebra step in identifying a divisorial valuation
with the local ring at its center. It does not construct a proper model, a
center, or prove that the center has codimension one.
-/

namespace Stafford38.Geometry.ProjectiveDVRCenter

open IsLocalRing

universe u

section

variable {K : Type u} [Field K] (R : Subring K)

local instance subringAlgebra : Algebra R K := R.subtype.toAlgebra

/-- A DVR subring of a field equals any valuation subring of that field which
locally dominates it. The domination hypothesis is precisely the algebraic
condition obtained after the center is known to be height one. -/
theorem dvr_eq_of_dominated_by_valuationSubring
    [IsDiscreteValuationRing R] [IsFractionRing R K] (V : ValuationSubring K)
    (hdom : (LocalSubring.mk R : LocalSubring K) ≤ V.toLocalSubring) :
    R = V.toSubring := by
  let vR : ValuationSubring K :=
    ((IsDiscreteValuationRing.maximalIdeal R).valuation K).valuationSubring
  have hcarrier : vR.toSubring = R := by
    change ((IsDiscreteValuationRing.maximalIdeal R).valuation K).valuationSubring.toSubring = R
    rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
    ext x
    simp only [Subring.mem_map]
    constructor
    · rintro ⟨a, ha, hax⟩
      change (a : K) = x at hax
      exact hax ▸ a.property
    · intro hx
      refine ⟨⟨x, hx⟩, Set.mem_univ _, ?_⟩
      rfl
  have hlocal : vR.toLocalSubring = (LocalSubring.mk R : LocalSubring K) := by
    apply LocalSubring.toSubring_injective
    exact hcarrier
  have hmax : IsMax (LocalSubring.mk R : LocalSubring K) := by
    rw [← hlocal]
    exact vR.isMax_toLocalSubring
  have heq := hmax.eq_of_le hdom
  exact congrArg LocalSubring.toSubring heq

#print axioms dvr_eq_of_dominated_by_valuationSubring

end

end Stafford38.Geometry.ProjectiveDVRCenter
