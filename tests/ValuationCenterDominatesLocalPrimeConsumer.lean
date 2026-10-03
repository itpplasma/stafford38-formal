module
public import Stafford38.Geometry.ValuationCenterDominatesLocalPrime

@[expose] public section

noncomputable section
set_option autoImplicit false

open Stafford38.Geometry

/-- Independent consumer for a chart subring whose prime is the contraction of the
retained valuation ring's maximal ideal. -/
example {K : Type*} [Field K] (A : Subring K) (V : ValuationSubring K)
    (hAV : A ≤ V.toSubring) (p : Ideal A) [p.IsPrime]
    (hcenter : (IsLocalRing.maximalIdeal V.toLocalSubring.toSubring).comap
      (Subring.inclusion hAV) = p) :
    LocalSubring.ofPrime A p ≤ V.toLocalSubring :=
  localRing_at_contracted_maximalIdeal_le_valuationSubring A V hAV p hcenter

#print axioms Stafford38.Geometry.localRing_at_contracted_maximalIdeal_le_valuationSubring
