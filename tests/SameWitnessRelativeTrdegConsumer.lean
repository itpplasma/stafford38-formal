import Stafford38.Geometry.SameWitnessRelativeTranscendenceDegree

set_option autoImplicit false

namespace Stafford38.Geometry.SameWitnessRelativeTranscendenceDegreeConsumer

open Stafford38.Geometry.SameWitnessRelativeTranscendenceDegree

universe u

/-- Import-side consumer for the finite-basis/local-parameter API. -/
theorem finiteBasisLocalParameterConsumer
    {k E V F κ ι : Type u}
    [Field k] [Field E] [Fintype ι] [CommRing V] [IsDomain V] [IsLocalRing V]
    [Field F] [Field κ]
    [Algebra k E] [Algebra E V] [Algebra E F] [Algebra V F]
    [IsScalarTower E V F] [Algebra k F] [IsScalarTower k E F]
    [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (basis : ι → E) (hbasis : IsTranscendenceBasis k basis)
    (hVF : Function.Injective (algebraMap V F))
    (x : V) (hx0 : x ≠ 0) (hxM : x ∈ IsLocalRing.maximalIdeal V)
    (hκalg : Algebra.IsAlgebraic E κ)
    (hbound : Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1) :
    Algebra.trdeg E F = 1 := by
  exact eq_one_of_same_total_bound_of_finite_basis_and_parameter
    basis hbasis hVF x hx0 hxM hκalg hbound

#print axioms finiteBasisLocalParameterConsumer

end Stafford38.Geometry.SameWitnessRelativeTranscendenceDegreeConsumer
