module
public import Stafford38.Geometry.SameWitness.OriginalPrimeAxis

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.SameWitness.OriginalPrimeAxisConsumer

open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.SameWitness

universe u

/-- Literal consumer for the axis closure theorem at the original prime. -/
theorem coordinate_axis_mem_smooth_fibre_closure_consumer
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) := by
  exact coordinate_axis_mem_smooth_fibre_closure hm I havoid

#print axioms coordinate_axis_mem_smooth_fibre_closure
#print axioms coordinate_axis_mem_smooth_fibre_closure_consumer

end Stafford38.Geometry.SameWitness.OriginalPrimeAxisConsumer
