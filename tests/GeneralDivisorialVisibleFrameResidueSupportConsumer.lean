module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrameResidueSupport

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.GeneralDivisorialVisibleFrame

open IsLocalRing Polynomial
open Stafford38
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace

universe u

theorem witness_q0_residue_consumer
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
        (ComponentFractionField P) := w.column.W.ambientAlgebra
    let V := w.column.W.place.valuation.toSubring
    letI : IsLocalRing V := w.column.W.place.isDiscrete.toIsLocalRing
    residue V (w.column.q 0) = 0 := by
  exact witness_q0_residue_eq_zero hm P w

theorem witness_retained_halg_consumer
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    GeneralDivisorialVisibleFrameWitnessFieldType.halg hm P w.column := by
  exact w.halg

#print axioms witness_q0_residue_consumer
#print axioms witness_retained_halg_consumer

end Stafford38.Geometry.GeneralDivisorialVisibleFrame
