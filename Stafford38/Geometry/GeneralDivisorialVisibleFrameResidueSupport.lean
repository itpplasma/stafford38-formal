import Stafford38.Geometry.GeneralDivisorialVisibleFrameWitness

set_option autoImplicit false

namespace Stafford38.Geometry.GeneralDivisorialVisibleFrame

open IsLocalRing Polynomial
open Stafford38
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

/-! Derived residue facts for the already-produced normalized witness.  These
do not duplicate or strengthen its data: they use the stored visible frame's
order factorization. -/

theorem witness_q0_mem_maximal
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
        (ComponentFractionField P) := w.column.W.ambientAlgebra
    let V := w.column.W.place.valuation.toSubring
    letI : IsLocalRing V := w.column.W.place.isDiscrete.toIsLocalRing
    w.column.q 0 ∈ maximalIdeal V := by
  let C := w.column
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
  let V := C.W.place.valuation.toSubring
  letI : IsLocalRing V := C.W.place.isDiscrete.toIsLocalRing
  letI : Algebra C.W.coefficientField V :=
    (relativeCoefficientMap C.W.coefficientField C.W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V (ComponentFractionField P) := V.subtype.toAlgebra
  letI : IsScalarTower k V (ComponentFractionField P) := C.groundTower
  let D := w.differential.core.D
  have hpos : 0 < D.a := lt_of_lt_of_le Nat.zero_lt_one D.one_le_a
  have hpow : D.t ^ D.a ∈ maximalIdeal V :=
    Ideal.pow_mem_of_mem _ D.t_mem D.a hpos
  change C.q 0 ∈ maximalIdeal V
  rw [← w.differential.core.D_Q0, D.Q₀_eq]
  exact Ideal.mul_mem_right _ _ hpow

theorem witness_q0_residue_eq_zero
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
        (ComponentFractionField P) := w.column.W.ambientAlgebra
    let V := w.column.W.place.valuation.toSubring
    letI : IsLocalRing V := w.column.W.place.isDiscrete.toIsLocalRing
    residue V (w.column.q 0) = 0 := by
  letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
      (ComponentFractionField P) := w.column.W.ambientAlgebra
  let V := w.column.W.place.valuation.toSubring
  letI : IsLocalRing V := w.column.W.place.isDiscrete.toIsLocalRing
  exact (IsLocalRing.residue_eq_zero_iff _).2
    (witness_q0_mem_maximal hm P w)

#print axioms witness_q0_mem_maximal
#print axioms witness_q0_residue_eq_zero

end Stafford38.Geometry.GeneralDivisorialVisibleFrame
