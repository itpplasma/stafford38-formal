import Stafford38.Geometry.GeneralDivisorialVisibleFrameResidueSupport
import Stafford38.Geometry.ProjectiveDivisorOrderGap

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.ActualWitnessStrictOrderGap

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.ProjectiveDivisorOrderGap

noncomputable section

universe u

/-- The actual normalized projective witness has a strict order gap with
respect to any supplied irreducible uniformizer of its retained DVR. The
ratio is the retained place parameter; in particular, this theorem does not
identify the projective denominator `q₀` with the uniformizer. -/
theorem exists_actual_witness_strict_orderGap
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    letI : Algebra (CoordinateZeroLocalRing w.column.W.coefficientField)
      (ComponentFractionField P) := w.column.W.ambientAlgebra
    let C := w.column
    let W := C.W
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
    ∀ (π : V), Irreducible π →
      ∃ (a r b : ℕ) (u₀ ur u₁ : Vˣ),
        0 < a ∧ 0 < r ∧ b = a + r ∧ a < b ∧
        C.q 0 = (u₀ : V) * π ^ a ∧
        W.place.parameter = (ur : V) * π ^ r ∧
        u₁ = u₀ * ur ∧
        C.q (Fin.succ ⟨0, hm⟩) = (u₁ : V) * π ^ b := by
  classical
  dsimp only
  intro π hπ
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  have hq₀max : C.q 0 ∈ maximalIdeal V :=
    GeneralDivisorialVisibleFrame.witness_q0_mem_maximal hm P w
  have hratioMax : W.place.parameter ∈ maximalIdeal V := by
    apply (IsLocalRing.mem_maximalIdeal _).2
    exact mem_nonunits_iff.mpr W.place.parameter_nonunit
  exact ProjectiveDivisorOrderGap.exists_uniformizer_strict_orderGap
    π hπ (C.q 0) W.place.parameter (C.q (Fin.succ ⟨0, hm⟩))
    C.q0_ne W.place.parameter_ne hq₀max hratioMax C.q_parameter


end

end Stafford38.Geometry.ActualWitnessStrictOrderGap
