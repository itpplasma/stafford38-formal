module
public import Stafford38.Geometry.SameWitnessTranscendenceDegreeBound

@[expose] public section

set_option autoImplicit false

universe u

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedGroundMapIdentification

example {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : Stafford38.Geometry.GeneralDivisorialVisibleFrame.GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1 :=
  Stafford38.Geometry.SameWitnessTranscendenceDegreeBound.component_trdeg_le_residue_trdeg_add_one_of_witness hm P w

#check Stafford38.Geometry.SameWitnessTranscendenceDegreeBound.component_trdeg_le_residue_trdeg_add_one_of_witness
#print axioms Stafford38.Geometry.SameWitnessTranscendenceDegreeBound.component_trdeg_le_residue_trdeg_add_one_of_witness
