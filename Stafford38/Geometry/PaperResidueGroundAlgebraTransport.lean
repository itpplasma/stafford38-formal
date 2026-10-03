module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrameColumn

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace Stafford38.Geometry.PaperResidueGroundAlgebraTransport

open IsLocalRing
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.RetainedDVR

universe u

theorem canonical_residue_algebra_eq_composite
    {k V : Type u} [Field k] [CharZero k]
    [CommRing V] [IsLocalRing V] [Algebra k V] :
    ((residue V).comp (algebraMap k V)).toAlgebra =
      (inferInstance : Algebra k (ResidueField V)) := by
  apply Algebra.algebra_ext
  intro c
  rfl

theorem algebraic_adjoin_transfer_of_algebra_eq
    {k L : Type u} [Field k] [Field L]
    (A B : Algebra k L) (hAB : A = B) (s : Set L)
    (hA : letI : Algebra k L := A;
      Algebra.IsAlgebraic (IntermediateField.adjoin k s : IntermediateField k L) L) :
    letI : Algebra k L := B;
      Algebra.IsAlgebraic (IntermediateField.adjoin k s : IntermediateField k L) L :=
  Stafford38.Geometry.GeneralDivisorialVisibleFrame.algebraic_adjoin_transfer_of_algebra_eq
    A B hAB s hA

theorem kaehler_finrank_eq_of_algebra_eq
    {k L : Type u} [Field k] [Field L]
    (A B : Algebra k L) (hAB : A = B) :
    (letI : Algebra k L := A; Module.finrank L (Ω[L⁄k])) =
      (letI : Algebra k L := B; Module.finrank L (Ω[L⁄k])) := by
  cases hAB
  rfl

theorem retained_algebra_eq_composite
    {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k V :=
      (retainedComponentCoefficientMap P i W).toAlgebra
    retainedResidueGroundAlgebra P i W =
      ((residue V).comp (algebraMap k V)).toAlgebra := by
  dsimp only
  rfl

#print axioms canonical_residue_algebra_eq_composite
#print axioms algebraic_adjoin_transfer_of_algebra_eq
#print axioms kaehler_finrank_eq_of_algebra_eq

end Stafford38.Geometry.PaperResidueGroundAlgebraTransport
