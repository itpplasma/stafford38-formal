import Stafford38.Geometry.GeneralDivisorialVisibleFrameCoreData

set_option autoImplicit false

namespace Stafford38.Geometry.GeneralDivisorialVisibleFrame

open IsLocalRing Polynomial
open Stafford38
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.DivisorTangentLattice
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

universe u

/-! Reducible aliases factor the shared residue-algebra context without
changing either witness field's proposition. -/
namespace GeneralDivisorialVisibleFrameWitnessFieldType

abbrev retainedGroundMap
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (column : GeneralDivisorialVisibleFrameColumn hm P) :=
  letI : Algebra (CoordinateZeroLocalRing column.W.coefficientField)
      (ComponentFractionField P) := column.W.ambientAlgebra
  let V := column.W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := column.W.place.isDiscrete
  letI : Algebra column.W.coefficientField V :=
      (relativeCoefficientMap column.W.coefficientField column.W.place).toAlgebra
  letI : Algebra k (ResidueField V) :=
      retainedResidueGroundAlgebra P ⟨0, hm⟩ column.W
  algebraMap k (ResidueField V) =
    (residue V).comp
      (retainedComponentCoefficientMap P ⟨0, hm⟩ column.W)

abbrev halg
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (column : GeneralDivisorialVisibleFrameColumn hm P) :=
  letI : Algebra (CoordinateZeroLocalRing column.W.coefficientField)
      (ComponentFractionField P) := column.W.ambientAlgebra
  let V := column.W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := column.W.place.isDiscrete
  letI : Algebra column.W.coefficientField V :=
      (relativeCoefficientMap column.W.coefficientField column.W.place).toAlgebra
  letI : Algebra k (ResidueField V) :=
      retainedResidueGroundAlgebra P ⟨0, hm⟩ column.W
  Algebra.IsAlgebraic
    (IntermediateField.adjoin k
      (Set.range fun j : Fin m ↦ residue V (column.q (Fin.succ j))) :
      IntermediateField k (ResidueField V))
    (ResidueField V)

end GeneralDivisorialVisibleFrameWitnessFieldType

/-- The same retained column and differential frame carry Lane-C's actual
residue algebraicity in the retained ground-field structure. -/
structure GeneralDivisorialVisibleFrameWitness
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) where
  column : GeneralDivisorialVisibleFrameColumn hm P
  differential : GeneralDivisorialVisibleFrameDifferential hm P column
  retainedGroundMap :
    GeneralDivisorialVisibleFrameWitnessFieldType.retainedGroundMap hm P column
  halg : GeneralDivisorialVisibleFrameWitnessFieldType.halg hm P column

end

end Stafford38.Geometry.GeneralDivisorialVisibleFrame
