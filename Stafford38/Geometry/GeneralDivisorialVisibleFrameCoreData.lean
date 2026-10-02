import Stafford38.Geometry.GeneralDivisorialVisibleFrameColumn

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

/-! These reducible aliases share the repeated local-algebra context for
the frame and the three coordinate equalities.  The maximal-ideal and
unit fields below stay inline because their dependent `D` binders otherwise
fail to elaborate at the producer boundary. -/
namespace GeneralDivisorialVisibleFrameCoreFieldType

abbrev frame
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P) :=
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
  let V := C.W.place.valuation.toSubring
  letI : IsLocalRing V := C.W.place.isDiscrete.toIsLocalRing
  letI : Algebra C.W.coefficientField V :=
      (relativeCoefficientMap C.W.coefficientField C.W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V (ComponentFractionField P) := V.subtype.toAlgebra
  letI : IsScalarTower k V (ComponentFractionField P) := C.groundTower
  VisibleDivisorFrame (V := V)
    (KaehlerDifferential.D k (ComponentFractionField P)) (Fin m)

abbrev q0
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P)
    (D : frame hm P C) :=
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
  let V := C.W.place.valuation.toSubring
  letI : IsLocalRing V := C.W.place.isDiscrete.toIsLocalRing
  letI : Algebra C.W.coefficientField V :=
      (relativeCoefficientMap C.W.coefficientField C.W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V (ComponentFractionField P) := V.subtype.toAlgebra
  letI : IsScalarTower k V (ComponentFractionField P) := C.groundTower
  D.Q₀ = C.q 0

abbrev q1
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P)
    (D : frame hm P C) :=
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
  let V := C.W.place.valuation.toSubring
  letI : IsLocalRing V := C.W.place.isDiscrete.toIsLocalRing
  letI : Algebra C.W.coefficientField V :=
      (relativeCoefficientMap C.W.coefficientField C.W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V (ComponentFractionField P) := V.subtype.toAlgebra
  letI : IsScalarTower k V (ComponentFractionField P) := C.groundTower
  D.Q₁ = C.q (Fin.succ ⟨0, hm⟩)

abbrev q
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P)
    (D : frame hm P C) :=
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
  let V := C.W.place.valuation.toSubring
  letI : IsLocalRing V := C.W.place.isDiscrete.toIsLocalRing
  letI : Algebra C.W.coefficientField V :=
      (relativeCoefficientMap C.W.coefficientField C.W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V (ComponentFractionField P) := V.subtype.toAlgebra
  letI : IsScalarTower k V (ComponentFractionField P) := C.groundTower
  ∀ j, D.Q j = C.q (Fin.succ j)

abbrev uniformizer
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P)
    (D : frame hm P C) :=
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
  let V := C.W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := C.W.place.isDiscrete
  letI : Algebra C.W.coefficientField V :=
      (relativeCoefficientMap C.W.coefficientField C.W.place).toAlgebra
  D.t = Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer V

end GeneralDivisorialVisibleFrameCoreFieldType

/-- The actual visible differential frame on the normalized column. -/
structure GeneralDivisorialVisibleFrameCore
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P) where
  D : GeneralDivisorialVisibleFrameCoreFieldType.frame hm P C
  D_Q0 : GeneralDivisorialVisibleFrameCoreFieldType.q0 hm P C D
  D_Q1 : GeneralDivisorialVisibleFrameCoreFieldType.q1 hm P C D
  D_Q : GeneralDivisorialVisibleFrameCoreFieldType.q hm P C D
  D_maximalIdeal :
    letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
    let V := C.W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := C.W.place.isDiscrete
    maximalIdeal V = Ideal.span {D.t}
  D_uniformizer : GeneralDivisorialVisibleFrameCoreFieldType.uniformizer hm P C D
  D_w_unit :
    letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
    let V := C.W.place.valuation.toSubring
    letI : IsLocalRing V := C.W.place.isDiscrete.toIsLocalRing
    IsUnit D.w

set_option maxHeartbeats 4000000

/-- The source Kähler image is exactly the coefficient module used by the
visible frame. -/
structure GeneralDivisorialVisibleFrameSourceImage
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (C : GeneralDivisorialVisibleFrameColumn hm P)
    (F : GeneralDivisorialVisibleFrameCore hm P C) where
  D_sourceImage :
    letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
    let V := C.W.place.valuation.toSubring
    letI : IsLocalRing V := C.W.place.isDiscrete.toIsLocalRing
    letI : Algebra C.W.coefficientField V :=
      (relativeCoefficientMap C.W.coefficientField C.W.place).toAlgebra
    letI : Algebra k V := C.groundCoeff.toAlgebra
    letI : Algebra V (ComponentFractionField P) := V.subtype.toAlgebra
    letI : IsScalarTower k V (ComponentFractionField P) := C.groundTower
    F.D.W = LinearMap.range (KaehlerDifferential.map k k V
      (ComponentFractionField P))

set_option maxHeartbeats 4000000

/-- The differential output groups the canonical frame and the actual source
Kähler-image equality. -/
structure GeneralDivisorialVisibleFrameDifferential
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
  (P : PrimeSpectrum (MvPolynomial (Fin m) k))
  (C : GeneralDivisorialVisibleFrameColumn hm P) where
  core : GeneralDivisorialVisibleFrameCore hm P C
  sourceImage : GeneralDivisorialVisibleFrameSourceImage hm P C core

set_option maxHeartbeats 4000000


end

end Stafford38.Geometry.GeneralDivisorialVisibleFrame
