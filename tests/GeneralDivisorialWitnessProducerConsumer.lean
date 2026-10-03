module
public import Stafford38.Geometry.GeneralDivisorialVisibleFrame

@[expose] public section

set_option autoImplicit false

universe u

open Stafford38.Geometry.GeneralDivisorialVisibleFrame

example {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m) (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k
      (Stafford38.Geometry.AffineComponentCoordinateSplit.componentCoordinate
        P ⟨0, hm⟩)) :
    Nonempty (GeneralDivisorialVisibleFrameWitness hm P) :=
  generalDivisorialVisibleFrameWithResidueAlgebraicity hm P hunit htrans

example {k : Type u} [Field k] [CharZero k] {m : ℕ}
    (hm : 0 < m) (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k
      (Stafford38.Geometry.AffineComponentCoordinateSplit.componentCoordinate
        P ⟨0, hm⟩)) :
    Stafford38.Geometry.ExactVisibleDivisorFrameInterface.HasNormalizedCompatibleVisibleFrame
      P hm :=
  generalDivisorialVisibleFrameExistence hm P hunit htrans

#print axioms generalDivisorialVisibleFrameWithResidueAlgebraicity
#print axioms generalDivisorialVisibleFrameExistence
