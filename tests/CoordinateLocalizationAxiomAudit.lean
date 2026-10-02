module
public import Stafford38.Geometry.ProjectiveCoefficientLocalization
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

set_option autoImplicit false

open Stafford38.Geometry.ProjectiveCoefficientLocalization

universe u v

section Generic

variable {k : Type u} [CommRing k] (d : ℕ)
variable {E : Type v} [CommRing E] [Algebra (Coeff k d) E] [Algebra k E]
  [IsScalarTower k (Coeff k d) E]
  [IsLocalization (nonZeroDivisors (Coeff k d)) E]

example : coordinateMap (k := k) d (MvPolynomial.X (0 : Fin (d + 1))) =
    (Polynomial.X : Polynomial E) := coordinateMap_zero (k := k) d

example (i : Fin d) : coordinateMap (k := k) d (MvPolynomial.X i.succ) =
    Polynomial.C (algebraMap (Coeff k d) E (MvPolynomial.X i)) :=
  coordinateMap_succ (k := k) d i

example :
    letI : Algebra (Source k d) (Polynomial E) :=
      (coordinateMap (k := k) d).toRingHom.toAlgebra
    IsLocalization (coordinateDenominators (k := k) d) (Polynomial E) :=
  coordinateMap_isLocalization (k := k) d

example :
    letI : Algebra (Source k d) (Polynomial E) :=
      (coordinateMap (k := k) d).toRingHom.toAlgebra
    Algebra.FormallyEtale (Source k d) (Polynomial E) :=
  coordinateMap_formallyEtale (k := k) d

#print axioms coordinateMap_zero
#print axioms coordinateMap_succ
#print axioms coordinateMap_isLocalization
#print axioms coordinateMap_formallyEtale
#print axioms fractionCoordinateMap_isLocalization
#print axioms fractionCoordinateMap_formallyEtale

end Generic

section ActualFractionField

variable {k : Type u} [Field k] (d : ℕ)

abbrev A := Coeff k d
abbrev E := FractionRing (A (k := k) d)

#synth IsDomain (A (k := k) d)
#synth Field (E (k := k) d)
#synth Algebra (A (k := k) d) (E (k := k) d)
#synth Algebra k (E (k := k) d)
#synth IsScalarTower k (A (k := k) d) (E (k := k) d)
#synth IsLocalization (nonZeroDivisors (A (k := k) d)) (E (k := k) d)

example : coordinateMap (k := k) d (MvPolynomial.X (0 : Fin (d + 1))) =
    (Polynomial.X : Polynomial (E (k := k) d)) := coordinateMap_zero (k := k) d

example (i : Fin d) : coordinateMap (k := k) d (MvPolynomial.X i.succ) =
    Polynomial.C (algebraMap (A (k := k) d) (E (k := k) d) (MvPolynomial.X i)) :=
  coordinateMap_succ (k := k) d i

example :
    letI : Algebra (Source k d) (Polynomial (E (k := k) d)) :=
      (coordinateMap (k := k) d).toRingHom.toAlgebra
    IsLocalization (coordinateDenominators (k := k) d) (Polynomial (E (k := k) d)) :=
  fractionCoordinateMap_isLocalization (k := k) d

example :
    letI : Algebra (Source k d) (Polynomial (E (k := k) d)) :=
      (coordinateMap (k := k) d).toRingHom.toAlgebra
    Algebra.FormallyEtale (Source k d) (Polynomial (E (k := k) d)) :=
  fractionCoordinateMap_formallyEtale (k := k) d

end ActualFractionField
