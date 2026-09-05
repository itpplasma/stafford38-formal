import Stafford38.LocalizedDifferentialCorollaries

open Stafford38.DifferentialOperators
open Stafford38.LocalizedDifferentialCorollaries

universe u
variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

theorem actualLocalizedOperatorConsumer
    (S : Submonoid (MvPolynomial (Fin n) k))
    (B : Type u) [CommRing B] [Algebra (MvPolynomial (Fin n) k) B]
    [Algebra k B] [IsScalarTower k (MvPolynomial (Fin n) k) B]
    [IsLocalization S B]
    (q : algebra (k := k) (R := B)) (hq : q ≠ 0) :
    ∃ F R T : algebra (k := k) (R := B), 1 = q * R + F * q * T :=
  s38_unconditional_localized_differential S B q hq

theorem actualPrincipalOpenConsumer
    (f : MvPolynomial (Fin n) k)
    (B : Type u) [CommRing B] [Algebra (MvPolynomial (Fin n) k) B]
    [Algebra k B] [IsScalarTower k (MvPolynomial (Fin n) k) B]
    [IsLocalization (Submonoid.powers f) B]
    (q : algebra (k := k) (R := B)) (hq : q ≠ 0) :
    ∃ F R T : algebra (k := k) (R := B), 1 = q * R + F * q * T :=
  s38_principal_open_differential f B q hq

theorem actualPartialLaurentConsumer
    (J : Finset (Fin n))
    (B : Type u) [CommRing B] [Algebra (MvPolynomial (Fin n) k) B]
    [Algebra k B] [IsScalarTower k (MvPolynomial (Fin n) k) B]
    [IsLocalization (Submonoid.powers
      (J.prod (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) k)))) B]
    (q : algebra (k := k) (R := B)) (hq : q ≠ 0) :
    ∃ F R T : algebra (k := k) (R := B), 1 = q * R + F * q * T :=
  s38_partial_laurent_differential J B q hq

theorem actualRationalOperatorConsumer
    (B : Type u) [CommRing B] [Algebra (MvPolynomial (Fin n) k) B]
    [Algebra k B] [IsScalarTower k (MvPolynomial (Fin n) k) B]
    [IsFractionRing (MvPolynomial (Fin n) k) B]
    (q : algebra (k := k) (R := B)) (hq : q ≠ 0) :
    ∃ F R T : algebra (k := k) (R := B), 1 = q * R + F * q * T :=
  s38_fraction_ring_differential (k := k) (n := n) B q hq

#print axioms actualLocalizedOperatorConsumer
#print axioms actualPrincipalOpenConsumer
#print axioms actualPartialLaurentConsumer
#print axioms actualRationalOperatorConsumer
