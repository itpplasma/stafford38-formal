import Stafford38.FoundationClosure
import Stafford38.LeftHandedCorollary
import Stafford38.EvolutionaryCorollary
import Stafford38.LocalizationCorollaries

open Stafford38 Stafford38.FixedSource
open Stafford38.WeylIteratedEquivalence

universe u

open Stafford38.LocalizationCorollaries

theorem orePaperConsumer (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (S : Submonoid (WeylAlg k n))
    [OreLocalization.OreSet (oppositeSubmonoid S)] :
    S38 (RightOreLocalization (WeylAlg k n) S) :=
  s38_rightOreLocalization (Stafford38.universalStatement k n)

-- This consumer asks for the advertised exponent, not an existential bound.
theorem exactDegreePaperConsumer (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (d : PresentedWeyl k (n + 1)) (hd : d ≠ 0) :
    ∃ ell R S : PresentedWeyl k (n + 1),
      IsLinearWeylCoordinate k n ell ∧
        1 = d * R + ell ^ bernsteinDegree k d * d * S :=
  Stafford38.universalFixedSourceStatement k n d hd

theorem leftPaperConsumer (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (d : WeylAlg k n) (hd : d ≠ 0) :
    ∃ R S F : WeylAlg k n, 1 = R * d + S * d * F :=
  LeftHandedCorollary.leftHanded_of_universalStatement
    Stafford38.universalStatement k n d hd

-- Coefficients are independent elements of an arbitrary noncommutative ring.
theorem evolutionConsumer {D : Type u} [Ring D]
    (k : Type u) [Field k] [CharZero k] [Algebra k D]
    (x p : D) (hw : p * x = x * p + 1) (r : ℕ) (hr : 0 < r)
    (terms : List (D × ℕ))
    (hx : ∀ t ∈ terms, t.1 * x = x * t.1)
    (hp : ∀ t ∈ terms, t.1 * p = p * t.1) :
    ∃ R S : D, 1 = (p ^ r - Evolution.potentialSum x terms) * R +
      x ^ r * (p ^ r - Evolution.potentialSum x terms) * S :=
  Evolution.evolutionaryCorollary k hw hr terms hx hp rfl

set_option pp.fullNames true in
#print axioms exactDegreePaperConsumer
set_option pp.fullNames true in
#print axioms leftPaperConsumer
set_option pp.fullNames true in
#print axioms evolutionConsumer
set_option pp.fullNames true in
#print axioms orePaperConsumer
set_option pp.fullNames true in
#print axioms Stafford38.Evolution.tensorEvolutionaryCorollary
