module
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Dvr

@[expose] public section

/-!
# Normalization and height-one local rings

A finite-type domain over a characteristic-zero field has finite normalization
in its own fraction field. The proof uses Noether normalization to a polynomial
ring, applies Mathlib's integral-closure finiteness there, and restricts scalars
back to the domain.

In a Noetherian domain, a nonzero nonunit has a minimal prime of height one.
For a Noetherian integrally closed domain, localization at a height-one prime
is a discrete valuation ring, without any global dimension restriction.
Contraction along an integral extension gives the height bound used to compare
the normalization center with its affine-chart center.
-/

namespace Stafford38.Geometry.NormalizationHeightOne

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

universe u

/-- Noether's finiteness theorem for the normalization of a finitely generated
domain over a field of characteristic zero, in abstract `IsIntegralClosure`
form. -/
theorem finite_normalization_of_fg_domain
    (k R : Type u) [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R]
    (C : Type u) [CommRing C] [Algebra R C] [Algebra C (FractionRing R)]
    [IsScalarTower R C (FractionRing R)] [IsIntegralClosure C R (FractionRing R)] :
    Module.Finite R C := by
  classical
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  letI : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) R := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) R :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin s) k) R).mpr hinj
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) R := inferInstance
  letI : Algebra (MvPolynomial (Fin s) k) C :=
    ((algebraMap R C).comp (algebraMap (MvPolynomial (Fin s) k) R)).toAlgebra
  haveI hARC : IsScalarTower (MvPolynomial (Fin s) k) R C :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (MvPolynomial (Fin s) k) C (FractionRing R) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k) R (FractionRing R),
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k) R C,
      IsScalarTower.algebraMap_apply R C (FractionRing R)]
  haveI : IsIntegralClosure C (MvPolynomial (Fin s) k) (FractionRing R) := by
    refine ⟨IsIntegralClosure.algebraMap_injective C R (FractionRing R), fun {x} => ?_⟩
    constructor
    · intro hx
      exact IsIntegralClosure.isIntegral_iff.mp
        (IsIntegral.tower_top (R := MvPolynomial (Fin s) k) (A := R) hx)
    · rintro ⟨y, rfl⟩
      exact isIntegral_trans (R := MvPolynomial (Fin s) k) (A := R) _
        (IsIntegralClosure.isIntegral R (FractionRing R) y).algebraMap
  haveI : Module.Finite (MvPolynomial (Fin s) k) C :=
    IsIntegralClosure.finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k))
      (FractionRing R) C
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) R C

/-- A nonzero nonunit of a Noetherian domain has a minimal prime of height
exactly one.  This is the zero divisor of the paper construction. -/
theorem exists_height_one_minimal_prime
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] {x : B}
    (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) :
    ∃ p : Ideal B, p ∈ (Ideal.span {x}).minimalPrimes ∧ p.height = 1 := by
  obtain ⟨p, hp⟩ := (Ideal.span {x}).nonempty_minimalPrimes (by simpa using hxu)
  have := hp.isPrime
  refine ⟨p, hp, le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp) ?_⟩
  have hne : p ≠ ⊥ := fun e ↦
    hx0 (by simpa [e, Ideal.span_singleton_eq_bot] using hp.1.2)
  rw [Order.one_le_iff_ne_zero]
  simpa [Ideal.height_eq_zero_iff_eq_bot] using hne

/-- The localization of a Noetherian integrally closed domain at a height-one
prime is a discrete valuation ring.  No global dimension hypothesis is used, so
this applies on a component of dimension greater than one. -/
theorem isDiscreteValuationRing_localization_of_height_eq_one
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (h : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hpb : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one h
  have : IsLocalRing (Localization.AtPrime p) := IsLocalization.AtPrime.isLocalRing _ p
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ ‹_›
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime p) := IsLocalization.AtPrime.not_isField A hpb _
  have hkd : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff,
      IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), h]
    norm_num
  have h3 : IsIntegrallyClosed (Localization.AtPrime p) ∧
      ∃! P : Ideal (Localization.AtPrime p), P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨‹_›, IsLocalRing.maximalIdeal _,
      ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf, inferInstance⟩, ?_⟩
    rintro P ⟨hPb, hPp⟩
    exact IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hPb)
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime p) hnf).out 4 1).mp h3

/-- Contraction along an integral extension does not lower height. -/
theorem height_le_height_under_of_isIntegral
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
    (P : Ideal A) [P.IsPrime] : P.height ≤ (Ideal.under R P).height := by
  have hs : StrictMono (PrimeSpectrum.comap (algebraMap R A)) := fun x y hxy ↦
    Ideal.IsIntegral.comap_lt_comap (I := x.asIdeal) (J := y.asIdeal) hxy
  have h := Order.height_le_height_apply_of_strictMono _ hs (⟨P, ‹_›⟩ : PrimeSpectrum A)
  rwa [← PrimeSpectrum.height_eq_orderHeight (⟨P, ‹_›⟩ : PrimeSpectrum A),
    ← PrimeSpectrum.height_eq_orderHeight
      (PrimeSpectrum.comap (algebraMap R A) (⟨P, ‹_›⟩ : PrimeSpectrum A))] at h

#print axioms finite_normalization_of_fg_domain
#print axioms exists_height_one_minimal_prime
#print axioms isDiscreteValuationRing_localization_of_height_eq_one
#print axioms height_le_height_under_of_isIntegral

end Stafford38.Geometry.NormalizationHeightOne
