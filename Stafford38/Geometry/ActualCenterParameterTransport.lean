module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace Stafford38.Geometry.ActualCenterParameterTransport

universe u

/-- The induced equivalence of prime localizations for a ring equivalence and
the corresponding comapped prime. -/
noncomputable def atPrimeEquiv
    {B C : Type u} [CommRing B] [CommRing C]
    (e : B ≃+* C) (P : Ideal B) (Q : Ideal C) [P.IsPrime] [Q.IsPrime]
    (hP : P = Q.comap e) : Localization.AtPrime P ≃+* Localization.AtPrime Q := by
  have hcomplement : P.primeCompl.map e = Q.primeCompl := by
    simpa only [hP] using e.map_primeCompl_comap_eq Q
  exact IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P)
    (Localization.AtPrime Q) e hcomplement

@[simp] theorem atPrimeEquiv_algebraMap
    {B C : Type u} [CommRing B] [CommRing C]
    (e : B ≃+* C) (P : Ideal B) (Q : Ideal C) [P.IsPrime] [Q.IsPrime]
    (hP : P = Q.comap e) (b : B) :
    atPrimeEquiv e P Q hP (algebraMap B (Localization.AtPrime P) b) =
      algebraMap C (Localization.AtPrime Q) (e b) := by
  have hloc : P.primeCompl ≤ Submonoid.comap (e : B →+* C) Q.primeCompl := by
    intro x hx
    change x ∉ P at hx
    change e x ∉ Q
    intro hxQ
    apply hx
    rw [hP]
    exact hxQ
  change (IsLocalization.map (Localization.AtPrime Q) (e : B →+* C) hloc)
    (algebraMap B (Localization.AtPrime P) b) = _
  exact IsLocalization.map_eq _ _

/-- A principal maximal-ideal generator transports across the induced
localization equivalence. -/
theorem span_transport_across_ring_equiv
    {B C : Type u} [CommRing B] [CommRing C]
    (e : B ≃+* C) (P : Ideal B) (Q : Ideal C) [P.IsPrime] [Q.IsPrime]
    (hP : P = Q.comap e)
    (s : C)
    (hs : Ideal.span {algebraMap C (Localization.AtPrime Q) s} =
      maximalIdeal (Localization.AtPrime Q)) :
    Ideal.span {algebraMap B (Localization.AtPrime P) (e.symm s)} =
      maximalIdeal (Localization.AtPrime P) := by
  let eLoc := atPrimeEquiv e P Q hP
  have heval' : eLoc.toRingHom (algebraMap B (Localization.AtPrime P) (e.symm s)) =
      algebraMap C (Localization.AtPrime Q) s := by
    simpa [eLoc] using atPrimeEquiv_algebraMap e P Q hP (e.symm s)
  have hspanMap : (Ideal.span {algebraMap B (Localization.AtPrime P) (e.symm s)}).map
      eLoc.toRingHom = (maximalIdeal (Localization.AtPrime P)).map eLoc.toRingHom := by
    rw [Ideal.map_span]
    rw [IsLocalRing.map_maximalIdeal_of_surjective eLoc.toRingHom eLoc.surjective]
    simpa only [Set.image_singleton, heval'] using hs
  have hmapInjective : Function.Injective (Ideal.map eLoc.toRingHom) := by
    intro I J h
    have h' := congrArg (Ideal.map eLoc.symm.toRingHom) h
    simpa using h'
  exact hmapInjective hspanMap

/-- Transport both order factorizations and the parameter selected on the
normalization subring to the integral-closure algebra carrier. The image
units are carried by the same induced local equivalence. -/
theorem transport_parameter_and_two_orders
    {B C : Type u} [CommRing B] [CommRing C]
    (e : B ≃+* C) (P : Ideal B) (Q : Ideal C) [P.IsPrime] [Q.IsPrime]
    (hP : P = Q.comap e)
    (s : C) (hs0 : s ≠ 0) (hsP : s ∈ Q)
    {q₀ q₁ : B} {n₀ n₁ : ℕ} {u₀ u₁ : Localization.AtPrime Q}
    (hspan : Ideal.span {algebraMap C (Localization.AtPrime Q) s} =
      maximalIdeal (Localization.AtPrime Q))
    (h₀ : algebraMap C (Localization.AtPrime Q) (e q₀) =
      (algebraMap C (Localization.AtPrime Q) s) ^ n₀ * u₀)
    (h₁ : algebraMap C (Localization.AtPrime Q) (e q₁) =
      (algebraMap C (Localization.AtPrime Q) s) ^ n₁ * u₁)
    (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁) :
    let sB := e.symm s
    ∃ u₀B u₁B : Localization.AtPrime P,
      sB ≠ 0 ∧ sB ∈ P ∧
      Ideal.span {algebraMap B (Localization.AtPrime P) sB} =
        maximalIdeal (Localization.AtPrime P) ∧
      IsUnit u₀B ∧ IsUnit u₁B ∧
      algebraMap B (Localization.AtPrime P) q₀ =
        (algebraMap B (Localization.AtPrime P) sB) ^ n₀ * u₀B ∧
      algebraMap B (Localization.AtPrime P) q₁ =
        (algebraMap B (Localization.AtPrime P) sB) ^ n₁ * u₁B := by
  classical
  dsimp only
  let eLoc := atPrimeEquiv e P Q hP
  let sB := e.symm s
  let u₀B := eLoc.symm u₀
  let u₁B := eLoc.symm u₁
  have hsB0 : sB ≠ 0 := by
    intro h
    apply hs0
    exact e.symm.injective (by simpa [sB] using h)
  have hsBP : sB ∈ P := by
    rw [hP]
    change e sB ∈ Q
    simpa [sB] using hsP
  have hspanB := span_transport_across_ring_equiv e P Q hP s hspan
  have hu₀B : IsUnit u₀B := IsUnit.map eLoc.symm.toMonoidHom hu₀
  have hu₁B : IsUnit u₁B := IsUnit.map eLoc.symm.toMonoidHom hu₁
  have h₀B : algebraMap B (Localization.AtPrime P) q₀ =
      (algebraMap B (Localization.AtPrime P) sB) ^ n₀ * u₀B := by
    apply eLoc.injective
    rw [map_mul, map_pow]
    simp [eLoc, u₀B, sB, atPrimeEquiv_algebraMap, h₀]
  have h₁B : algebraMap B (Localization.AtPrime P) q₁ =
      (algebraMap B (Localization.AtPrime P) sB) ^ n₁ * u₁B := by
    apply eLoc.injective
    rw [map_mul, map_pow]
    simp [eLoc, u₁B, sB, atPrimeEquiv_algebraMap, h₁]
  exact ⟨u₀B, u₁B, hsB0, hsBP, hspanB, hu₀B, hu₁B, h₀B, h₁B⟩

end Stafford38.Geometry.ActualCenterParameterTransport
