import Mathlib.RingTheory.DedekindDomain.Dvr

set_option autoImplicit false

namespace Stafford38.Geometry.DVRUniformizerNumerator

open IsLocalRing

universe u

/-- A uniformizer in a DVR localization of a domain has a numerator in the
original prime ideal which remains a generator of the localized maximal ideal.
The denominator is retained to identify the numerator with a unit multiple of
the chosen uniformizer. -/
theorem exists_numerator_of_dvr_localization_of_irreducible
    {B : Type u} [CommRing B] [IsDomain B]
    (P : Ideal B) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (π : Localization.AtPrime P) (hπ : Irreducible π) :
    ∃ a : B, ∃ b : P.primeCompl,
      a ≠ 0 ∧ a ∈ P ∧
      IsLocalization.mk' (Localization.AtPrime P) a b = π ∧
      Ideal.span {algebraMap B (Localization.AtPrime P) a} =
        maximalIdeal (Localization.AtPrime P) := by
  let R := Localization.AtPrime P
  obtain ⟨a, b, hrep⟩ := IsLocalization.exists_mk'_eq P.primeCompl π
  have hmax : maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπmem : π ∈ maximalIdeal R := by
    rw [hmax]
    exact Submodule.mem_span_singleton_self π
  have hbunit : IsUnit (algebraMap B R (b : B)) :=
    IsLocalization.map_units R b
  have hmapa : algebraMap B R a = π * algebraMap B R (b : B) := by
    calc
      algebraMap B R a = IsLocalization.mk' R a b * algebraMap B R (b : B) :=
        (IsLocalization.mk'_spec R a b).symm
      _ = π * algebraMap B R (b : B) := by rw [hrep]
  have haLoc : algebraMap B R a ∈ maximalIdeal R := by
    rw [hmapa]
    exact (maximalIdeal R).mul_mem_right _ hπmem
  have haP : a ∈ P :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R P a).mp haLoc
  have ha0 : a ≠ 0 := by
    intro ha
    have hzero : π = 0 := by
      rw [hrep.symm, ha]
      simp
    exact hπ.ne_zero hzero
  have hspan : Ideal.span {algebraMap B R a} = Ideal.span {π} := by
    rw [hmapa]
    exact Ideal.span_singleton_mul_right_unit hbunit π
  exact ⟨a, b, ha0, haP, hrep, by rw [hspan, hmax.symm]⟩

/-- A uniformizer in a DVR localization of a domain has a numerator in the
 original prime ideal which remains a generator of the localized maximal ideal.
 The denominator is retained to identify the numerator with a unit multiple of
 the chosen uniformizer. -/
theorem exists_numerator_of_dvr_localization
    {B : Type u} [CommRing B] [IsDomain B]
    (P : Ideal B) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)] :
    ∃ π : Localization.AtPrime P, Irreducible π ∧
      ∃ a : B, ∃ b : P.primeCompl,
        a ≠ 0 ∧ a ∈ P ∧
        IsLocalization.mk' (Localization.AtPrime P) a b = π ∧
        Ideal.span {algebraMap B (Localization.AtPrime P) a} =
          maximalIdeal (Localization.AtPrime P) := by
  let R := Localization.AtPrime P
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, b, ha0, haP, hrep, hspan⟩ :=
    exists_numerator_of_dvr_localization_of_irreducible P π hπ
  exact ⟨π, hπ, a, b, ha0, haP, hrep, hspan⟩


end Stafford38.Geometry.DVRUniformizerNumerator
