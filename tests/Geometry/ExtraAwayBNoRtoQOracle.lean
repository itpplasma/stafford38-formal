import Stafford38.Geometry.EtaleGenericOpenExtraAwayB
import Mathlib.Data.Nat.Prime.Int

set_option autoImplicit false

open Stafford38.Geometry.EtaleGenericOpenTransport
namespace ExtraAwayBNoRtoQOracle

abbrev Q := ℤ
abbrev B := Localization.Away (2 : ℤ)
abbrev R := B

private noncomputable def e : Localization.Away (2 : ℤ) ≃ₐ[ℤ]
    Localization.Away (algebraMap ℤ B (2 : ℤ)) := by
  let hunit : IsUnit (algebraMap ℤ B (2 : ℤ)) :=
    IsLocalization.Away.algebraMap_isUnit (2 : ℤ)
  let eB : B ≃ₐ[B] Localization.Away (algebraMap ℤ B (2 : ℤ)) :=
    IsLocalization.atUnit (R := B)
      (S := Localization.Away (algebraMap ℤ B (2 : ℤ)))
      (x := algebraMap ℤ B (2 : ℤ)) hunit
  exact eB.restrictScalars ℤ

private theorem no_ring_hom : ¬ Nonempty (B →+* ℤ) := by
  rintro ⟨φ⟩
  have hu : IsUnit (φ (algebraMap ℤ B (2 : ℤ))) :=
    IsUnit.map φ (IsLocalization.Away.algebraMap_isUnit (2 : ℤ))
  have hm : φ (algebraMap ℤ B (2 : ℤ)) = 2 := by
    simpa using (map_intCast φ 2)
  rw [hm] at hu
  norm_num [Int.isUnit_iff] at hu

theorem no_algebra : ¬ Nonempty (Algebra B ℤ) := by
  rintro ⟨A⟩
  letI : Algebra B ℤ := A
  exact no_ring_hom ⟨algebraMap B ℤ⟩

private abbrev M : Ideal B := ⊥
private instance : IsDomain B :=
  IsLocalization.Away.isDomain B (by norm_num : (2 : ℤ) ≠ 0)
private instance : M.IsPrime := Ideal.isPrime_bot

theorem actual_B_only_instance :
    Algebra.FormallyEtale B
      (Localization.Away (genericOpenBMap (M := M) (f := (2 : ℤ)) e
        (algebraMap ℤ B (1 : ℤ)))) := by
  letI : Algebra.FormallyEtale B (Localization.AtPrime M) :=
    Algebra.FormallyEtale.of_isLocalization M.primeCompl
  simpa [R, Q, B] using
    (formallyEtale_genericOpenExtraAway_of_pointLocal
      (R := B) (Q := ℤ) (B := B) M (2 : ℤ) e (1 : ℤ))

#check no_algebra
#check actual_B_only_instance
#print axioms no_algebra
#print axioms actual_B_only_instance
end ExtraAwayBNoRtoQOracle
