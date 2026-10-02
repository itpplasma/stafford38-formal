import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.PaperUnitPowerFactorization

private theorem exists_unit_factorization_atPrime
    {B : Type*} [CommRing B] [IsDomain B]
    (P : Ideal B) [P.IsPrime] (s q : B) (e : ℕ)
    (u : Localization.AtPrime P) (hu : IsUnit u)
    (hq : algebraMap B (Localization.AtPrime P) q =
      (algebraMap B (Localization.AtPrime P) s) ^ e * u) :
    ∃ d n : B, d ∉ P ∧ n ∉ P ∧ q * d = s ^ e * n := by
  let V := Localization.AtPrime P
  obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (M := P.primeCompl) u
  have hrepr : u * algebraMap B V (d : B) = algebraMap B V n := hd
  have hdunit : IsUnit (algebraMap B V (d : B)) := IsLocalization.map_units V d
  have hnunit : IsUnit (algebraMap B V n) := by
    rw [← hrepr]
    exact hu.mul hdunit
  have hdnot : (d : B) ∉ P := d.2
  have hnnot : n ∉ P := by
    have hnmem : n ∈ P.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff V P n).mp hnunit
    exact hnmem
  have hloc : algebraMap B V (q * d) = algebraMap B V (s ^ e * n) := by
    calc
      algebraMap B V (q * (d : B)) = algebraMap B V q * algebraMap B V (d : B) := map_mul _ _ _
      _ = ((algebraMap B V s) ^ e * u) * algebraMap B V (d : B) := by rw [hq]
      _ = (algebraMap B V s) ^ e * algebraMap B V n := by rw [mul_assoc, hrepr]
      _ = algebraMap B V (s ^ e * n) := by simp [map_mul, map_pow]
  have hinj : Function.Injective (algebraMap B V) :=
    IsLocalization.injective V P.primeCompl_le_nonZeroDivisors
  refine ⟨d, n, hdnot, hnnot, ?_⟩
  exact hinj hloc

/-- A unit-power factorization at `B_P` can be cleared to elements outside `P`.
After multiplying the four numerator/denominator elements, one principal open
simultaneously makes both residual factors units while preserving the original
`B`-coordinates. -/
theorem exists_common_away_unit_power_factorizations
    {B : Type*} [CommRing B] [IsDomain B]
    (P : Ideal B) [hp : P.IsPrime] (s q₀ q₁ : B) (a b : ℕ)
    (u₀ u₁ : Localization.AtPrime P)
    (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁)
    (h₀ : algebraMap B (Localization.AtPrime P) q₀ =
      (algebraMap B (Localization.AtPrime P) s) ^ a * u₀)
    (h₁ : algebraMap B (Localization.AtPrime P) q₁ =
      (algebraMap B (Localization.AtPrime P) s) ^ b * u₁) :
    ∃ d₀ n₀ d₁ n₁ f : B,
      d₀ ∉ P ∧ n₀ ∉ P ∧ d₁ ∉ P ∧ n₁ ∉ P ∧ f ∉ P ∧
      q₀ * d₀ = s ^ a * n₀ ∧ q₁ * d₁ = s ^ b * n₁ ∧
      ∃ v₀ v₁ : Localization.Away f,
        IsUnit v₀ ∧ IsUnit v₁ ∧
        algebraMap B (Localization.Away f) q₀ =
          (algebraMap B (Localization.Away f) s) ^ a * v₀ ∧
        algebraMap B (Localization.Away f) q₁ =
          (algebraMap B (Localization.Away f) s) ^ b * v₁ := by
  obtain ⟨d₀, n₀, hd₀, hn₀, hq₀⟩ :=
    exists_unit_factorization_atPrime P s q₀ a u₀ hu₀ h₀
  obtain ⟨d₁, n₁, hd₁, hn₁, hq₁⟩ :=
    exists_unit_factorization_atPrime P s q₁ b u₁ hu₁ h₁
  let f : B := (d₀ * n₀) * (d₁ * n₁)
  have hf : f ∉ P := by
    dsimp [f]
    exact hp.mul_notMem (hp.mul_notMem hd₀ hn₀)
      (hp.mul_notMem hd₁ hn₁)
  let W := Localization.Away f
  have hfunit : IsUnit (algebraMap B W f) :=
    IsLocalization.Away.algebraMap_isUnit f
  have hd₀dvd : d₀ ∣ f := ⟨n₀ * (d₁ * n₁), by dsimp [f]; ac_rfl⟩
  have hn₀dvd : n₀ ∣ f := ⟨d₀ * (d₁ * n₁), by dsimp [f]; ac_rfl⟩
  have hd₁dvd : d₁ ∣ f := ⟨d₀ * n₀ * n₁, by dsimp [f]; ac_rfl⟩
  have hn₁dvd : n₁ ∣ f := ⟨d₀ * n₀ * d₁, by dsimp [f]; ac_rfl⟩
  have hd₀unit : IsUnit (algebraMap B W d₀) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap B W) hd₀dvd) hfunit
  have hn₀unit : IsUnit (algebraMap B W n₀) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap B W) hn₀dvd) hfunit
  have hd₁unit : IsUnit (algebraMap B W d₁) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap B W) hd₁dvd) hfunit
  have hn₁unit : IsUnit (algebraMap B W n₁) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap B W) hn₁dvd) hfunit
  let v₀ : W := ↑(hn₀unit.unit * hd₀unit.unit⁻¹)
  let v₁ : W := ↑(hn₁unit.unit * hd₁unit.unit⁻¹)
  have hv₀ : IsUnit v₀ := by
    exact (hn₀unit.unit * hd₀unit.unit⁻¹).isUnit
  have hv₁ : IsUnit v₁ := by
    exact (hn₁unit.unit * hd₁unit.unit⁻¹).isUnit
  have hq₀W : algebraMap B W q₀ * algebraMap B W d₀ =
      (algebraMap B W s) ^ a * algebraMap B W n₀ := by
    simpa [map_mul, map_pow] using congrArg (algebraMap B W) hq₀
  have hq₁W : algebraMap B W q₁ * algebraMap B W d₁ =
      (algebraMap B W s) ^ b * algebraMap B W n₁ := by
    simpa [map_mul, map_pow] using congrArg (algebraMap B W) hq₁
  have hunitratio₀ : algebraMap B W n₀ * ↑(hd₀unit.unit⁻¹) =
      ↑(hn₀unit.unit * hd₀unit.unit⁻¹) := by
    calc
      algebraMap B W n₀ * ↑(hd₀unit.unit⁻¹) =
          ↑hn₀unit.unit * ↑(hd₀unit.unit⁻¹) :=
        congrArg (fun z : W => z * ↑(hd₀unit.unit⁻¹)) hn₀unit.unit_spec.symm
      _ = ↑(hn₀unit.unit * hd₀unit.unit⁻¹) := by rw [Units.val_mul]
  have hunitratio₁ : algebraMap B W n₁ * ↑(hd₁unit.unit⁻¹) =
      ↑(hn₁unit.unit * hd₁unit.unit⁻¹) := by
    calc
      algebraMap B W n₁ * ↑(hd₁unit.unit⁻¹) =
          ↑hn₁unit.unit * ↑(hd₁unit.unit⁻¹) :=
        congrArg (fun z : W => z * ↑(hd₁unit.unit⁻¹)) hn₁unit.unit_spec.symm
      _ = ↑(hn₁unit.unit * hd₁unit.unit⁻¹) := by rw [Units.val_mul]
  have hfactor₀ : algebraMap B W q₀ = (algebraMap B W s) ^ a * v₀ := by
    dsimp [v₀]
    calc
      algebraMap B W q₀ = algebraMap B W q₀ *
          (algebraMap B W d₀ * ↑(hd₀unit.unit⁻¹)) := by
        rw [hd₀unit.mul_val_inv, mul_one]
      _ = (algebraMap B W q₀ * algebraMap B W d₀) *
          ↑(hd₀unit.unit⁻¹) := by rw [← mul_assoc]
      _ = ((algebraMap B W s) ^ a * algebraMap B W n₀) *
          ↑(hd₀unit.unit⁻¹) := by rw [hq₀W]
      _ = (algebraMap B W s) ^ a *
          (algebraMap B W n₀ * ↑(hd₀unit.unit⁻¹)) := by rw [mul_assoc]
      _ = (algebraMap B W s) ^ a * ↑(hn₀unit.unit * hd₀unit.unit⁻¹) := by
          rw [hunitratio₀]
  have hfactor₁ : algebraMap B W q₁ = (algebraMap B W s) ^ b * v₁ := by
    dsimp [v₁]
    calc
      algebraMap B W q₁ = algebraMap B W q₁ *
          (algebraMap B W d₁ * ↑(hd₁unit.unit⁻¹)) := by
        rw [hd₁unit.mul_val_inv, mul_one]
      _ = (algebraMap B W q₁ * algebraMap B W d₁) *
          ↑(hd₁unit.unit⁻¹) := by rw [← mul_assoc]
      _ = ((algebraMap B W s) ^ b * algebraMap B W n₁) *
          ↑(hd₁unit.unit⁻¹) := by rw [hq₁W]
      _ = (algebraMap B W s) ^ b *
          (algebraMap B W n₁ * ↑(hd₁unit.unit⁻¹)) := by rw [mul_assoc]
      _ = (algebraMap B W s) ^ b * ↑(hn₁unit.unit * hd₁unit.unit⁻¹) := by
          rw [hunitratio₁]
  exact ⟨d₀, n₀, d₁, n₁, f, hd₀, hn₀, hd₁, hn₁, hf, hq₀, hq₁,
    v₀, v₁, hv₀, hv₁, hfactor₀, hfactor₁⟩


end Stafford38.Geometry.PaperUnitPowerFactorization
