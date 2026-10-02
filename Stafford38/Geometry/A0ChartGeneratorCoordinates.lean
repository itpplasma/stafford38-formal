import Stafford38.Geometry.A0ChartFormalEtale

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace Stafford38.Geometry.A0ChartGeneratorCoordinates

open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary

universe u v w

private theorem selectedChartAwayEquiv_base
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q)
    (x : SelectedAffineChartQuotient (k := k) P j) :
    selectedChartAwayEquivOfQuotientEquiv P j hsel
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j) x) =
      algebraMap Q (Localization.Away (hsel (selectedAffineChartDenominator P j)))
        (hsel x) := by
  let R := SelectedAffineChartQuotient (k := k) P j
  let S := SelectedAffineChartLocalization (k := k) P j
  let T := Localization.Away (hsel (selectedAffineChartDenominator P j))
  let M := Submonoid.powers (selectedAffineChartDenominator P j)
  let N := Submonoid.powers (hsel (selectedAffineChartDenominator P j))
  letI : IsLocalization M S := Localization.isLocalization
  letI : IsLocalization.Away
      (hsel.toRingEquiv.toRingHom (selectedAffineChartDenominator P j)) T :=
    Localization.isLocalization
  have hmap : Submonoid.map hsel M = N := by
    simp [M, N, Submonoid.map_powers]
  change IsLocalization.algEquivOfAlgEquiv
      (S := S) (Q := T) (h := hsel) hmap
    (algebraMap R S x) = algebraMap Q T (hsel x)
  exact IsLocalization.algEquivOfAlgEquiv_eq
    (S := S) (Q := T) (h := hsel) hmap x

private theorem selectedChartAwayEquiv_invSelf
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q) :
    selectedChartAwayEquivOfQuotientEquiv P j hsel
      (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) =
      IsLocalization.Away.invSelf (hsel (selectedAffineChartDenominator P j)) := by
  let R := SelectedAffineChartQuotient (k := k) P j
  let S := SelectedAffineChartLocalization (k := k) P j
  let T := Localization.Away (hsel (selectedAffineChartDenominator P j))
  let M := Submonoid.powers (selectedAffineChartDenominator P j)
  let N := Submonoid.powers (hsel (selectedAffineChartDenominator P j))
  letI : IsLocalization M S := Localization.isLocalization
  letI : IsLocalization.Away
      (hsel.toRingEquiv.toRingHom (selectedAffineChartDenominator P j)) T :=
    Localization.isLocalization
  have hmap : Submonoid.map hsel M = N := by
    simp [M, N, Submonoid.map_powers]
  let E := selectedChartAwayEquivOfQuotientEquiv P j hsel
  have hbase := selectedChartAwayEquiv_base P j hsel
    (selectedAffineChartDenominator P j)
  have hprod :
      algebraMap Q T (hsel (selectedAffineChartDenominator P j)) *
          E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) = 1 := by
    calc
      _ = E (algebraMap R S (selectedAffineChartDenominator P j)) *
          E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) := by
            rw [hbase]
      _ = E (algebraMap R S (selectedAffineChartDenominator P j) *
          IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) := by
            rw [← map_mul]
      _ = E 1 := by rw [IsLocalization.Away.mul_invSelf]
      _ = 1 := map_one _
  calc
    E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) =
        1 * E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) := by simp
    _ = (algebraMap Q T (hsel (selectedAffineChartDenominator P j)) *
        IsLocalization.Away.invSelf (hsel (selectedAffineChartDenominator P j))) *
        E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) := by
          rw [IsLocalization.Away.mul_invSelf]
    _ = IsLocalization.Away.invSelf (hsel (selectedAffineChartDenominator P j)) *
        (algebraMap Q T (hsel (selectedAffineChartDenominator P j)) *
          E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j))) := by ac_rfl
    _ = IsLocalization.Away.invSelf (hsel (selectedAffineChartDenominator P j)) * 1 := by
          rw [hprod]
    _ = IsLocalization.Away.invSelf (hsel (selectedAffineChartDenominator P j)) := by simp

/-- The original affine variable in the common open is the selected chart
coordinate divided by the selected chart's distinguished denominator.  This
is the multiplicative identity before any map to the valuation ring or field. -/
theorem originalGenerator_commonOpen_identity
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    {B : Type w} [CommRing B] [Algebra Q B]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j i : Fin m)
    (hij : i ≠ j) (hxj : componentCoordinate P j ≠ 0)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q)
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    algebraMap Cq C
        (algebraMap Q Cq
          (hsel (selectedAffineChartVariableClass P j i hij))) =
      algebraMap Cq C (algebraMap Q Cq g) *
        originalAffineChartToCommonOpen P j hxj hsel M f e
          (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := by
  dsimp
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  let A₀ := OriginalAffineChartQuotient (k := k) P
  let S := OriginalAffineChartLocalization (k := k) P j
  let T := Localization.Away g
  letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  have hz : genericOpenBMap M f e (algebraMap Q B g) = algebraMap Q Cq g :=
    genericOpenBMap_base_eq M f e g
  letI : IsLocalization.Away (algebraMap Q Cq g) C := by
    rw [← hz]
    infer_instance
  let h : S ≃ₐ[k] T :=
    (originalAffineChartOverlapEquiv P j hxj).trans
      (selectedChartAwayEquivOfQuotientEquiv P j hsel)
  let ψ : T →+* C := IsLocalization.Away.map
    (S := T) (Q := C) (algebraMap Q Cq) g
  have hXi :
      originalAffineChartToCommonOpen P j hxj hsel M f e
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) =
      ψ (algebraMap Q T
        (hsel (selectedAffineChartVariableClass P j i hij)) *
        IsLocalization.Away.invSelf g) := by
    change ψ (h (algebraMap A₀ S
      (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)))) = _
    have hov : h (algebraMap A₀ S
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i))) =
      algebraMap Q T
        (hsel (selectedAffineChartVariableClass P j i hij)) *
          IsLocalization.Away.invSelf g := by
      change selectedChartAwayEquivOfQuotientEquiv P j hsel
        ((originalAffineChartOverlapEquiv P j hxj)
          (algebraMap A₀ S
            (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)))) = _
      rw [originalAffineChartOverlapEquiv_Xi P j i hij hxj]
      rw [map_mul, selectedChartAwayEquiv_base, selectedChartAwayEquiv_invSelf]
    rw [hov]
  have hψv :
      ψ (algebraMap Q T
        (hsel (selectedAffineChartVariableClass P j i hij))) =
      algebraMap Cq C (algebraMap Q Cq
        (hsel (selectedAffineChartVariableClass P j i hij))) := by
    simp [ψ, IsLocalization.Away.map, IsLocalization.map_mk']
  have hψg : ψ (algebraMap Q T g) = algebraMap Cq C (algebraMap Q Cq g) := by
    simp [ψ, IsLocalization.Away.map, IsLocalization.map_mk']
  have hmul :
      algebraMap Q T g *
          (algebraMap Q T (hsel (selectedAffineChartVariableClass P j i hij)) *
            IsLocalization.Away.invSelf g) =
        algebraMap Q T (hsel (selectedAffineChartVariableClass P j i hij)) := by
    calc
      _ = (algebraMap Q T g * IsLocalization.Away.invSelf g) *
          algebraMap Q T (hsel (selectedAffineChartVariableClass P j i hij)) := by ac_rfl
      _ = algebraMap Q T (hsel (selectedAffineChartVariableClass P j i hij)) := by
        simp [IsLocalization.Away.mul_invSelf]
  calc
    algebraMap Cq C (algebraMap Q Cq
        (hsel (selectedAffineChartVariableClass P j i hij))) =
      ψ (algebraMap Q T
        (hsel (selectedAffineChartVariableClass P j i hij))) := hψv.symm
    _ = ψ (algebraMap Q T g) *
        ψ (algebraMap Q T
          (hsel (selectedAffineChartVariableClass P j i hij)) *
          IsLocalization.Away.invSelf g) := by
      rw [← map_mul]
      exact congrArg ψ hmul.symm
    _ = algebraMap Cq C (algebraMap Q Cq g) *
        originalAffineChartToCommonOpen P j hxj hsel M f e
          (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := by
      rw [hψg, hXi]

/-- The selected projective coordinate times the original affine generator
is one on the common open. -/
theorem selectedGenerator_commonOpen_product
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    {B : Type w} [CommRing B] [Algebra Q B]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q)
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    algebraMap Cq C (algebraMap Q Cq g) *
      originalAffineChartToCommonOpen P j hxj hsel M f e
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j)) = 1 := by
  dsimp
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  let A₀ := OriginalAffineChartQuotient (k := k) P
  let S₀ := OriginalAffineChartLocalization (k := k) P j
  let T := Localization.Away g
  let E := selectedChartAwayEquivOfQuotientEquiv P j hsel
  letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  have hz : genericOpenBMap M f e (algebraMap Q B g) = algebraMap Q Cq g :=
    genericOpenBMap_base_eq M f e g
  letI : IsLocalization.Away (algebraMap Q Cq g) C := by
    rw [← hz]
    infer_instance
  let ψ : T →+* C := IsLocalization.Away.map
    (S := T) (Q := C) (algebraMap Q Cq) g
  have hprod : algebraMap Q T g *
      E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) = 1 := by
    change algebraMap Q T g *
      selectedChartAwayEquivOfQuotientEquiv P j hsel
        (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j)) = 1
    rw [selectedChartAwayEquiv_invSelf P j hsel]
    rw [IsLocalization.Away.mul_invSelf]
  have hψg : ψ (algebraMap Q T g) = algebraMap Cq C (algebraMap Q Cq g) := by
    simp [ψ, IsLocalization.Away.map]
  have hXj : originalAffineChartToCommonOpen P j hxj hsel M f e
      (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j)) =
      ψ (E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j))) := by
    change ψ (E ((originalAffineChartOverlapEquiv P j hxj)
      (algebraMap A₀ S₀
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j))) )) = _
    rw [originalAffineChartOverlapEquiv_Xj]
  calc
    _ = ψ (algebraMap Q T g) *
        ψ (E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j))) := by
      rw [hψg, hXj]
    _ = ψ (algebraMap Q T g *
        E (IsLocalization.Away.invSelf (selectedAffineChartDenominator P j))) := by
      rw [map_mul]
    _ = 1 := by rw [hprod]; simp

/-- The same selected-coordinate value, when represented from `B`, is its
canonical image through the common open. -/
theorem genericOpenExtraAwayBMap_algebraMap
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (g x : Q) :
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    genericOpenExtraAwayBMap M f e g (algebraMap Q B x) =
      algebraMap Cq C (algebraMap Q Cq x) := by
  dsimp
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  change algebraMap Cq C (genericOpenBMap M f e (algebraMap Q B x)) = _
  rw [genericOpenBMap_base_eq M f e x]

end Stafford38.Geometry.A0ChartGeneratorCoordinates
end
