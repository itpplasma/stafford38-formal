import Stafford38.Geometry.ProjectiveChartSameFieldOverlap
import Stafford38.Geometry.ChartGenericPointFractionRing
import Stafford38.Geometry.EtaleGenericOpenExtraAwayB
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace Stafford38.Geometry.A0ChartFormalEtale

open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ProjectiveChartCoordinates

universe u v w

/-- If a formally etale algebra already inverts `r`, it is formally etale
as an algebra over the localization that inverts `r`. -/
theorem formallyEtale_away_of_formallyEtale_base
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallyEtale R S] (r : R)
    (hr : IsUnit (algebraMap R S r)) :
    let T := Localization.Away r
    letI : Algebra T S :=
      (IsLocalization.Away.lift (g := algebraMap R S) r hr).toAlgebra
    Algebra.FormallyEtale T S := by
  let T := Localization.Away r
  let φ : T →+* S := IsLocalization.Away.lift (g := algebraMap R S) r hr
  letI : Algebra T S := φ.toAlgebra
  have hcomp : (algebraMap T S).comp (algebraMap R T) = algebraMap R S := by
    exact IsLocalization.Away.lift_comp (g := algebraMap R S) r hr
  letI : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq (fun x => (DFunLike.congr_fun hcomp x).symm)
  letI : IsLocalization
      (Submonoid.map (algebraMap R S) (Submonoid.powers r)) S := by
    apply IsLocalization.of_le_isUnit
    rintro z ⟨x, hx, rfl⟩
    rcases (Submonoid.mem_powers_iff _ _).mp hx with ⟨n, hn⟩
    rw [← hn, map_pow]
    exact hr.pow n
  exact Algebra.FormallyEtale.localization_map
    (R := R) (S := S) (Rₘ := T) (Sₘ := S) (Submonoid.powers r)


/-- A quotient-chart equivalence carries its chart-denominator localization
with it. -/
noncomputable def selectedChartAwayEquivOfQuotientEquiv
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q) :
    SelectedAffineChartLocalization (k := k) P j ≃ₐ[k]
      Localization.Away (hsel (selectedAffineChartDenominator P j)) := by
  let R := SelectedAffineChartQuotient (k := k) P j
  let S := SelectedAffineChartLocalization (k := k) P j
  let T := Localization.Away (hsel (selectedAffineChartDenominator P j))
  let M := Submonoid.powers (selectedAffineChartDenominator P j)
  let N := Submonoid.powers (hsel (selectedAffineChartDenominator P j))
  letI : IsLocalization M S := inferInstance
  letI : IsLocalization N T := inferInstance
  have hmap : Submonoid.map hsel.toRingHom M = N := by
    simp [M, N, Submonoid.map_powers]
  exact IsLocalization.algEquivOfAlgEquiv
    (A := k) (R := R) (M := M) (S := S) (P := Q) (T := N) (Q := T)
    hsel hmap

/-- The precise Q-algebra structure on the common open is the one induced by
its canonical localization over Q. -/
theorem formallyEtale_genericOpenExtraAway_overQ
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (g : Q) :
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Algebra Q Cq :=
      Algebra.compHom Cq (algebraMap Q (Localization.Away f))
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    Algebra.FormallyEtale Q C := by
  dsimp
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
  letI : Algebra (Localization.Away f) Cq := inferInstance
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  letI : SMul Q Cq := (inferInstance : Algebra Q Cq).toSMul
  letI : SMul Cq C := (inferInstance : Algebra Cq C).toSMul
  letI : SMul Q C := (Algebra.compHom C (algebraMap Q Cq)).toSMul
  letI : IsScalarTower Q Cq C :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra.FormallyEtale Q Cq := formallyEtale_genericOpenRing M f e
  letI : Algebra.FormallyEtale Cq C :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (genericOpenBMap M f e (algebraMap Q B g)))
  exact Algebra.FormallyEtale.comp Q Cq C


/-- The finite-birational map on B restricts to the canonical Q map on its
localized generic chart. -/
theorem genericOpenBMap_base_eq
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (q : Q) :
    genericOpenBMap M f e (algebraMap Q B q) =
      algebraMap Q (genericOpenRing M f e) q := by
  let Cq := genericOpenRing M f e
  let Bf := Localization.Away (algebraMap Q B f)
  letI : Algebra Q Cq := inferInstance
  change algebraMap (Localization.Away f) Cq
      (e.symm (algebraMap B Bf (algebraMap Q B q))) = _
  rw [← IsScalarTower.algebraMap_apply Q B Bf]
  rw [e.symm.commutes]
  rfl

/-- The canonical Q-algebra map into the common generic open agrees with the
map induced from the integral chart algebra. -/
theorem genericOpenExtraAway_base_map_agrees
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (g : Q) :
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    (genericOpenExtraAwayBMap M f e g).comp (algebraMap Q B) =
      algebraMap Q C := by
  dsimp
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  ext q
  change algebraMap Cq C (genericOpenBMap M f e (algebraMap Q B q)) = _
  rw [genericOpenBMap_base_eq M f e q]
  rfl

/-- The original affine chart localization maps into the selected projective
chart localization and then into the actual common open. -/
noncomputable def originalAffineChartLocalizationToCommonOpen
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    {B : Type w} [CommRing B] [Algebra Q B]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q)
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    let C := genericOpenExtraAwayB M f e (hsel (selectedAffineChartDenominator P j))
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    OriginalAffineChartLocalization (k := k) P j →+* C := by
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  letI : Algebra (Localization.Away f) Cq := inferInstance
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  let z := genericOpenBMap M f e (algebraMap Q B g)
  have hz : z = algebraMap Q Cq g := genericOpenBMap_base_eq M f e g
  letI : IsLocalization.Away (algebraMap Q Cq g) C := by
    rw [← hz]
    infer_instance
  let h : OriginalAffineChartLocalization (k := k) P j ≃ₐ[k]
      Localization.Away g :=
    (originalAffineChartOverlapEquiv P j hxj).trans
      (selectedChartAwayEquivOfQuotientEquiv P j hsel)
  let ψraw : Localization.Away g →+* C :=
    IsLocalization.Away.map (S := Localization.Away g) (Q := C)
      (algebraMap Q Cq) g
  let ψ : Localization.Away g →+* C :=
    RingHom.copy ψraw (fun x => ψraw x) rfl
  exact ψ.comp h.toAlgHom.toRingHom

/-- The original affine quotient maps to the same common open through its
selected chart localization. -/
noncomputable def originalAffineChartToCommonOpen
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    {B : Type w} [CommRing B] [Algebra Q B]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q)
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    let C := genericOpenExtraAwayB M f e (hsel (selectedAffineChartDenominator P j))
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    OriginalAffineChartQuotient (k := k) P →+* C :=
  (originalAffineChartLocalizationToCommonOpen P j hxj hsel M f e).comp
    (algebraMap (OriginalAffineChartQuotient (k := k) P)
      (OriginalAffineChartLocalization P j))

/-- The chart map above is formally etale: first localize the original chart,
then use the checked affine-overlap equivalence, and finally localize the
common generic open at the image of the selected denominator. -/
theorem formallyEtale_originalAffineChartToCommonOpen
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
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    let A₀ := OriginalAffineChartQuotient (k := k) P
    let S := OriginalAffineChartLocalization (k := k) P j
    letI : Algebra A₀ C :=
      (originalAffineChartToCommonOpen P j hxj hsel M f e).toAlgebra
    Algebra.FormallyEtale A₀ C := by
  dsimp
  let g := hsel (selectedAffineChartDenominator P j)
  let C := genericOpenExtraAwayB M f e g
  letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
  let A₀ := OriginalAffineChartQuotient (k := k) P
  let S := OriginalAffineChartLocalization (k := k) P j
  let T := Localization.Away g
  let Cq := genericOpenRing M f e
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C :=
    Algebra.compHom C (algebraMap Q Cq)
  have hg : IsUnit (algebraMap Q C g) := by
    change IsUnit (algebraMap Cq C (algebraMap Q Cq g))
    rw [← genericOpenBMap_base_eq M f e g]
    exact IsLocalization.Away.algebraMap_isUnit
      (genericOpenBMap M f e (algebraMap Q B g))
  letI : Algebra.FormallyEtale Q C :=
    formallyEtale_genericOpenExtraAway_overQ M f e g
  let φ : T →+* C := IsLocalization.Away.lift
    (g := algebraMap Q C) g hg
  letI : Algebra T C := φ.toAlgebra
  letI : SMul Q T := (inferInstance : Algebra Q T).toSMul
  letI : SMul T C := (inferInstance : Algebra T C).toSMul
  letI : SMul Q C := (Algebra.compHom C (algebraMap Q Cq)).toSMul
  have hcomp : (algebraMap T C).comp (algebraMap Q T) = algebraMap Q C := by
    exact IsLocalization.Away.lift_comp (g := algebraMap Q C) g hg
  letI : IsScalarTower Q T C :=
    IsScalarTower.of_algebraMap_eq (fun q => (DFunLike.congr_fun hcomp q).symm)
  letI : Algebra.FormallyEtale T C :=
    formallyEtale_away_of_formallyEtale_base (R := Q) (S := C) g hg
  let h : S ≃ₐ[k] T :=
    (originalAffineChartOverlapEquiv P j hxj).trans
      (selectedChartAwayEquivOfQuotientEquiv P j hsel)
  letI : Algebra S T := h.toAlgHom.toAlgebra
  let hS : S ≃ₐ[S] T := { h with commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_equiv hS
  letI : Algebra S C := Algebra.compHom C (algebraMap S T)
  letI : SMul T C := (inferInstance : Algebra T C).toSMul
  letI : SMul S C := (Algebra.compHom C (algebraMap S T)).toSMul
  letI : IsScalarTower S T C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hSC : Algebra.FormallyEtale S C :=
    Algebra.FormallyEtale.comp S T C
  letI : Algebra A₀ S := inferInstance
  letI : Algebra A₀ C :=
    (originalAffineChartToCommonOpen P j hxj hsel M f e).toAlgebra
  letI : SMul A₀ S := (inferInstance : Algebra A₀ S).toSMul
  letI : SMul S C := (inferInstance : Algebra S C).toSMul
  letI : SMul A₀ C := (inferInstance : Algebra A₀ C).toSMul
  letI : IsScalarTower A₀ S C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra.FormallyEtale A₀ S :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (originalAffineChartDenominator P j))
  exact Algebra.FormallyEtale.comp A₀ S C

end Stafford38.Geometry.A0ChartFormalEtale
end
