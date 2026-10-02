module
public import Stafford38.Geometry.A0ChartFormalEtale
public import Stafford38.Geometry.AffineComponentCoordinateSplit
public import Stafford38.Geometry.EtaleGenericOpenExtraAwayB
public import Stafford38.Geometry.ProjectiveChartSameFieldOverlap
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap

universe u v w

/-- The original-affine chart map into the common open is the identity on the
ground field: it commutes with `k` mapped through the original affine chart
algebra and `k` mapped through the ground ring `Q`. -/
theorem originalAffineChartToCommonOpen_groundMap
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
    let U := genericOpenExtraAwayB M f e g
    letI : Semiring U := (inferInstance : CommSemiring U).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
    (originalAffineChartToCommonOpen P j hxj hsel M f e).comp
        (algebraMap k (OriginalAffineChartQuotient (k := k) P)) =
      (algebraMap Q U).comp (algebraMap k Q) := by
  dsimp only
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Semiring U := (inferInstance : CommSemiring U).toSemiring
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
  let A₀ := OriginalAffineChartQuotient (k := k) P
  let S₀ := OriginalAffineChartLocalization (k := k) P j
  let T := Localization.Away g
  let overlap : S₀ ≃ₐ[k] T :=
    (originalAffineChartOverlapEquiv P j hxj).trans
      (selectedChartAwayEquivOfQuotientEquiv P j hsel)
  have hz : genericOpenBMap M f e (algebraMap Q B g) = algebraMap Q Cq g :=
    genericOpenBMap_base_eq M f e g
  letI : IsLocalization.Away (algebraMap Q Cq g) U := by
    rw [← hz]
    infer_instance
  let ψ : T →+* U := IsLocalization.Away.map
    (S := T) (Q := U) (algebraMap Q Cq) g
  apply RingHom.ext
  intro c
  change ψ (overlap (algebraMap A₀ S₀ (algebraMap k A₀ c))) =
    algebraMap Q U (algebraMap k Q c)
  rw [← IsScalarTower.algebraMap_apply k A₀ S₀ c, overlap.commutes]
  rw [IsScalarTower.algebraMap_apply k Q T c]
  simp [ψ, IsLocalization.Away.map]
  rfl

end Stafford38.Geometry.SameWitness
