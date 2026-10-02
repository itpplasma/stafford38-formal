import Stafford38.Geometry.SelectedResidueCoefficientLocalization
import Stafford38.Geometry.ProjectiveChartNormalizationCenter
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

noncomputable section
set_option autoImplicit false

namespace Stafford38.Geometry.SelectedResidueCoefficientLocalization

universe u

local instance subringAlgebra {F : Type u} [CommRing F] (R : Subring F) :
    Algebra R F := R.subtype.toAlgebra

/-- The canonical map from an affine chart subalgebra to its integral closure
inside the same component function field. This exposes the unique inclusion
used by the normalized projective-column bridge. -/
noncomputable def chartSubalgebraToIntegralClosure
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    (Q : Subalgebra k F) : Q →+* integralClosure Q.toSubring F := by
  let qToR : Q →+* Q.toSubring :=
    RingHom.codRestrict Q.val.toRingHom Q.toSubring (by
      intro q
      exact q.property)
  exact RingHom.codRestrict Q.val.toRingHom (integralClosure Q.toSubring F) (by
    intro q
    have hval : algebraMap Q.toSubring F (qToR q) = (q : F) := rfl
    change IsIntegral Q.toSubring (q : F)
    rw [← hval]
    exact isIntegral_algebraMap)

@[simp] theorem coe_chartSubalgebraToIntegralClosure
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    (Q : Subalgebra k F) (q : Q) :
    ((chartSubalgebraToIntegralClosure Q q : integralClosure Q.toSubring F) : F) =
      (q : F) := rfl

/-- If the residue map is injective on a coefficient ring `A`, every image in a local ring
of a non-zero-divisor of `A` is a unit. Thus localizing a containing algebra `B` at the
canonical image of `A`'s non-zero-divisors extends its map into the retained local ring. -/
theorem exists_localization_map_of_residue_injective
    {A B T : Type*} [CommRing A] [Nontrivial A] [CommRing B] [CommRing T]
    [IsLocalRing T]
    (j : A →+* B) (fB : B →+* T) (fA : A →+* T)
    (hcomp : fB.comp j = fA)
    (hres : Function.Injective
      ((IsLocalRing.residue T).comp fA)) :
    ∃ f : Localization ((nonZeroDivisors A).map j) →+* T,
      f.comp (algebraMap B (Localization ((nonZeroDivisors A).map j))) = fB := by
  classical
  let S := (nonZeroDivisors A).map j
  have hunit : ∀ s : S, IsUnit (fB s.1) := by
    intro s
    obtain ⟨a, ha, hsa⟩ := Submonoid.mem_map.mp s.property
    rw [← hsa]
    have hfa : fB (j a) = fA a := by
      simpa only [RingHom.comp_apply] using RingHom.congr_fun hcomp a
    rw [hfa]
    apply (IsLocalRing.notMem_maximalIdeal).mp
    intro ham
    have hzero : IsLocalRing.residue T (fA a) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ham
    have hzero' :
        ((IsLocalRing.residue T).comp fA) a = 0 := by
      simpa only [RingHom.comp_apply] using hzero
    have hzero'' :
        ((IsLocalRing.residue T).comp fA) a =
          ((IsLocalRing.residue T).comp fA) 0 := by
      simpa using hzero'
    have ha0 : a = 0 := hres hzero''
    exact (nonZeroDivisors.ne_zero ha) ha0
  let f : Localization S →+* T := IsLocalization.lift (S := Localization S) hunit
  refine ⟨f, ?_⟩
  apply RingHom.ext
  intro b
  exact IsLocalization.lift_eq hunit b

/-- Apply the denominator-extension lemma to the actual integral closure of a chart subalgebra.
The selected coefficient subalgebra maps to the normalization through its inclusion in `Q`,
and the normalization maps to the same valuation ring containing `Q`. -/
theorem exists_chart_normalization_localization_map
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    (Q : Subalgebra k F) (V : ValuationSubring F)
    [IsLocalRing V.toSubring] [Algebra k V.toSubring]
    [Algebra k (IsLocalRing.ResidueField V.toSubring)]
    [IsScalarTower k V.toSubring (IsLocalRing.ResidueField V.toSubring)]
    (hground : ∀ c : k,
      (algebraMap k V.toSubring c : F) = algebraMap k F c)
    (hQV : Q.toSubring ≤ V.toSubring)
    {t : Set (IsLocalRing.ResidueField V.toSubring)}
    (htb : IsTranscendenceBasis k ((↑) : t → IsLocalRing.ResidueField V.toSubring))
    (x : t → Q)
    (hx : ∀ z, IsLocalRing.residue V.toSubring
      ⟨(x z : F), hQV (x z).property⟩ =
        (z : IsLocalRing.ResidueField V.toSubring)) :
    let A : Subalgebra k Q := Algebra.adjoin k (Set.range x)
    let B := integralClosure Q.toSubring F
    ∃ (j : A →+* B) (fB : B →+* V.toSubring)
      (fLoc : Localization ((nonZeroDivisors A).map j) →+* V.toSubring),
      (∀ a : A, ((j a : B) : F) = ((a : A) : Q)) ∧
      (∀ b : B, ((fB b : V.toSubring) : F) = (b : F)) ∧
      fLoc.comp (algebraMap B (Localization ((nonZeroDivisors A).map j))) = fB ∧
        fB.comp j = (chartAlgebraToValuation (k := k) (F := F)
          Q V hground hQV).toRingHom.comp
          (Subalgebra.val A).toRingHom := by
  classical
  let A : Subalgebra k Q := Algebra.adjoin k (Set.range x)
  let B := integralClosure Q.toSubring F
  let qToB : Q →+* B := chartSubalgebraToIntegralClosure Q
  let j : A →+* B := qToB.comp (Subalgebra.val A).toRingHom
  let hBV : B.toSubring ≤ V.toSubring :=
    ProjectiveChartNormalizationCenter.integralClosure_subring_le_valuationSubring
      Q.toSubring V hQV
  let fB : B →+* V.toSubring :=
    RingHom.codRestrict B.val.toRingHom V.toSubring (fun b => hBV b.property)
  let fA : A →+* V.toSubring :=
    (chartAlgebraToValuation (k := k) (F := F) Q V hground hQV).toRingHom.comp
      (Subalgebra.val A).toRingHom
  have hcomp : fB.comp j = fA := by
    ext a
    rfl
  let ψ : A →ₐ[k] IsLocalRing.ResidueField V.toSubring :=
    selectedCoefficientResidueMap Q V hground hQV t x
  have hψ : Function.Injective ψ.toRingHom :=
    (selectedCoefficientResidueMap_injective Q V hQV hground htb x hx).1
  have hresEq : (IsLocalRing.residue V.toSubring).comp fA = ψ.toRingHom := by
    ext a
    rfl
  have hres : Function.Injective
      ((IsLocalRing.residue V.toSubring).comp fA) := by
    rw [hresEq]
    exact hψ
  obtain ⟨fLoc, hLoc⟩ :=
    exists_localization_map_of_residue_injective
      j fB fA hcomp hres
  have hjF : ∀ a : A, ((j a : B) : F) = ((a : A) : Q) := by
    intro a
    rfl
  have hfBF : ∀ b : B, ((fB b : V.toSubring) : F) = (b : F) := by
    intro b
    rfl
  exact ⟨j, fB, fLoc, hjF, hfBF, hLoc, hcomp⟩

end Stafford38.Geometry.SelectedResidueCoefficientLocalization
