module
public import Stafford38.Geometry.ComponentProjectiveChartFactorization
public import Stafford38.Geometry.LocalizedProjectiveChartTransition
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

@[expose] public section

/-!
# Standard projective charts for component equations

For each selected homogeneous coordinate `X chart`, this module identifies
the matching affine dehomogenized equation quotient with the quotient of the
standard homogeneous localization on `Proj`. The chart is handled by a proved
coordinate permutation from the zeroth-chart presentation. It also records
equality of the two affine equation ideals on the chart overlap; this module
does not identify or glue the integral closures of the affine chart rings.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace Stafford38.Geometry.ProjectiveChartNormalizationBridge

noncomputable section

universe u

variable {k : Type u} [Field k] {m : ℕ}

local instance : GradedRing (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k) :=
  MvPolynomial.gradedAlgebra

abbrev A (k : Type u) [Field k] (m : ℕ) := MvPolynomial (Fin (m + 1)) k
abbrev Xzero (k : Type u) [Field k] (m : ℕ) : A k m :=
  MvPolynomial.X (0 : Fin (m + 1))
abbrev G (k : Type u) [Field k] (m : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k
abbrev H (k : Type u) [Field k] (m : ℕ) :=
  HomogeneousLocalization.Away (G k m) (Xzero k m)

theorem xzeroHomogeneous : MvPolynomial.X (0 : Fin (m + 1)) ∈ G k m 1 :=
  by change (MvPolynomial.X (0 : Fin (m + 1))).IsHomogeneous 1
     exact MvPolynomial.isHomogeneous_X (R := k) _

theorem xnextHomogeneous (i : Fin m) :
    MvPolynomial.X (Fin.succ i : Fin (m + 1)) ∈ G k m 1 :=
  by change (MvPolynomial.X (Fin.succ i : Fin (m + 1))).IsHomogeneous 1
     exact MvPolynomial.isHomogeneous_X (R := k) _

theorem projectiveVariableHomogeneous (i : Fin (m + 1)) :
    MvPolynomial.X i ∈ G k m 1 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact xzeroHomogeneous (k := k) (m := m)
  · exact xnextHomogeneous (k := k) (m := m) j

def variableToChart (i : Fin m) : H k m :=
  HomogeneousLocalization.Away.mk (G k m)
    (xzeroHomogeneous (k := k) (m := m)) 1
    (MvPolynomial.X (Fin.succ i : Fin (m + 1)))
    (by simpa using xnextHomogeneous (k := k) (m := m) i)

theorem val_variableToChart (i : Fin m) :
    HomogeneousLocalization.val (variableToChart (k := k) (m := m) i) =
      Localization.mk (MvPolynomial.X (Fin.succ i : Fin (m + 1)))
        ⟨Xzero k m, (Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp [Xzero]⟩⟩ := by
  rw [variableToChart, HomogeneousLocalization.Away.val_mk]
  simp only [pow_one]

def constantsToDegreeZero : k →+* G k m 0 where
  toFun c := ⟨MvPolynomial.C c, by
    change (MvPolynomial.C c).IsHomogeneous 0
    exact MvPolynomial.isHomogeneous_C _ _⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def constantsRingHom : k →+* H k m :=
  (HomogeneousLocalization.fromZeroRingHom (G k m)
    (Submonoid.powers (MvPolynomial.X (0 : Fin (m + 1))))).comp
    (constantsToDegreeZero (k := k) (m := m))

def chartVariables : Fin m → H k m := variableToChart (k := k) (m := m)

def chartToAway : MvPolynomial (Fin m) k →+* H k m :=
  MvPolynomial.eval₂Hom (constantsRingHom (k := k) (m := m))
    (chartVariables (k := k) (m := m))

def dehomMap : A k m →+* MvPolynomial (Fin m) k :=
  (ProjectiveChartCoordinates.dehomogenizeProjectiveChart
    (0 : Fin (m + 1)) (ProjectiveChartCoordinates.zerothChartEquiv (m := m))).toRingHom

def valHom : H k m →+* Localization (Submonoid.powers (Xzero k m)) where
  toFun z := HomogeneousLocalization.val (𝒜 := G k m)
    (x := Submonoid.powers (Xzero k m)) z
  map_one' := HomogeneousLocalization.val_one
  map_mul' := HomogeneousLocalization.val_mul
  map_zero' := HomogeneousLocalization.val_zero
  map_add' := HomogeneousLocalization.val_add

def localizationDehom : Localization.Away (Xzero k m) →+*
    MvPolynomial (Fin m) k :=
  Localization.awayLift (dehomMap (k := k) (m := m))
    (Xzero k m) (by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨1, ?_⟩
      simp [dehomMap, ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero])

theorem localizationDehom_mk_pow (p : A k m) (n : ℕ) :
    localizationDehom (k := k) (m := m)
        (Localization.mk p ⟨(Xzero k m) ^ n,
          (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩) =
      dehomMap (k := k) (m := m) p := by
  rw [localizationDehom]
  change Localization.awayLift (dehomMap (k := k) (m := m)) (Xzero k m)
    (isUnit_iff_exists_inv.mpr ⟨1, by
      simp [dehomMap, ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero]⟩)
    (Localization.mk p ⟨(Xzero k m) ^ n,
      (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (dehomMap (k := k) (m := m))
    (Xzero k m) p 1 (by
      simp [dehomMap, ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero]) n]
  simp

def awayToChart : H k m →+* MvPolynomial (Fin m) k :=
  (localizationDehom (k := k) (m := m)).comp (valHom (k := k) (m := m))

theorem awayToChart_constants (c : k) :
    awayToChart (k := k) (m := m) (constantsRingHom (k := k) (m := m) c) =
      MvPolynomial.C c := by
  change localizationDehom (k := k) (m := m)
    (HomogeneousLocalization.val (HomogeneousLocalization.mk
      ⟨0, constantsToDegreeZero (k := k) (m := m) c, 1, one_mem _⟩)) = _
  rw [HomogeneousLocalization.val_mk]
  change localizationDehom (k := k) (m := m)
    (Localization.mk (MvPolynomial.C c) ⟨1, one_mem _⟩) = _
  simpa [Xzero, dehomMap, ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero]
    using localizationDehom_mk_pow (k := k) (m := m) (MvPolynomial.C c) 0

theorem awayToChart_chartToAway_X (i : Fin m) :
    awayToChart (k := k) (m := m) (chartToAway (k := k) (m := m) (MvPolynomial.X i)) =
      MvPolynomial.X i := by
  rw [awayToChart, RingHom.comp_apply]
  change localizationDehom (k := k) (m := m)
      (HomogeneousLocalization.val (chartToAway (k := k) (m := m)
        (MvPolynomial.X i))) = _
  rw [chartToAway, MvPolynomial.eval₂Hom_X', chartVariables]
  rw [variableToChart, HomogeneousLocalization.Away.val_mk]
  rw [localizationDehom_mk_pow]
  simp [dehomMap, ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero]

theorem awayToChart_chartToAway_C (c : k) :
    awayToChart (k := k) (m := m) (chartToAway (k := k) (m := m) (MvPolynomial.C c)) =
      MvPolynomial.C c := by
  simp [chartToAway, MvPolynomial.eval₂Hom_C, awayToChart_constants]

theorem awayToChart_comp_chartToAway :
    (awayToChart (k := k) (m := m)).comp (chartToAway (k := k) (m := m)) =
      RingHom.id (MvPolynomial (Fin m) k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simpa [RingHom.comp_apply] using awayToChart_chartToAway_C (k := k) (m := m) c
  · intro i
    simpa [RingHom.comp_apply] using awayToChart_chartToAway_X (k := k) (m := m) i

theorem chartToAway_monomial_fraction (a : ℕ)
    (ai : Fin (m + 1) → ℕ) (hai : ∑ i, ai i = a) :
    ∃ p : MvPolynomial (Fin m) k,
      chartToAway (k := k) (m := m) p =
        HomogeneousLocalization.Away.mk (G k m)
          (xzeroHomogeneous (k := k) (m := m)) a
          (∏ i : Fin (m + 1), MvPolynomial.X i ^ ai i)
          (by
            have hmem :
                (∏ i : Fin (m + 1), MvPolynomial.X i ^ ai i) ∈
                  G k m (∑ i, ai i) := by
              simpa using SetLike.prod_pow_mem_graded (G k m)
                (fun _ : Fin (m + 1) ↦ 1) (fun i ↦ MvPolynomial.X i) ai
                (F := Finset.univ)
                (fun i _ ↦ projectiveVariableHomogeneous (k := k) (m := m) i)
            simpa [hai] using hmem) := by
  subst a
  simp only [Fin.sum_univ_succ]
  let p : MvPolynomial (Fin m) k :=
    ∏ j : Fin m, MvPolynomial.X j ^ ai (Fin.succ j)
  refine ⟨p, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  change valHom (chartToAway (k := k) (m := m) p) = _
  dsimp [p]
  simp only [map_prod, map_pow, chartToAway, MvPolynomial.eval₂Hom_X',
    chartVariables]
  change (∏ j : Fin m,
      HomogeneousLocalization.val (variableToChart (k := k) (m := m) j) ^
        ai (Fin.succ j)) = _
  simp only [val_variableToChart, Localization.mk_pow, Localization.mk_prod]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨1, one_mem _⟩, ?_⟩
  simp only [one_mul, Fin.prod_univ_succ, pow_add]
  simp only [SubmonoidClass.coe_pow,
    Finset.prod_pow_eq_pow_sum]
  ring

def ambientVariableAdjoin : Subalgebra (G k m 0) (A k m) :=
  Algebra.adjoin (G k m 0) (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i))

theorem ambient_variables_generate : ambientVariableAdjoin (k := k) (m := m) = ⊤ := by
  rw [← top_le_iff]
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C c =>
      exact (ambientVariableAdjoin (k := k) (m := m)).algebraMap_mem
        ⟨MvPolynomial.C c, by
          change (MvPolynomial.C c).IsHomogeneous 0
          exact MvPolynomial.isHomogeneous_C _ _⟩
  | add p q hp hq => exact (ambientVariableAdjoin (k := k) (m := m)).add_mem hp hq
  | mul_X p i hp =>
      exact (ambientVariableAdjoin (k := k) (m := m)).mul_mem hp
        (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem degreeZero_eq_C (z : G k m 0) :
    ∃ c : k, (z : A k m) = MvPolynomial.C c := by
  have hz : (z : A k m).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := (z : A k m))).2 z.property
  exact ⟨(z : A k m).coeff 0,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz⟩

theorem degreeZero_algebraMap_mem_chartRange (z : G k m 0) :
    algebraMap (G k m 0) (H k m) z ∈ Set.range (chartToAway (k := k) (m := m)) := by
  obtain ⟨c, hc⟩ := degreeZero_eq_C (k := k) (m := m) z
  have hz : z = constantsToDegreeZero (k := k) (m := m) c := Subtype.ext hc
  refine ⟨MvPolynomial.C c, ?_⟩
  rw [hz]
  change chartToAway (k := k) (m := m) (MvPolynomial.C c) =
    constantsRingHom (k := k) (m := m) c
  simp [chartToAway, MvPolynomial.eval₂Hom_C]

def chartImage : Subalgebra (G k m 0) (H k m) where
  carrier := Set.range (chartToAway (k := k) (m := m))
  zero_mem' := ⟨0, by simp [chartToAway]⟩
  one_mem' := ⟨1, by simp [chartToAway]⟩
  add_mem' := by
    rintro x y ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, by simp [chartToAway]⟩
  mul_mem' := by
    rintro x y ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p * q, by simp [chartToAway]⟩
  algebraMap_mem' := degreeZero_algebraMap_mem_chartRange (k := k) (m := m)

def coordinateFractionSet : Set (H k m) :=
  {z | ∃ (a : ℕ) (ai : Fin (m + 1) → ℕ),
    ∃ (hai : ∑ i, ai i • 1 = a • 1) (_ : ∀ i, ai i ≤ 1),
      HomogeneousLocalization.Away.mk (G k m)
        (xzeroHomogeneous (k := k) (m := m)) a
        (∏ i : Fin (m + 1), MvPolynomial.X i ^ ai i)
        (by
          have hdegree : ∑ i, ai i = a := by simpa using hai
          simpa [hdegree] using SetLike.prod_pow_mem_graded (G k m)
            (fun _ : Fin (m + 1) ↦ 1) (fun i ↦ MvPolynomial.X i) ai
            (F := Finset.univ)
            (fun i _ ↦ projectiveVariableHomogeneous (k := k) (m := m) i)) = z}

theorem chartImage_eq_top : chartImage (k := k) (m := m) = ⊤ := by
  have hgen : Algebra.adjoin (G k m 0) (coordinateFractionSet (k := k) (m := m)) = ⊤ := by
    simpa [coordinateFractionSet] using
      (HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
        (f := Xzero k m) (xzeroHomogeneous (k := k) (m := m))
        (ι' := Fin (m + 1)) (fun i : Fin (m + 1) => MvPolynomial.X i)
        (ambient_variables_generate (k := k) (m := m))
        (fun _ => 1)
        (projectiveVariableHomogeneous (k := k) (m := m)))
  have hle : Algebra.adjoin (G k m 0) (coordinateFractionSet (k := k) (m := m)) ≤
      chartImage (k := k) (m := m) := by
    rw [Algebra.adjoin_le_iff]
    rintro z ⟨a, ai, hai, hle, rfl⟩
    have hs : ∑ i, ai i = a := by simpa using hai
    obtain ⟨p, hp⟩ := chartToAway_monomial_fraction
      (k := k) (m := m) a ai hs
    exact ⟨p, hp⟩
  apply top_unique
  intro z hz
  rw [← hgen] at hz
  exact hle hz

theorem chartToAway_surjective :
    Function.Surjective (chartToAway (k := k) (m := m)) := by
  intro z
  have hz : z ∈ chartImage (k := k) (m := m) := by
    rw [chartImage_eq_top (k := k) (m := m)]
    simp
  exact hz

theorem awayToChart_injective :
    Function.Injective (awayToChart (k := k) (m := m)) := by
  intro x y h
  obtain ⟨p, rfl⟩ := chartToAway_surjective (k := k) (m := m) x
  obtain ⟨q, rfl⟩ := chartToAway_surjective (k := k) (m := m) y
  have hpq : p = q := by
    calc
      p = awayToChart (k := k) (m := m) (chartToAway (k := k) (m := m) p) := by
        symm
        simpa only [RingHom.comp_apply, RingHom.id_apply] using
          congrArg (fun f : MvPolynomial (Fin m) k →+* MvPolynomial (Fin m) k => f p)
            (awayToChart_comp_chartToAway (k := k) (m := m))
      _ = awayToChart (k := k) (m := m) (chartToAway (k := k) (m := m) q) := h
      _ = q := by
        simpa only [RingHom.comp_apply, RingHom.id_apply] using
          congrArg (fun f : MvPolynomial (Fin m) k →+* MvPolynomial (Fin m) k => f q)
            (awayToChart_comp_chartToAway (k := k) (m := m))
  exact congrArg (chartToAway (k := k) (m := m)) hpq

theorem chartToAway_dehom_homogeneous
    (H : A k m) (d : ℕ) (hH : H.IsHomogeneous d) :
    chartToAway (k := k) (m := m) (dehomMap (k := k) (m := m) H) =
      HomogeneousLocalization.Away.mk (G k m)
          (xzeroHomogeneous (k := k) (m := m)) d H (by
          simpa using hH) := by
  apply awayToChart_injective (k := k) (m := m)
  calc
    awayToChart (k := k) (m := m)
        (chartToAway (k := k) (m := m) (dehomMap (k := k) (m := m) H)) =
      dehomMap (k := k) (m := m) H := by
        simpa only [RingHom.comp_apply, RingHom.id_apply] using
          congrArg (fun f : MvPolynomial (Fin m) k →+* MvPolynomial (Fin m) k =>
            f (dehomMap (k := k) (m := m) H))
            (awayToChart_comp_chartToAway (k := k) (m := m))
    _ = awayToChart (k := k) (m := m)
        (HomogeneousLocalization.Away.mk (G k m)
          (xzeroHomogeneous (k := k) (m := m)) d H (by simpa using hH)) := by
      symm
      change localizationDehom (k := k) (m := m)
        (HomogeneousLocalization.val
          (HomogeneousLocalization.Away.mk (G k m)
            (xzeroHomogeneous (k := k) (m := m)) d H (by simpa using hH))) = _
      rw [HomogeneousLocalization.Away.val_mk]
      exact localizationDehom_mk_pow (k := k) (m := m) H d

noncomputable def zerothChartRingEquiv :
    MvPolynomial (Fin m) k ≃+* H k m := by
  have hleft : Function.LeftInverse
      (awayToChart (k := k) (m := m)) (chartToAway (k := k) (m := m)) := by
    intro p
    simpa only [RingHom.comp_apply, RingHom.id_apply] using
      congrArg (fun f : MvPolynomial (Fin m) k →+* MvPolynomial (Fin m) k => f p)
        (awayToChart_comp_chartToAway (k := k) (m := m))
  exact RingEquiv.ofBijective (chartToAway (k := k) (m := m))
    ⟨hleft.injective, chartToAway_surjective (k := k) (m := m)⟩

/-- The standard zeroth basic open of the ambient projective spectrum has
the explicit affine coordinate ring used by the projective-chart maps. -/
noncomputable def zerothProjBasicOpenIsoSpec :
    (AlgebraicGeometry.Proj.basicOpen (G k m) (Xzero k m)).toScheme ≅
      AlgebraicGeometry.Spec (.of (MvPolynomial (Fin m) k)) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec (G k m) (Xzero k m)
      (xzeroHomogeneous (k := k) (m := m)) (by decide) ≪≫
    AlgebraicGeometry.Scheme.Spec.mapIso
      (zerothChartRingEquiv (k := k) (m := m)).toCommRingCatIso.op

open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartFactorization

noncomputable def componentEquationDegree
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (E : ProjectiveEquationIndex P) : ℕ := Classical.choose E.2

theorem componentEquation_isHomogeneous
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (E : ProjectiveEquationIndex P) :
    E.1.IsHomogeneous (componentEquationDegree P E) :=
  (Classical.choose_spec E.2).1

noncomputable def componentEquationFraction
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (E : ProjectiveEquationIndex P) : H k m :=
  HomogeneousLocalization.Away.mk (G k m)
    (xzeroHomogeneous (k := k) (m := m))
    (componentEquationDegree P E) E.1
    (by simpa using componentEquation_isHomogeneous (k := k) (m := m) P E)

noncomputable def componentHomogeneousChartIdeal
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) : Ideal (H k m) :=
  Ideal.span (Set.range (componentEquationFraction (k := k) (m := m) P))

theorem componentChartEquationIdeal_map_eq
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    Ideal.map (chartToAway (k := k) (m := m))
        (componentChartEquationIdeal P 0
          (ProjectiveChartCoordinates.zerothChartEquiv (m := m))) =
      componentHomogeneousChartIdeal (k := k) (m := m) P := by
  change Ideal.map (chartToAway (k := k) (m := m))
      (Ideal.span (Set.range fun E : ProjectiveEquationIndex P =>
        dehomMap (k := k) (m := m) E.1)) = _
  have hrange :
      Set.range (fun E : ProjectiveEquationIndex P =>
        chartToAway (k := k) (m := m) (dehomMap (k := k) (m := m) E.1)) =
      Set.range (componentEquationFraction (k := k) (m := m) P) := by
    ext z
    constructor
    · rintro ⟨E, rfl⟩
      exact ⟨E, (chartToAway_dehom_homogeneous (k := k) (m := m)
        E.1 (componentEquationDegree P E) (componentEquation_isHomogeneous P E)).symm⟩
    · rintro ⟨E, rfl⟩
      exact ⟨E, chartToAway_dehom_homogeneous (k := k) (m := m)
        E.1 (componentEquationDegree P E) (componentEquation_isHomogeneous P E)⟩
  rw [Ideal.map_span]
  have himage :
      chartToAway (k := k) (m := m) ''
          Set.range (fun E : ProjectiveEquationIndex P =>
            dehomMap (k := k) (m := m) E.1) =
        Set.range (fun E : ProjectiveEquationIndex P =>
          chartToAway (k := k) (m := m) (dehomMap (k := k) (m := m) E.1)) := by
    ext z
    constructor
    · rintro ⟨x, ⟨E, rfl⟩, rfl⟩
      exact ⟨E, rfl⟩
    · rintro ⟨E, rfl⟩
      exact ⟨dehomMap (k := k) (m := m) E.1, ⟨E, rfl⟩, rfl⟩
  rw [himage, hrange]
  rfl

noncomputable def componentChartClosedRingEquiv
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    (MvPolynomial (Fin m) k) ⧸
        (componentChartEquationIdeal P 0
          (ProjectiveChartCoordinates.zerothChartEquiv (m := m))) ≃+*
      (H k m) ⧸ componentHomogeneousChartIdeal (k := k) (m := m) P :=
  Ideal.quotientEquiv _ _ (zerothChartRingEquiv (k := k) (m := m))
    (componentChartEquationIdeal_map_eq (k := k) (m := m) P).symm

theorem componentProjectiveClosure_overlapEquationIdeals_eq
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1)) :
    LocalizedProjectiveChartTransition.localizedZeroChartEquationIdeal
        (K := k) chart (fun E : ProjectiveEquationIndex P => E.1) =
      LocalizedProjectiveChartTransition.localizedChosenChartEquationIdeal
        (K := k) chart (fun E : ProjectiveEquationIndex P => E.1) := by
  exact LocalizedProjectiveChartTransition.localized_chartEquationIdeals_eq
    (K := k) chart (fun E : ProjectiveEquationIndex P => E.1)
    (componentEquationDegree P) (componentEquation_isHomogeneous P)


def chartIndexPerm (chart : Fin (m + 1)) : Fin (m + 1) ≃ Fin (m + 1) where
  toFun := Fin.cases chart fun i =>
    (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart i).1
  invFun := fun a => if h : a = chart then 0 else
    Fin.succ ((AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart).symm ⟨a, h⟩)
  left_inv := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simp
    · have hne : (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart i).1 ≠ chart :=
        (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart i).2
      simp [hne]
  right_inv := by
    intro a
    by_cases h : a = chart
    · subst a
      simp
    · simp [h]

def renameGraded (e : Fin (m + 1) ≃ Fin (m + 1)) : G k m →+*ᵍ G k m where
  toRingHom := (MvPolynomial.renameEquiv k e).toRingEquiv.toRingHom
  map_mem := by
    intro d p hp
    exact hp.rename_isHomogeneous

theorem renameGraded_Xzero (chart : Fin (m + 1)) :
    renameGraded (k := k) (m := m) (chartIndexPerm (m := m) chart)
      (Xzero k m) = MvPolynomial.X chart := by
  simp [renameGraded, Xzero, chartIndexPerm]

def chartAwayViaRename (chart : Fin (m + 1)) :
    H k m →+* HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart) :=
  Eq.mp (congrArg (fun f : A k m =>
      H k m →+* HomogeneousLocalization.Away (G k m) f)
      (renameGraded_Xzero (k := k) (m := m) chart))
    (HomogeneousLocalization.Away.map
      (renameGraded (k := k) (m := m) (chartIndexPerm (m := m) chart))
      (Xzero k m))

theorem awayMap_transport_mk
    {f g : A k m} (φ : G k m →+*ᵍ G k m) (hfg : φ f = g)
    (hf : f ∈ G k m 1) (hg : g ∈ G k m 1)
    (d : ℕ) (p : A k m) (hp : p ∈ G k m (d • 1)) :
    Eq.mp (congrArg (fun z : A k m =>
        HomogeneousLocalization.Away (G k m) f →+*
          HomogeneousLocalization.Away (G k m) z) hfg)
      (HomogeneousLocalization.Away.map φ f)
      (HomogeneousLocalization.Away.mk (G k m) hf d p hp) =
    HomogeneousLocalization.Away.mk (G k m) hg d (φ p) (by simpa using φ.map_mem hp) := by
  cases hfg
  simp [HomogeneousLocalization.Away.map_mk]

def chartDehomAny (chart : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1)) k →+* MvPolynomial (Fin m) k :=
  (ProjectiveChartCoordinates.dehomogenizeProjectiveChart chart
    (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart)).toRingHom

theorem chartDehomAny_eq_rename (chart : Fin (m + 1)) :
    chartDehomAny (k := k) (m := m) chart =
      (dehomMap (k := k) (m := m)).comp
        (MvPolynomial.renameEquiv k
          (chartIndexPerm (m := m) chart).symm).toRingEquiv.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [chartDehomAny, dehomMap]
  · intro a
    by_cases h : a = chart
    · subst a
      simp [chartDehomAny, dehomMap,
        ProjectiveChartCoordinates.dehomogenizeProjectiveChart, chartIndexPerm]
    · let i := (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart).symm ⟨a, h⟩
      have hi : (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart i).1 = a := by
        exact congrArg Subtype.val
          ((AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart).apply_symm_apply ⟨a, h⟩)
      have hperm : (chartIndexPerm (m := m) chart).symm a = i.succ := by
        apply (chartIndexPerm (m := m) chart).injective
        simp [chartIndexPerm, i, h]
      simp [chartDehomAny, dehomMap,
        ProjectiveChartCoordinates.dehomogenizeProjectiveChart, chartIndexPerm, h]

def chartToAwayAny (chart : Fin (m + 1)) :
    MvPolynomial (Fin m) k →+* HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart) :=
  (chartAwayViaRename (k := k) (m := m) chart).comp
    (chartToAway (k := k) (m := m))

theorem chartAwayViaRename_mk (chart : Fin (m + 1)) (d : ℕ)
    (p : A k m) (hp : p ∈ G k m (d • 1)) :
    chartAwayViaRename (k := k) (m := m) chart
      (HomogeneousLocalization.Away.mk (G k m) (xzeroHomogeneous (k := k) (m := m))
        d p hp) =
      HomogeneousLocalization.Away.mk (G k m)
        (projectiveVariableHomogeneous (k := k) (m := m) chart) d
        (renameGraded (k := k) (m := m) (chartIndexPerm (m := m) chart) p)
        ((renameGraded (k := k) (m := m) (chartIndexPerm (m := m) chart)).map_mem hp) := by
  exact awayMap_transport_mk (k := k) (m := m)
    (renameGraded (k := k) (m := m) (chartIndexPerm (m := m) chart))
    (renameGraded_Xzero (k := k) (m := m) chart)
    (xzeroHomogeneous (k := k) (m := m))
    (projectiveVariableHomogeneous (k := k) (m := m) chart)
    d p (by simpa using hp)

theorem chartToAwayAny_dehom_homogeneous (chart : Fin (m + 1))
    (p : A k m) (d : ℕ) (hp : p.IsHomogeneous d) :
    chartToAwayAny (k := k) (m := m) chart
        (chartDehomAny (k := k) (m := m) chart p) =
      HomogeneousLocalization.Away.mk (G k m)
        (projectiveVariableHomogeneous (k := k) (m := m) chart) d p
        (by simpa using hp) := by
  let p' := (MvPolynomial.renameEquiv k
    (chartIndexPerm (m := m) chart).symm) p
  have hp' : p'.IsHomogeneous d := by
    exact hp.rename_isHomogeneous (f := (chartIndexPerm (m := m) chart).symm)
  have hzero := chartToAway_dehom_homogeneous (k := k) (m := m) p' d hp'
  rw [chartToAwayAny, RingHom.comp_apply]
  rw [chartDehomAny_eq_rename]
  change chartAwayViaRename (k := k) (m := m) chart
      (chartToAway (k := k) (m := m) (dehomMap (k := k) (m := m) p')) = _
  rw [hzero]
  simpa [p', renameGraded] using chartAwayViaRename_mk (k := k) (m := m) chart d p'
    (by simpa using hp')

theorem chartAwayViaRename_surjective (chart : Fin (m + 1)) :
    Function.Surjective (chartAwayViaRename (k := k) (m := m) chart) := by
  intro z
  obtain ⟨d, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (G k m) (projectiveVariableHomogeneous (k := k) (m := m) chart) z
  let p' := (MvPolynomial.renameEquiv k
    (chartIndexPerm (m := m) chart).symm) p
  have hp' : p' ∈ G k m (d • 1) := by
    simpa [p'] using hp.rename_isHomogeneous
      (f := (chartIndexPerm (m := m) chart).symm)
  refine ⟨HomogeneousLocalization.Away.mk (G k m)
    (xzeroHomogeneous (k := k) (m := m)) d p' hp', ?_⟩
  rw [chartAwayViaRename_mk]
  simp [p', renameGraded, MvPolynomial.rename_rename]

theorem chartToAwayAny_surjective (chart : Fin (m + 1)) :
    Function.Surjective (chartToAwayAny (k := k) (m := m) chart) := by
  intro z
  obtain ⟨u, hu⟩ := chartAwayViaRename_surjective (k := k) (m := m) chart z
  obtain ⟨p, hp⟩ := chartToAway_surjective (k := k) (m := m) u
  refine ⟨p, ?_⟩
  change chartAwayViaRename (k := k) (m := m) chart (chartToAway (k := k) (m := m) p) = z
  rw [hp]
  exact hu

def chartLocalizationDehomAny (chart : Fin (m + 1)) :
    Localization.Away (MvPolynomial.X (R := k) chart) →+* MvPolynomial (Fin m) k :=
  Localization.awayLift (chartDehomAny (k := k) (m := m) chart)
    (MvPolynomial.X (R := k) chart) (by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨1, ?_⟩
      simp [chartDehomAny, ProjectiveChartCoordinates.dehomogenizeProjectiveChart])

theorem chartLocalizationDehomAny_mk_pow (chart : Fin (m + 1))
    (p : A k m) (n : ℕ) :
    chartLocalizationDehomAny (k := k) (m := m) chart
        (Localization.mk p ⟨(MvPolynomial.X (R := k) chart) ^ n,
          (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩) =
      chartDehomAny (k := k) (m := m) chart p := by
  rw [chartLocalizationDehomAny]
  rw [Localization.awayLift_mk (chartDehomAny (k := k) (m := m) chart)
    (MvPolynomial.X (R := k) chart) p 1 (by
      simp [chartDehomAny, ProjectiveChartCoordinates.dehomogenizeProjectiveChart]) n]
  simp

def chartValHomAny (chart : Fin (m + 1)) :
    HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart) →+*
      Localization (Submonoid.powers (MvPolynomial.X (R := k) chart)) where
  toFun z := HomogeneousLocalization.val (𝒜 := G k m)
    (x := Submonoid.powers (MvPolynomial.X (R := k) chart)) z
  map_one' := HomogeneousLocalization.val_one
  map_mul' := HomogeneousLocalization.val_mul
  map_zero' := HomogeneousLocalization.val_zero
  map_add' := HomogeneousLocalization.val_add

def awayToChartAny (chart : Fin (m + 1)) :
    HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart) →+* MvPolynomial (Fin m) k :=
  (chartLocalizationDehomAny (k := k) (m := m) chart).comp
    (chartValHomAny (k := k) (m := m) chart)

theorem chartToAwayAny_C (chart : Fin (m + 1)) (c : k) :
    chartToAwayAny (k := k) (m := m) chart (MvPolynomial.C c) =
      HomogeneousLocalization.Away.mk (G k m)
        (projectiveVariableHomogeneous (k := k) (m := m) chart) 0
        (MvPolynomial.C c) (by simpa using MvPolynomial.isHomogeneous_C c 0) := by
  rw [chartToAwayAny, RingHom.comp_apply, chartToAway, MvPolynomial.eval₂Hom_C]
  change chartAwayViaRename (k := k) (m := m) chart
    (HomogeneousLocalization.Away.mk (G k m) (xzeroHomogeneous (k := k) (m := m)) 0
      (MvPolynomial.C c) (by simpa using MvPolynomial.isHomogeneous_C c 0)) = _
  simpa [renameGraded] using chartAwayViaRename_mk (k := k) (m := m) chart 0
    (MvPolynomial.C c) (by simpa using MvPolynomial.isHomogeneous_C c 0)

theorem chartToAwayAny_X (chart : Fin (m + 1)) (i : Fin m) :
    chartToAwayAny (k := k) (m := m) chart (MvPolynomial.X i) =
      HomogeneousLocalization.Away.mk (G k m)
        (projectiveVariableHomogeneous (k := k) (m := m) chart) 1
        (MvPolynomial.X ((AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart i).1))
        (by simpa using MvPolynomial.isHomogeneous_X (R := k) _) := by
  rw [chartToAwayAny, RingHom.comp_apply, chartToAway, MvPolynomial.eval₂Hom_X']
  change chartAwayViaRename (k := k) (m := m) chart
    (HomogeneousLocalization.Away.mk (G k m) (xzeroHomogeneous (k := k) (m := m)) 1
      (MvPolynomial.X (Fin.succ i)) (by simpa using MvPolynomial.isHomogeneous_X (R := k) _)) = _
  simpa [chartIndexPerm, renameGraded] using chartAwayViaRename_mk (k := k) (m := m) chart 1
    (MvPolynomial.X (Fin.succ i)) (by simpa using MvPolynomial.isHomogeneous_X (R := k) _)

theorem awayToChartAny_C (chart : Fin (m + 1)) (c : k) :
    awayToChartAny (k := k) (m := m) chart (chartToAwayAny (k := k) (m := m) chart (MvPolynomial.C c)) =
      MvPolynomial.C c := by
  rw [chartToAwayAny_C]
  change chartLocalizationDehomAny (k := k) (m := m) chart
    (HomogeneousLocalization.val
      (HomogeneousLocalization.Away.mk (G k m)
        (projectiveVariableHomogeneous (k := k) (m := m) chart) 0
        (MvPolynomial.C c) (by simpa using MvPolynomial.isHomogeneous_C c 0))) = _
  rw [HomogeneousLocalization.Away.val_mk]
  simpa [chartDehomAny, ProjectiveChartCoordinates.dehomogenizeProjectiveChart]
    using chartLocalizationDehomAny_mk_pow (k := k) (m := m) chart
      (MvPolynomial.C c) 0

theorem awayToChartAny_X (chart : Fin (m + 1)) (i : Fin m) :
    awayToChartAny (k := k) (m := m) chart (chartToAwayAny (k := k) (m := m) chart (MvPolynomial.X i)) =
      MvPolynomial.X i := by
  rw [chartToAwayAny_X]
  change chartLocalizationDehomAny (k := k) (m := m) chart
    (HomogeneousLocalization.val
      (HomogeneousLocalization.Away.mk (G k m)
        (projectiveVariableHomogeneous (k := k) (m := m) chart) 1
        (MvPolynomial.X ((AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart i).1))
        (by simpa using MvPolynomial.isHomogeneous_X (R := k) _))) = _
  rw [HomogeneousLocalization.Away.val_mk]
  rw [chartLocalizationDehomAny_mk_pow]
  have hne : (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart i).1 ≠ chart :=
    (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart i).2
  simp [chartDehomAny, ProjectiveChartCoordinates.dehomogenizeProjectiveChart, hne]

theorem awayToChartAny_comp_chartToAwayAny (chart : Fin (m + 1)) :
    (awayToChartAny (k := k) (m := m) chart).comp
        (chartToAwayAny (k := k) (m := m) chart) =
      RingHom.id (MvPolynomial (Fin m) k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simpa [RingHom.comp_apply] using awayToChartAny_C (k := k) (m := m) chart c
  · intro i
    simpa [RingHom.comp_apply] using awayToChartAny_X (k := k) (m := m) chart i

theorem chartToAwayAny_injective (chart : Fin (m + 1)) :
    Function.Injective (chartToAwayAny (k := k) (m := m) chart) := by
  intro p q hpq
  have h := congrArg (awayToChartAny (k := k) (m := m) chart) hpq
  change ((awayToChartAny (k := k) (m := m) chart).comp
      (chartToAwayAny (k := k) (m := m) chart)) p =
    ((awayToChartAny (k := k) (m := m) chart).comp
      (chartToAwayAny (k := k) (m := m) chart)) q at h
  rw [awayToChartAny_comp_chartToAwayAny] at h
  simpa using h

noncomputable def chartRingEquivAny (chart : Fin (m + 1)) :
    MvPolynomial (Fin m) k ≃+*
      HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart) :=
  RingEquiv.ofBijective (chartToAwayAny (k := k) (m := m) chart)
    ⟨chartToAwayAny_injective (k := k) (m := m) chart,
      chartToAwayAny_surjective (k := k) (m := m) chart⟩

noncomputable def componentEquationFractionAny
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (chart : Fin (m + 1))
    (E : ProjectiveEquationIndex P) :
    HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart) :=
  HomogeneousLocalization.Away.mk (G k m)
    (projectiveVariableHomogeneous (k := k) (m := m) chart)
    (componentEquationDegree (k := k) (m := m) P E) E.1
    (by simpa using componentEquation_isHomogeneous (k := k) (m := m) P E)

noncomputable def componentHomogeneousChartIdealAny
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (chart : Fin (m + 1)) :
    Ideal (HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart)) :=
  Ideal.span (Set.range (componentEquationFractionAny (k := k) (m := m) P chart))

theorem componentChartEquationIdeal_map_eq_any
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (chart : Fin (m + 1)) :
    Ideal.map (chartToAwayAny (k := k) (m := m) chart)
        (componentChartEquationIdeal P chart
          (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart)) =
      componentHomogeneousChartIdealAny (k := k) (m := m) P chart := by
  change Ideal.map (chartToAwayAny (k := k) (m := m) chart)
      (Ideal.span (Set.range fun E : ProjectiveEquationIndex P =>
        chartDehomAny (k := k) (m := m) chart E.1)) = _
  have hrange :
      Set.range (fun E : ProjectiveEquationIndex P =>
        chartToAwayAny (k := k) (m := m) chart
          (chartDehomAny (k := k) (m := m) chart E.1)) =
      Set.range (componentEquationFractionAny (k := k) (m := m) P chart) := by
    ext z
    constructor
    · rintro ⟨E, rfl⟩
      exact ⟨E, (chartToAwayAny_dehom_homogeneous (k := k) (m := m) chart
        E.1 (componentEquationDegree (k := k) (m := m) P E)
        (componentEquation_isHomogeneous (k := k) (m := m) P E)).symm⟩
    · rintro ⟨E, rfl⟩
      exact ⟨E, chartToAwayAny_dehom_homogeneous (k := k) (m := m) chart
        E.1 (componentEquationDegree (k := k) (m := m) P E)
        (componentEquation_isHomogeneous (k := k) (m := m) P E)⟩
  rw [Ideal.map_span]
  have himage :
      chartToAwayAny (k := k) (m := m) chart ''
          Set.range (fun E : ProjectiveEquationIndex P =>
            chartDehomAny (k := k) (m := m) chart E.1) =
        Set.range (fun E : ProjectiveEquationIndex P =>
          chartToAwayAny (k := k) (m := m) chart
            (chartDehomAny (k := k) (m := m) chart E.1)) := by
    ext z
    constructor
    · rintro ⟨x, ⟨E, rfl⟩, rfl⟩
      exact ⟨E, rfl⟩
    · rintro ⟨E, rfl⟩
      exact ⟨chartDehomAny (k := k) (m := m) chart E.1, ⟨E, rfl⟩, rfl⟩
  rw [himage, hrange]
  rfl

/-- The exact dehomogenized component-chart quotient is the homogeneous
equation quotient in the standard `Proj` localization at `X chart`. -/
noncomputable def componentChartClosedRingEquivAny
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (chart : Fin (m + 1)) :
    (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart
      (AsymptoticChartArcAdapter.chartAffineCoordinateEquiv chart)) ≃+*
      (HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart)) ⧸
        componentHomogeneousChartIdealAny (k := k) (m := m) P chart :=
  Ideal.quotientEquiv _ _ (chartRingEquivAny (k := k) (m := m) chart)
    (componentChartEquationIdeal_map_eq_any (k := k) (m := m) P chart).symm

/-- Mathlib's standard affine chart identification for the selected projective
coordinate, before imposing the component equations. -/
noncomputable def componentBasicOpenProjIsoSpecAny
    (chart : Fin (m + 1)) :
    (AlgebraicGeometry.Proj.basicOpen (G k m) (MvPolynomial.X chart)).toScheme ≅
      AlgebraicGeometry.Spec
        (.of (HomogeneousLocalization.Away (G k m) (MvPolynomial.X chart))) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec (G k m) (MvPolynomial.X chart)
      (projectiveVariableHomogeneous (k := k) (m := m) chart) (by decide)

end
end Stafford38.Geometry.ProjectiveChartNormalizationBridge
