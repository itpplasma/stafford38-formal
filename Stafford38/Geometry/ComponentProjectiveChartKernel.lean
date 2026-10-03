module
public import Stafford38.Geometry.ComponentProjectiveChartFactorization

@[expose] public section

/-! Exact affine generic-point kernel of the projective cone in any chart. -/

namespace Stafford38.Geometry.ComponentProjectiveChartKernel

open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.ComponentProjectiveChartFactorization

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000

universe u

variable {k : Type u} [Field k] {m : ℕ}

theorem homogenizeAtZero_eval_common_scale
    {S : Type*} [CommSemiring S] (f : MvPolynomial (Fin m) k)
    (coeff : k →+* S) (y : Fin m → S) (t : S) :
    MvPolynomial.eval₂ coeff
        (fun a ↦ Fin.cases 1 y a * t) (homogenizeAtZero f) =
      MvPolynomial.eval₂ coeff (Fin.cases 1 y) (homogenizeAtZero f) *
        t ^ f.totalDegree := by
  exact eval₂_mul_common_of_isHomogeneous
    (homogenizeAtZero_isHomogeneous f) coeff (Fin.cases 1 y) t

/-- Reindex zeroth-chart coordinates so coordinate zero becomes the chosen
projective chart and successors follow the explicit complement equivalence. -/
def chartIndexEquiv (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) :
    Fin (m + 1) ≃ Fin (m + 1) :=
  Equiv.ofBijective (fun a ↦ Fin.cases chart (fun i ↦ (e i).1) a) (by
    constructor
    · intro a b hab
      rcases Fin.eq_zero_or_eq_succ a with ha | ⟨i, ha⟩
      · subst a
        rcases Fin.eq_zero_or_eq_succ b with hb | ⟨j, hb⟩
        · subst b
          rfl
        · subst b
          have hab' : chart = (e j).1 := by
            change chart = (e j).1 at hab
            exact hab
          exact False.elim ((e j).property hab'.symm)
      · subst a
        rcases Fin.eq_zero_or_eq_succ b with hb | ⟨j, hb⟩
        · subst b
          have hab' : (e i).1 = chart := by
            change (e i).1 = chart at hab
            exact hab
          exact False.elim ((e i).property hab')
        · subst b
          have hab' : (e i).1 = (e j).1 := by
            change (e i).1 = (e j).1 at hab
            exact hab
          have hij : i = j := e.injective (Subtype.ext hab')
          subst j
          rfl
    · intro b
      by_cases hb : b = chart
      · refine ⟨0, ?_⟩
        simp [hb]
      · let i : Fin m := e.symm ⟨b, hb⟩
        refine ⟨Fin.succ i, ?_⟩
        simp [i]
  )

@[simp] theorem chartIndexEquiv_zero (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) :
    chartIndexEquiv chart e 0 = chart := by
  rfl

@[simp] theorem chartIndexEquiv_succ (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) (i : Fin m) :
    chartIndexEquiv chart e i.succ = (e i).1 := by
  rfl

/-- Homogenize in the selected chart by transporting the standard
zeroth-chart homogenization along the coordinate permutation. -/
def homogenizeAtChart (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (f : MvPolynomial (Fin m) k) : MvPolynomial (Fin (m + 1)) k :=
  MvPolynomial.rename (chartIndexEquiv chart e) (homogenizeAtZero f)

theorem homogenizeAtChart_isHomogeneous (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (f : MvPolynomial (Fin m) k) :
    (homogenizeAtChart chart e f).IsHomogeneous f.totalDegree := by
  simpa [homogenizeAtChart] using
    (homogenizeAtZero_isHomogeneous f).rename_isHomogeneous

theorem dehomogenize_chart_homogenizeAtChart (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (f : MvPolynomial (Fin m) k) :
    dehomogenizeProjectiveChart chart e (homogenizeAtChart chart e f) = f := by
  have hmaps :
      (dehomogenizeProjectiveChart chart e).comp
        (MvPolynomial.renameEquiv k (chartIndexEquiv chart e)).toAlgHom =
        projectiveDehomogenize := by
    apply MvPolynomial.algHom_ext
    intro a
    rcases Fin.eq_zero_or_eq_succ a with hzero | ⟨i, hi⟩
    · subst a
      simp [dehomogenizeProjectiveChart, projectiveDehomogenize,
        chartIndexEquiv_zero]
    · subst a
      simp [dehomogenizeProjectiveChart, projectiveDehomogenize,
        chartIndexEquiv_succ, (e i).property]
  calc
    dehomogenizeProjectiveChart chart e (homogenizeAtChart chart e f) =
        ((dehomogenizeProjectiveChart chart e).comp
          (MvPolynomial.renameEquiv k (chartIndexEquiv chart e)).toAlgHom)
          (homogenizeAtZero f) := rfl
    _ = projectiveDehomogenize (homogenizeAtZero f) := by rw [hmaps]
    _ = f := projectiveDehomogenize_homogenizeAtZero f

def chartGenericPoint (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) :
    Fin m → ComponentFractionField P :=
  fun i ↦ componentProjectivePoint P (e i).1 / componentProjectivePoint P chart

theorem componentChartEquationIdeal_eq_genericEvalKer
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    componentChartEquationIdeal P chart e =
      RingHom.ker (MvPolynomial.eval₂Hom
        (algebraMap k (ComponentFractionField P)) (chartGenericPoint P chart e)) := by
  apply le_antisymm
  · let q : Fin (m + 1) → ComponentFractionField P :=
      fun a ↦ componentProjectivePoint P a / componentProjectivePoint P chart
    have hqchart : q chart = 1 := by
      dsimp [q]
      exact div_self hchart
    have hq : ∀ a, q a = (componentProjectivePoint P chart)⁻¹ *
        componentProjectivePoint P a := by
      intro a
      simp [q, div_eq_mul_inv, mul_comm]
    have hkernel := eval₂_ker_contains_componentChartEquationIdeal
      (P := P) (V := ComponentFractionField P)
      (coeff := algebraMap k (ComponentFractionField P))
      (ι := RingHom.id (ComponentFractionField P))
      (hι := Function.injective_id) (hcoeff := rfl)
      (q := q) (chart := chart) (e := e) (hqchart := hqchart)
      (scale := (componentProjectivePoint P chart)⁻¹) (hq := hq)
    change componentChartEquationIdeal P chart e ≤
      RingHom.ker (MvPolynomial.eval₂Hom
        (algebraMap k (ComponentFractionField P))
        (fun i ↦ q (e i).1)) at hkernel
    change componentChartEquationIdeal P chart e ≤
      RingHom.ker (MvPolynomial.eval₂Hom
        (algebraMap k (ComponentFractionField P)) (chartGenericPoint P chart e))
    exact hkernel
  · intro f hf
    change MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
      (chartGenericPoint P chart e) f = 0 at hf
    let H := homogenizeAtChart chart e f
    have hdehom : dehomogenizeProjectiveChart chart e H = f :=
      dehomogenize_chart_homogenizeAtChart chart e f
    have hH : H.IsHomogeneous f.totalDegree :=
      homogenizeAtChart_isHomogeneous chart e f
    let σ := chartIndexEquiv chart e
    have hpoint : (fun a ↦ componentProjectivePoint P (σ a)) =
        fun a ↦ Fin.cases 1 (chartGenericPoint P chart e) a *
          componentProjectivePoint P chart := by
      funext a
      rcases Fin.eq_zero_or_eq_succ a with hzero | ⟨i, hi⟩
      · subst a
        simp [σ, chartIndexEquiv_zero, componentProjectivePoint_eq_finCases]
      · subst a
        change componentProjectivePoint P (e i).1 =
          (componentProjectivePoint P (e i).1 / componentProjectivePoint P chart) *
            componentProjectivePoint P chart
        exact (div_mul_cancel₀ (componentProjectivePoint P (e i).1) hchart).symm
    have hgenericEval :
        MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
          (componentProjectivePoint P) H = 0 := by
      have hscale :
          MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
            (fun a ↦ Fin.cases 1 (chartGenericPoint P chart e) a *
              componentProjectivePoint P chart) (homogenizeAtZero f) =
            MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
              (Fin.cases 1 (chartGenericPoint P chart e)) (homogenizeAtZero f) *
              componentProjectivePoint P chart ^ f.totalDegree := by
        exact homogenizeAtZero_eval_common_scale f
          (algebraMap k (ComponentFractionField P))
          (chartGenericPoint P chart e) (componentProjectivePoint P chart)
      have hrename :
          MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
              (componentProjectivePoint P)
              (MvPolynomial.rename σ (homogenizeAtZero f)) =
            MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
              (componentProjectivePoint P ∘ σ) (homogenizeAtZero f) :=
        MvPolynomial.eval₂_rename (algebraMap k (ComponentFractionField P)) σ
          (componentProjectivePoint P) (homogenizeAtZero f)
      calc
        MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
            (componentProjectivePoint P) H =
            MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
              (fun a ↦ componentProjectivePoint P (σ a)) (homogenizeAtZero f) := by
                dsimp only [H, homogenizeAtChart]
                exact hrename
        _ = MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
              (Fin.cases 1 (chartGenericPoint P chart e)) (homogenizeAtZero f) *
                componentProjectivePoint P chart ^ f.totalDegree := by
                rw [hpoint]
                exact hscale
        _ = 0 := by
            have hzero : MvPolynomial.eval₂
                (algebraMap k (ComponentFractionField P))
                (Fin.cases 1 (chartGenericPoint P chart e))
                (homogenizeAtZero f) = 0 := by
              calc
                _ = MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
                    (chartGenericPoint P chart e)
                    (projectiveDehomogenize (homogenizeAtZero f)) :=
                      (eval₂_projectiveDehomogenize
                        (algebraMap k (ComponentFractionField P))
                        (chartGenericPoint P chart e) (homogenizeAtZero f)).symm
                _ = MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
                    (chartGenericPoint P chart e) f := by
                      rw [projectiveDehomogenize_homogenizeAtZero]
                _ = 0 := hf
            rw [hzero]
            simp
    have hcone : componentProjectiveConeMap P H = 0 := by
      rw [componentProjectiveConeMap_eq_eval₂_mul_X_pow_of_isHomogeneous P hH]
      have hgenericEvalZero : MvPolynomial.eval₂
          (algebraMap k (ComponentFractionField P))
          (Fin.cases 1 (fun j ↦ componentCoordinate P j)) H = 0 := by
        simpa only [componentProjectivePoint_eq_finCases] using hgenericEval
      rw [hgenericEvalZero]
      simp
    have hHmem : H ∈ componentProjectiveClosureIdeal P := hcone
    have hdehom_mem : dehomogenizeProjectiveChart chart e H ∈
        componentChartEquationIdeal P chart e := by
      apply Ideal.subset_span
      exact ⟨⟨H, f.totalDegree, hH, hHmem⟩, rfl⟩
    rw [hdehom] at hdehom_mem
    exact hdehom_mem

#print axioms chartIndexEquiv
#print axioms homogenizeAtChart_isHomogeneous
#print axioms dehomogenize_chart_homogenizeAtChart
#print axioms componentChartEquationIdeal_eq_genericEvalKer

/-- The canonical quotient-to-function-field map for a projective chart,
derived from generic-chart evaluation via the quotient universal property. -/
noncomputable def canonicalComponentChartEquationGenericPointMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e) →ₐ[k]
      ComponentFractionField P :=
  Ideal.Quotient.liftₐ (componentChartEquationIdeal P chart e)
    (MvPolynomial.aeval (chartGenericPoint P chart e)) (by
      intro f hf
      have hker := componentChartEquationIdeal_eq_genericEvalKer P chart e hchart
      rw [hker] at hf
      exact RingHom.mem_ker.mp hf)

/-- Generator action of the canonical chart quotient map. -/
theorem canonicalComponentChartEquationGenericPointMap_mk
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0)
    (f : MvPolynomial (Fin m) k) :
    canonicalComponentChartEquationGenericPointMap P chart e hchart
        (Ideal.Quotient.mk _ f) =
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e) f := by
  change Ideal.Quotient.lift (componentChartEquationIdeal P chart e)
      (MvPolynomial.aeval (chartGenericPoint P chart e)).toRingHom _
      (Ideal.Quotient.mk (componentChartEquationIdeal P chart e) f) = _
  rw [Ideal.Quotient.lift_mk]
  rfl

/-- The quotient universal-property characterization of the canonical map. -/
theorem canonicalComponentChartEquationGenericPointMap_comp_mk
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    (canonicalComponentChartEquationGenericPointMap P chart e hchart).comp
        (Ideal.Quotient.mkₐ k (componentChartEquationIdeal P chart e)) =
      MvPolynomial.aeval (chartGenericPoint P chart e) := by
  exact Ideal.Quotient.liftₐ_comp _ _ _

/-- Any algebra map with the prescribed generic-chart evaluation is this map. -/
theorem canonicalComponentChartEquationGenericPointMap_unique
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0)
    (f : (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e) →ₐ[k]
      ComponentFractionField P)
    (hf : f.comp (Ideal.Quotient.mkₐ k (componentChartEquationIdeal P chart e)) =
      MvPolynomial.aeval (chartGenericPoint P chart e)) :
    f = canonicalComponentChartEquationGenericPointMap P chart e hchart := by
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hp := congrArg (fun g : MvPolynomial (Fin m) k →ₐ[k]
      ComponentFractionField P => g p) hf
  rw [canonicalComponentChartEquationGenericPointMap_mk]
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    MvPolynomial.aeval_def] using hp

end

end Stafford38.Geometry.ComponentProjectiveChartKernel
