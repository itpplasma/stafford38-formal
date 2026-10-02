import Stafford38.Geometry.FormalDivisorAxisLift
import Stafford38.Geometry.TiltedArcAvoidance
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Conditional tilted-arc adapter for a smooth formal local chart

This file starts *after* a chosen smooth local model has been identified with
`k[[t,z₁,…,z_d]]`.  It does not construct that identification for an arbitrary
smooth local ring.  Given the projective chart coordinates, their formal
transverse derivatives, the strict t-order factorizations, and the closed-point
transversality minor in this model, it tilts the t-axis away from one nonzero
bad-locus series.  The substitution preserves constants and unit minors, so
`FormalDivisorAxisLift` supplies the printed normalized tangent columns and
axis conormal.  The local-model and transversality data remain explicit inputs.
-/

namespace Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

open Stafford38.GeometrySplitTangentMatrix
open Stafford38.GeometryFormalDivisorAxisLift
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryRetractionSpecialization
open Stafford38.GeometryPowerSeriesTangentLimit

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

universe u v w

variable {k : Type u} [Field k]

/-- The coefficient vector `(1, α₁, …, α_d)` with a constant codomain. -/
def tiltedArcCoefficients {d : ℕ} (α : Fin d → k) : Fin (d + 1) → k :=
  @Fin.cons d (fun _ => k) (1 : k) α

@[simp] theorem tiltedArcCoefficients_zero {d : ℕ} (α : Fin d → k) :
    tiltedArcCoefficients (k := k) α 0 = 1 := by
  simp [tiltedArcCoefficients]

@[simp] theorem tiltedArcCoefficients_succ {d : ℕ} (α : Fin d → k) (j : Fin d) :
    tiltedArcCoefficients (k := k) α j.succ = α j := by
  simp [tiltedArcCoefficients]

/-- The formal curve `t ↦ (t, α₁t, …, α_dt)` in the `PUnit` one-variable
presentation used by the existing bad-locus avoidance theorem. -/
def tiltedArcPointPUnit {d : ℕ} (α : Fin d → k) :
    Fin (d + 1) → MvPowerSeries PUnit.{1} k :=
  fun i => MvPowerSeries.C ((Fin.cons 1 α : Fin (d + 1) → k) i) *
    MvPowerSeries.X (PUnit.unit : PUnit.{1})

theorem tiltedArcHasSubstPUnit {d : ℕ} (α : Fin d → k) :
    MvPowerSeries.HasSubst (tiltedArcPointPUnit (k := k) α) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  change MvPowerSeries.constantCoeff
    (MvPowerSeries.C (tiltedArcCoefficients (k := k) α i) *
      MvPowerSeries.X (PUnit.unit : PUnit.{1})) = 0
  simp

/-- Restriction to the same tilted arc in Mathlib's `PUnit` target. -/
noncomputable def tiltedArcMapPUnit {d : ℕ} (α : Fin d → k) :
    MvPowerSeries (Fin (d + 1)) k →+* MvPowerSeries PUnit.{1} k :=
  (MvPowerSeries.substAlgHom (tiltedArcHasSubstPUnit (k := k) α)).toRingHom

/-- The canonical singleton-index identification from the avoidance target to
`PowerSeries`; this makes nonvanishing refer to exactly the same formal arc as
all tangent columns below. -/
noncomputable def punitToPowerSeries {k : Type u} [Field k] :
    MvPowerSeries PUnit.{1} k ≃ₐ[k] PowerSeries k :=
  MvPowerSeries.renameEquiv k (Equiv.equivPUnit Unit).symm

/-- The power-series arc map, obtained by transporting the existing avoidance
substitution along the canonical singleton-index equivalence. -/
noncomputable def tiltedArcMap {d : ℕ} (α : Fin d → k) :
    MvPowerSeries (Fin (d + 1)) k →+* PowerSeries k :=
  (punitToPowerSeries (k := k)).toRingEquiv.toRingHom.comp
    (tiltedArcMapPUnit (k := k) α)

/-- Restriction of a completed local function to the tilted arc. -/
noncomputable def tiltedArc {d : ℕ} (α : Fin d → k)
    (f : MvPowerSeries (Fin (d + 1)) k) : PowerSeries k :=
  tiltedArcMap (k := k) α f

/-- The existing avoidance theorem, specialized to the exact PUnit arc map used
below.  Keeping this conversion as a separate lemma also pins the singleton
index universe once, at the interface rather than in the downstream proof. -/
theorem exists_tiltedArcPointPUnit_avoidance [Infinite k] {d : ℕ}
    (bad : MvPowerSeries (Fin (d + 1)) k) (hbad : bad ≠ 0) :
    ∃ α : Fin d → k,
      MvPowerSeries.subst (tiltedArcPointPUnit (k := k) α) bad ≠ 0 := by
  exact Stafford38.Geometry.TiltedArcAvoidance.exists_tilt_subst_ne_zero.{u, 0} bad hbad

@[simp] theorem tiltedArc_X_t {d : ℕ} (α : Fin d → k) :
    tiltedArc (k := k) α (MvPowerSeries.X 0) = PowerSeries.X := by
  change MvPowerSeries.rename (Equiv.equivPUnit Unit).symm
      ((MvPowerSeries.substAlgHom (tiltedArcHasSubstPUnit (k := k) α))
        (MvPowerSeries.X 0)) = _
  rw [MvPowerSeries.substAlgHom_X]
  change MvPowerSeries.rename (Equiv.equivPUnit Unit).symm
    (MvPowerSeries.C (1 : k) * MvPowerSeries.X (PUnit.unit : PUnit.{1})) = _
  rw [map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
  simp [PowerSeries.X_apply]

private theorem tiltedArc_t_power_mul {d : ℕ} (α : Fin d → k)
    (r : ℕ) (f : MvPowerSeries (Fin (d + 1)) k) :
    tiltedArc (k := k) α ((MvPowerSeries.X 0) ^ r * f) =
      (PowerSeries.X : PowerSeries k) ^ r * tiltedArc (k := k) α f := by
  change (tiltedArcMap (k := k) α) ((MvPowerSeries.X 0) ^ r * f) = _
  rw [(tiltedArcMap (k := k) α).map_mul, (tiltedArcMap (k := k) α).map_pow]
  have hx : tiltedArcMap (k := k) α (MvPowerSeries.X 0) = PowerSeries.X := by
    simpa [tiltedArc] using tiltedArc_X_t (k := k) α
  rw [hx]
  rfl

private theorem constantCoeff_tiltedArcPUnit {d : ℕ} (α : Fin d → k)
    (f : MvPowerSeries (Fin (d + 1)) k) :
    MvPowerSeries.constantCoeff (tiltedArcMapPUnit (k := k) α f) =
      MvPowerSeries.constantCoeff f := by
  change MvPowerSeries.constantCoeff
      ((MvPowerSeries.substAlgHom (tiltedArcHasSubstPUnit (k := k) α)) f) = _
  rw [MvPowerSeries.substAlgHom_apply]
  have hsub := tiltedArcHasSubstPUnit (k := k) α
  have hzero : ∀ i, MvPowerSeries.constantCoeff
      (tiltedArcPointPUnit (k := k) α i) = 0 := by
    intro i
    change MvPowerSeries.constantCoeff
      (MvPowerSeries.C (tiltedArcCoefficients (k := k) α i) *
        MvPowerSeries.X (PUnit.unit : PUnit.{1})) = 0
    simp
  have hsplit : f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
      (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) := by ring
  have htail : MvPowerSeries.constantCoeff
      (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) = 0 := by simp
  rw [hsplit, MvPowerSeries.subst_add hsub]
  rw [MvPowerSeries.subst_C, map_add,
    MvPowerSeries.constantCoeff_subst_eq_zero hsub hzero htail]
  simp

@[simp] theorem tiltedArc_constantCoeff {d : ℕ} (α : Fin d → k)
    (f : MvPowerSeries (Fin (d + 1)) k) :
    PowerSeries.constantCoeff (tiltedArc (k := k) α f) =
      MvPowerSeries.constantCoeff f := by
  change MvPowerSeries.constantCoeff
    (MvPowerSeries.rename (Equiv.equivPUnit Unit).symm
      (tiltedArcMapPUnit (k := k) α f)) = _
  rw [MvPowerSeries.constantCoeff_rename]
  exact constantCoeff_tiltedArcPUnit α f

private theorem tiltedArc_ne_zero_of_avoidance {d : ℕ}
    (α : Fin d → k) (f : MvPowerSeries (Fin (d + 1)) k)
    (havoid : MvPowerSeries.subst (tiltedArcPointPUnit (k := k) α) f ≠ 0) :
    tiltedArc (k := k) α f ≠ 0 := by
  have hPUnit : tiltedArcMapPUnit (k := k) α f ≠ 0 := by
    simpa [tiltedArcMapPUnit, MvPowerSeries.substAlgHom_apply] using havoid
  intro hzero
  apply hPUnit
  have hzero' : (punitToPowerSeries (k := k))
      (tiltedArcMapPUnit (k := k) α f) = 0 := by
    change (punitToPowerSeries (k := k))
      (tiltedArcMapPUnit (k := k) α f) = 0 at hzero
    exact hzero
  have hkernel : (tiltedArcMapPUnit (k := k) α f) = 0 :=
    (punitToPowerSeries (k := k)).injective (by simpa using hzero')
  exact hkernel

/-- The formal transverse derivative columns in the smooth local model. -/
noncomputable def localTransverseDerivativeMatrix {d : ℕ} {ι : Type v}
    (q : ι → MvPowerSeries (Fin (d + 1)) k) :
    Matrix ι (Fin d) (MvPowerSeries (Fin (d + 1)) k) :=
  fun i j => MvPowerSeries.pderiv k (Fin.succ j) (q i)

/-- The transverse derivative matrix restricted to the chosen tilted arc. -/
noncomputable def tiltedTransverseDerivativeMatrix {d : ℕ} {ι : Type v}
    (α : Fin d → k) (q : ι → MvPowerSeries (Fin (d + 1)) k) :
    Matrix ι (Fin d) (PowerSeries k) :=
  fun i j => tiltedArc (k := k) α
    (localTransverseDerivativeMatrix (k := k) q i j)

private theorem pderiv_t_factor {d : ℕ} (j : Fin d) (r : ℕ)
    (u : MvPowerSeries (Fin (d + 1)) k) :
    MvPowerSeries.pderiv k (Fin.succ j)
        ((MvPowerSeries.X 0 : MvPowerSeries (Fin (d + 1)) k) ^ r * u) =
      (MvPowerSeries.X 0) ^ r * MvPowerSeries.pderiv k (Fin.succ j) u := by
  have hdt : MvPowerSeries.pderiv k (Fin.succ j)
      (MvPowerSeries.X 0 : MvPowerSeries (Fin (d + 1)) k) = 0 := by
    exact MvPowerSeries.pderiv_X_of_ne (Fin.succ_ne_zero j).symm
  have hdtr : MvPowerSeries.pderiv k (Fin.succ j)
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin (d + 1)) k) ^ r) = 0 := by
    rw [MvPowerSeries.pderiv_pow]
    simp [hdt]
  rw [(MvPowerSeries.pderiv k (Fin.succ j)).leibniz]
  simpa [hdtr, smul_eq_mul]

/-- Substitution preserves the constant coefficient of every selected minor.
Thus a minor which is a unit at the closed point remains a unit in `k[[t]]`. -/
theorem tilted_minor_constantCoeff {d : ℕ} {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]
    (α : Fin d → k) (B : Matrix ι κ (MvPowerSeries (Fin (d + 1)) k))
    (rows : κ ↪ ι) :
    PowerSeries.constantCoeff
      (selectedMinor (fun i j => tiltedArc (k := k) α (B i j)) rows).det =
    MvPowerSeries.constantCoeff (selectedMinor B rows).det := by
  have hmap : selectedMinor (fun i j => tiltedArc (k := k) α (B i j)) rows =
      (tiltedArcMap (k := k) α).mapMatrix (selectedMinor B rows) := by
    ext i j
    rfl
  rw [hmap]
  rw [← RingHom.map_det]
  exact tiltedArc_constantCoeff α _

/-- Shared selected-arc data for the generic and constant-correction
axis-lift routes. It performs only bad-locus avoidance and transports the
chart, divisor orders, units, derivative divisibilities, and selected minor. -/
private theorem tiltedArc_divisorData_of_alpha
    {d : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (α : Fin d → k)
    (q : ι → MvPowerSeries (Fin (d + 1)) k)
    (rows : Fin d ↪ ι) (chart zero axis : ι) (a b : ℕ)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
    (hqchart : q chart = 1)
    (hqzero : q zero = (MvPowerSeries.X 0) ^ a * u₀)
    (hu₀ : MvPowerSeries.constantCoeff u₀ ≠ 0)
    (hqaxis : q axis = (MvPowerSeries.X 0) ^ b * u₁)
    (hu₁ : MvPowerSeries.constantCoeff u₁ ≠ 0)
    (hminor : MvPowerSeries.constantCoeff
      (selectedMinor (localTransverseDerivativeMatrix (k := k) q) rows).det ≠ 0) :
    tiltedArc (k := k) α (q chart) = 1 ∧
      (∀ j, tiltedTransverseDerivativeMatrix (k := k) α q chart j = 0) ∧
      (tiltedArc (k := k) α (q zero) =
        (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α u₀) ∧
      PowerSeries.constantCoeff (tiltedArc (k := k) α u₀) ≠ 0 ∧
      (tiltedArc (k := k) α (q axis) =
        (PowerSeries.X : PowerSeries k) ^ b * tiltedArc (k := k) α u₁) ∧
      PowerSeries.constantCoeff (tiltedArc (k := k) α u₁) ≠ 0 ∧
      (∀ j, ∃ w : PowerSeries k,
        tiltedTransverseDerivativeMatrix (k := k) α q zero j =
          (PowerSeries.X : PowerSeries k) ^ a * w) ∧
      (∀ j, ∃ w : PowerSeries k,
        tiltedTransverseDerivativeMatrix (k := k) α q axis j =
          (PowerSeries.X : PowerSeries k) ^ b * w) ∧
      PowerSeries.constantCoeff
        (selectedMinor (tiltedTransverseDerivativeMatrix (k := k) α q) rows).det ≠ 0 := by
  have hqchartₐ : tiltedArc (k := k) α (q chart) = 1 := by
    have h := congrArg (tiltedArcMap (k := k) α) hqchart
    simpa [tiltedArc] using h
  have hZchartₐ : ∀ j,
      tiltedTransverseDerivativeMatrix (k := k) α q chart j = 0 := by
    intro j
    have hderiv := congrArg (MvPowerSeries.pderiv k (Fin.succ j)) hqchart
    have hzero : MvPowerSeries.pderiv k (Fin.succ j) (q chart) = 0 := by
      simpa using hderiv
    have h := congrArg (tiltedArcMap (k := k) α) hzero
    simpa [tiltedTransverseDerivativeMatrix, localTransverseDerivativeMatrix,
      tiltedArc] using h
  have hqzeroₐ : tiltedArc (k := k) α (q zero) =
      (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α u₀ := by
    calc
      tiltedArc (k := k) α (q zero) =
          tiltedArc (k := k) α ((MvPowerSeries.X 0) ^ a * u₀) :=
        congrArg (tiltedArc (k := k) α) hqzero
      _ = (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α u₀ :=
        tiltedArc_t_power_mul α a u₀
  have hu₀ₐ : PowerSeries.constantCoeff (tiltedArc (k := k) α u₀) ≠ 0 := by
    rw [tiltedArc_constantCoeff]
    exact hu₀
  have hqaxisₐ : tiltedArc (k := k) α (q axis) =
      (PowerSeries.X : PowerSeries k) ^ b * tiltedArc (k := k) α u₁ := by
    calc
      tiltedArc (k := k) α (q axis) =
          tiltedArc (k := k) α ((MvPowerSeries.X 0) ^ b * u₁) :=
        congrArg (tiltedArc (k := k) α) hqaxis
      _ = (PowerSeries.X : PowerSeries k) ^ b * tiltedArc (k := k) α u₁ :=
        tiltedArc_t_power_mul α b u₁
  have hu₁ₐ : PowerSeries.constantCoeff (tiltedArc (k := k) α u₁) ≠ 0 := by
    rw [tiltedArc_constantCoeff]
    exact hu₁
  have hZzeroₐ : ∀ j, ∃ w : PowerSeries k,
      tiltedTransverseDerivativeMatrix (k := k) α q zero j =
        (PowerSeries.X : PowerSeries k) ^ a * w := by
    intro j
    refine ⟨tiltedArc (k := k) α
      (MvPowerSeries.pderiv k (Fin.succ j) u₀), ?_⟩
    have hderiv := pderiv_t_factor (k := k) j a u₀
    have hqderiv := congrArg (MvPowerSeries.pderiv k (Fin.succ j)) hqzero
    have hmap := congrArg (tiltedArcMap (k := k) α) (by simpa [hderiv] using hqderiv)
    change tiltedArcMap (k := k) α
        (MvPowerSeries.pderiv k (Fin.succ j) (q zero)) = _
    calc
      _ = tiltedArc (k := k) α
          ((MvPowerSeries.X 0) ^ a * MvPowerSeries.pderiv k (Fin.succ j) u₀) := hmap
      _ = (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α
          (MvPowerSeries.pderiv k (Fin.succ j) u₀) := tiltedArc_t_power_mul α a _
  have hZaxisₐ : ∀ j, ∃ w : PowerSeries k,
      tiltedTransverseDerivativeMatrix (k := k) α q axis j =
        (PowerSeries.X : PowerSeries k) ^ b * w := by
    intro j
    refine ⟨tiltedArc (k := k) α
      (MvPowerSeries.pderiv k (Fin.succ j) u₁), ?_⟩
    have hderiv := pderiv_t_factor (k := k) j b u₁
    have hqderiv := congrArg (MvPowerSeries.pderiv k (Fin.succ j)) hqaxis
    have hmap := congrArg (tiltedArcMap (k := k) α) (by simpa [hderiv] using hqderiv)
    change tiltedArcMap (k := k) α
        (MvPowerSeries.pderiv k (Fin.succ j) (q axis)) = _
    calc
      _ = tiltedArc (k := k) α
          ((MvPowerSeries.X 0) ^ b * MvPowerSeries.pderiv k (Fin.succ j) u₁) := hmap
      _ = (PowerSeries.X : PowerSeries k) ^ b * tiltedArc (k := k) α
          (MvPowerSeries.pderiv k (Fin.succ j) u₁) := tiltedArc_t_power_mul α b _
  have hminorₐ : PowerSeries.constantCoeff
      (selectedMinor (tiltedTransverseDerivativeMatrix (k := k) α q) rows).det ≠ 0 := by
    change PowerSeries.constantCoeff
      (selectedMinor (fun i j => tiltedArc (k := k) α
        (localTransverseDerivativeMatrix (k := k) q i j)) rows).det ≠ 0
    rw [tilted_minor_constantCoeff (k := k) (α := α)
      (B := localTransverseDerivativeMatrix (k := k) q) rows]
    exact hminor
  exact ⟨hqchartₐ, hZchartₐ, hqzeroₐ, hu₀ₐ, hqaxisₐ,
    hu₁ₐ, hZzeroₐ, hZaxisₐ, hminorₐ⟩

private theorem exists_tiltedArc_divisorData
    [Infinite k]
    {d : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (q : ι → MvPowerSeries (Fin (d + 1)) k)
    (bad : MvPowerSeries (Fin (d + 1)) k) (hbad : bad ≠ 0)
    (rows : Fin d ↪ ι) (chart zero axis : ι) (a b : ℕ)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
    (hqchart : q chart = 1)
    (hqzero : q zero = (MvPowerSeries.X 0) ^ a * u₀)
    (hu₀ : MvPowerSeries.constantCoeff u₀ ≠ 0)
    (hqaxis : q axis = (MvPowerSeries.X 0) ^ b * u₁)
    (hu₁ : MvPowerSeries.constantCoeff u₁ ≠ 0)
    (hminor : MvPowerSeries.constantCoeff
      (selectedMinor (localTransverseDerivativeMatrix (k := k) q) rows).det ≠ 0) :
    ∃ α : Fin d → k,
      tiltedArc (k := k) α bad ≠ 0 ∧
      tiltedArc (k := k) α (q chart) = 1 ∧
      (∀ j, tiltedTransverseDerivativeMatrix (k := k) α q chart j = 0) ∧
      (tiltedArc (k := k) α (q zero) =
        (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α u₀) ∧
      PowerSeries.constantCoeff (tiltedArc (k := k) α u₀) ≠ 0 ∧
      (tiltedArc (k := k) α (q axis) =
        (PowerSeries.X : PowerSeries k) ^ b * tiltedArc (k := k) α u₁) ∧
      PowerSeries.constantCoeff (tiltedArc (k := k) α u₁) ≠ 0 ∧
      (∀ j, ∃ w : PowerSeries k,
        tiltedTransverseDerivativeMatrix (k := k) α q zero j =
          (PowerSeries.X : PowerSeries k) ^ a * w) ∧
      (∀ j, ∃ w : PowerSeries k,
        tiltedTransverseDerivativeMatrix (k := k) α q axis j =
          (PowerSeries.X : PowerSeries k) ^ b * w) ∧
      PowerSeries.constantCoeff
        (selectedMinor (tiltedTransverseDerivativeMatrix (k := k) α q) rows).det ≠ 0 := by
  obtain ⟨α, havoidPUnit⟩ :=
    exists_tiltedArcPointPUnit_avoidance (k := k) bad hbad
  have havoid := tiltedArc_ne_zero_of_avoidance (k := k) α bad havoidPUnit
  obtain ⟨hqchartₐ, hZchartₐ, hqzeroₐ, hu₀ₐ, hqaxisₐ,
      hu₁ₐ, hZzeroₐ, hZaxisₐ, hminorₐ⟩ :=
    tiltedArc_divisorData_of_alpha (k := k) α q rows chart zero axis a b
      u₀ u₁ hqchart hqzero hu₀ hqaxis hu₁ hminor
  exact ⟨α, havoid, hqchartₐ, hZchartₐ, hqzeroₐ, hu₀ₐ,
    hqaxisₐ, hu₁ₐ, hZzeroₐ, hZaxisₐ, hminorₐ⟩

/-- A conditional closed-point tilted-arc producer.  The premises are exactly
local power-series data: the chart map `q`, its genuine formal transverse
partial derivatives, strict divisor-axis factors, and a full-rank transverse
minor at the closed point.  The selected arc avoids the supplied nonzero
bad-locus series; substitution preserves the unit constants and minor.  The
canonical `FormalDivisorAxisLift` then constructs the correction, normalized
tangent column, split matrix, and axis conormal. -/
theorem exists_tilted_local_axis_lift
    [Infinite k] [CharZero k]
    {d : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (q : ι → MvPowerSeries (Fin (d + 1)) k)
    (bad : MvPowerSeries (Fin (d + 1)) k) (hbad : bad ≠ 0)
    (rows : Fin d ↪ ι) (chart zero axis : ι) (a b : ℕ)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
    (hqchart : q chart = 1)
    (ha : 0 < a) (hab : a < b)
    (hqzero : q zero = (MvPowerSeries.X 0) ^ a * u₀)
    (hu₀ : MvPowerSeries.constantCoeff u₀ ≠ 0)
    (hqaxis : q axis = (MvPowerSeries.X 0) ^ b * u₁)
    (hu₁ : MvPowerSeries.constantCoeff u₁ ≠ 0)
    (hminor : MvPowerSeries.constantCoeff
      (selectedMinor (localTransverseDerivativeMatrix (k := k) q) rows).det ≠ 0) :
    ∃ α : Fin d → k,
      tiltedArc (k := k) α bad ≠ 0 ∧
      (tiltedArc (k := k) α (q zero) =
        (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α u₀) ∧
      PowerSeries.constantCoeff (tiltedArc (k := k) α u₀) ≠ 0 ∧
      (tiltedArc (k := k) α (q axis) =
        (PowerSeries.X : PowerSeries k) ^ b * tiltedArc (k := k) α u₁) ∧
      PowerSeries.constantCoeff (tiltedArc (k := k) α u₁) ≠ 0 ∧
      PowerSeries.constantCoeff
        (selectedMinor (tiltedTransverseDerivativeMatrix (k := k) α q) rows).det ≠ 0 ∧
      ∃ (lambda : Fin d → PowerSeries k) (c : ℕ)
        (tau : ι → PowerSeries k)
        (C : Matrix (FormalTangentColumn (Fin d)) ι (PowerSeries k))
        (ell : ι → PowerSeries k),
        lambda = correctionCoefficients (tiltedTransverseDerivativeMatrix (k := k) α q) rows
          (fun i => PowerSeries.derivative k (tiltedArc (k := k) α (q i))) ∧
        (∀ j,
          PowerSeries.derivative k (tiltedArc (k := k) α (q (rows j))) =
            (tiltedTransverseDerivativeMatrix (k := k) α q).mulVec lambda (rows j)) ∧
        tau chart = 0 ∧
        (∀ j, tau (rows j) = 0) ∧
        c ≤ a - 1 ∧
        (∀ i,
          PowerSeries.derivative k (tiltedArc (k := k) α (q i)) -
              (tiltedTransverseDerivativeMatrix (k := k) α q).mulVec lambda i =
            (PowerSeries.X : PowerSeries k) ^ c * tau i) ∧
        (∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) ∧
        PowerSeries.constantCoeff (tau axis) = 0 ∧
        (∀ column : FormalTangentColumn (Fin d),
          PowerSeries.constantCoeff
            (formalTangentMatrix (fun i => tiltedArc (k := k) α (q i))
              (tiltedTransverseDerivativeMatrix (k := k) α q) tau axis column) = 0) ∧
        C * formalTangentMatrix (fun i => tiltedArc (k := k) α (q i))
            (tiltedTransverseDerivativeMatrix (k := k) α q) tau = 1 ∧
        rowMul ell (formalTangentMatrix (fun i => tiltedArc (k := k) α (q i))
            (tiltedTransverseDerivativeMatrix (k := k) α q) tau) = 0 ∧
        residueColumn ell = axisRow (k := k) axis := by
  obtain ⟨α, havoid, hqchartₐ, hZchartₐ, hqzeroₐ, hu₀ₐ,
      hqaxisₐ, hu₁ₐ, hZzeroₐ, hZaxisₐ, hminorₐ⟩ :=
    exists_tiltedArc_divisorData (k := k) q bad hbad rows chart zero axis a b
      u₀ u₁ hqchart hqzero hu₀ hqaxis hu₁ hminor
  let qₐ : ι → PowerSeries k := fun i => tiltedArc (k := k) α (q i)
  let Zₐ : Matrix ι (Fin d) (PowerSeries k) :=
    tiltedTransverseDerivativeMatrix (k := k) α q
  have hlift := exists_formalDivisorAxisLift qₐ Zₐ rows chart zero axis
    a b (tiltedArc (k := k) α u₀) (tiltedArc (k := k) α u₁)
    hqchartₐ hZchartₐ ha hab hqzeroₐ hu₀ₐ hZzeroₐ hqaxisₐ hZaxisₐ hminorₐ
  rcases hlift with ⟨lambda, c, tau, C, ell, hlambda, hselected,
    htauchart, htauselected, hc, hfactor, hprimitive, haxis,
    haxiscolumns, hCB, hell, hellres⟩
  exact ⟨α, havoid, hqzeroₐ, hu₀ₐ, hqaxisₐ, hu₁ₐ, hminorₐ,
    lambda, c, tau, C, ell,
    (by simpa [qₐ, Zₐ] using hlambda),
    (by simpa [qₐ, Zₐ] using hselected),
    htauchart, htauselected, hc, hfactor, hprimitive, haxis,
    (by simpa [qₐ, Zₐ] using haxiscolumns), hCB, hell, hellres⟩

/-- A transverse formal coordinate maps to its constant tilt coefficient
multiplied by `t`. -/
@[simp] theorem tiltedArc_X_succ {d : ℕ} (α : Fin d → k) (j : Fin d) :
    tiltedArc (k := k) α (MvPowerSeries.X (Fin.succ j)) =
      PowerSeries.C (α j) * PowerSeries.X := by
  change MvPowerSeries.rename (Equiv.equivPUnit Unit).symm
      ((MvPowerSeries.substAlgHom (tiltedArcHasSubstPUnit (k := k) α))
        (MvPowerSeries.X (Fin.succ j))) = _
  rw [MvPowerSeries.substAlgHom_X]
  change MvPowerSeries.rename (Equiv.equivPUnit Unit).symm
    (MvPowerSeries.C (α j) * MvPowerSeries.X (PUnit.unit : PUnit.{1})) = _
  rw [map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
  change PowerSeries.C (α j) * PowerSeries.X = _
  rfl

@[simp] theorem tiltedArc_C {d : ℕ} (α : Fin d → k) (b : k) :
    tiltedArc (k := k) α (MvPowerSeries.C b) = PowerSeries.C b := by
  simp [tiltedArc, tiltedArcMap, tiltedArcMapPUnit, punitToPowerSeries]
  rfl

/-- In the selected-coordinate chart, the tilted selected coordinate is
`β_j + α_j t`; its transverse derivative row is the identity and its raw
`t`-derivative is `α_j`. -/
theorem selected_coordinate_rows_on_tilted_arc
    {d : ℕ} {ι : Type*} (q : ι → MvPowerSeries (Fin (d + 1)) k)
    (rows : Fin d ↪ ι) (β α : Fin d → k)
    (hrows : ∀ j, q (rows j) =
      MvPowerSeries.C (β j) + MvPowerSeries.X (Fin.succ j)) :
    (∀ j, tiltedArc (k := k) α (q (rows j)) =
      PowerSeries.C (β j) + PowerSeries.C (α j) * PowerSeries.X) ∧
    (∀ j l, tiltedTransverseDerivativeMatrix (k := k) α q (rows j) l =
      if j = l then 1 else 0) ∧
    (∀ j, PowerSeries.derivative k
      (tiltedArc (k := k) α (q (rows j))) = PowerSeries.C (α j)) := by
  have hC (b : k) : (tiltedArcMap (k := k) α) (MvPowerSeries.C b) =
      PowerSeries.C b := tiltedArc_C (k := k) α b
  have hX (j : Fin d) : (tiltedArcMap (k := k) α)
      (MvPowerSeries.X (Fin.succ j)) = PowerSeries.C (α j) * PowerSeries.X :=
    tiltedArc_X_succ (k := k) α j
  have hrowArc (j : Fin d) : tiltedArc (k := k) α (q (rows j)) =
      PowerSeries.C (β j) + PowerSeries.C (α j) * PowerSeries.X := by
    have h := congrArg (tiltedArcMap (k := k) α) (hrows j)
    change (tiltedArcMap (k := k) α) (q (rows j)) =
      (tiltedArcMap (k := k) α) (MvPowerSeries.C (β j) +
        MvPowerSeries.X (Fin.succ j)) at h
    rw [map_add, hC, hX] at h
    exact h
  have hderiv (j l : Fin d) :
      MvPowerSeries.pderiv k (Fin.succ l) (q (rows j)) =
        if j = l then (1 : MvPowerSeries (Fin (d + 1)) k) else 0 := by
    rw [hrows j]
    by_cases hjl : j = l
    · subst l
      simp
    · have hne : Fin.succ j ≠ Fin.succ l := by
        intro h
        exact hjl ((Fin.succ_injective d) h)
      simp [hjl, MvPowerSeries.pderiv_X_of_ne, hne]
  constructor
  · exact hrowArc
  constructor
  · intro j l
    change tiltedArc (k := k) α
      (MvPowerSeries.pderiv k (Fin.succ l) (q (rows j))) = _
    rw [hderiv j l]
    by_cases hjl : j = l <;> simp [tiltedArc, hjl]
  · intro j
    rw [hrowArc j]
    rw [map_add, (PowerSeries.derivative k).leibniz]
    simp

/-- The selected-coordinate output for one fixed tilted arc. This is only an
abbreviation for the resulting propositions, not an assumed package. -/
abbrev SelectedCoordinateAxisLiftData
    {d : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (q : ι → MvPowerSeries (Fin (d + 1)) k)
    (rows : Fin d ↪ ι) (chart zero axis : ι) (a b : ℕ)
    (β α : Fin d → k)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k) : Prop :=
    (tiltedArc (k := k) α (q zero) =
      (PowerSeries.X : PowerSeries k) ^ a * tiltedArc (k := k) α u₀) ∧
    PowerSeries.constantCoeff (tiltedArc (k := k) α u₀) ≠ 0 ∧
    (tiltedArc (k := k) α (q axis) =
      (PowerSeries.X : PowerSeries k) ^ b * tiltedArc (k := k) α u₁) ∧
    PowerSeries.constantCoeff (tiltedArc (k := k) α u₁) ≠ 0 ∧
    (∀ j, tiltedArc (k := k) α (q (rows j)) =
      PowerSeries.C (β j) + PowerSeries.C (α j) * PowerSeries.X) ∧
    (∀ j l, tiltedTransverseDerivativeMatrix (k := k) α q (rows j) l =
      if j = l then 1 else 0) ∧
    (selectedMinor (tiltedTransverseDerivativeMatrix (k := k) α q) rows).det = 1 ∧
    ∃ (c : ℕ) (tau : ι → PowerSeries k)
      (C : Matrix (FormalTangentColumn (Fin d)) ι (PowerSeries k))
      (ell : ι → PowerSeries k),
      c ≤ a - 1 ∧
      (∀ j, PowerSeries.derivative k
        (tiltedArc (k := k) α (q (rows j))) = PowerSeries.C (α j)) ∧
      tau chart = 0 ∧
      (∀ j, tau (rows j) = 0) ∧
      (∀ i, PowerSeries.derivative k (tiltedArc (k := k) α (q i)) -
        (tiltedTransverseDerivativeMatrix (k := k) α q).mulVec
          (fun j => PowerSeries.C (α j)) i =
        (PowerSeries.X : PowerSeries k) ^ c * tau i) ∧
      (∃ i, PowerSeries.constantCoeff (tau i) ≠ 0) ∧
      PowerSeries.constantCoeff (tau axis) = 0 ∧
      (∀ column : FormalTangentColumn (Fin d),
        PowerSeries.constantCoeff
          (formalTangentMatrix (fun i => tiltedArc (k := k) α (q i))
            (tiltedTransverseDerivativeMatrix (k := k) α q) tau axis column) = 0) ∧
      C * formalTangentMatrix (fun i => tiltedArc (k := k) α (q i))
          (tiltedTransverseDerivativeMatrix (k := k) α q) tau = 1 ∧
      rowMul ell (formalTangentMatrix (fun i => tiltedArc (k := k) α (q i))
          (tiltedTransverseDerivativeMatrix (k := k) α q) tau) = 0 ∧
      residueColumn ell = axisRow (k := k) axis

/-- For a specified tilt `α`, centered selected coordinates force the
transverse minor to be the identity. The supplied ground-field correction is
`α`; this theorem does not choose an arc or solve a power-series system. -/
theorem tilted_local_axis_lift_of_selected_coordinate_rows_on_arc
    [CharZero k]
    {d : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (q : ι → MvPowerSeries (Fin (d + 1)) k)
    (rows : Fin d ↪ ι) (chart zero axis : ι) (a b : ℕ)
    (β α : Fin d → k)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
    (hqchart : q chart = 1)
    (ha : 0 < a) (hab : a < b)
    (hqzero : q zero = (MvPowerSeries.X 0) ^ a * u₀)
    (hu₀ : MvPowerSeries.constantCoeff u₀ ≠ 0)
    (hqaxis : q axis = (MvPowerSeries.X 0) ^ b * u₁)
    (hu₁ : MvPowerSeries.constantCoeff u₁ ≠ 0)
    (hrows : ∀ j, q (rows j) =
      MvPowerSeries.C (β j) + MvPowerSeries.X (Fin.succ j)) :
    SelectedCoordinateAxisLiftData (k := k) q rows chart zero axis a b β α u₀ u₁ := by
  have hlocalEntry : ∀ j l,
      localTransverseDerivativeMatrix (k := k) q (rows j) l =
        if j = l then 1 else 0 := by
    intro j l
    change MvPowerSeries.pderiv k (Fin.succ l) (q (rows j)) = _
    rw [hrows j]
    by_cases hjl : j = l
    · subst l
      simp
    · have hne : Fin.succ j ≠ Fin.succ l := by
        intro h
        exact hjl ((Fin.succ_injective d) h)
      simp [hjl, MvPowerSeries.pderiv_X_of_ne, hne]
  have hlocalMinor : selectedMinor
      (localTransverseDerivativeMatrix (k := k) q) rows = 1 := by
    ext j l n
    change MvPowerSeries.coeff n
      (localTransverseDerivativeMatrix (k := k) q (rows j) l) =
        MvPowerSeries.coeff n
          (if j = l then (1 : MvPowerSeries (Fin (d + 1)) k) else 0)
    rw [hlocalEntry j l]
  have hminor : MvPowerSeries.constantCoeff
      (selectedMinor (localTransverseDerivativeMatrix (k := k) q) rows).det ≠ 0 := by
    rw [hlocalMinor]
    simp
  obtain ⟨hqchartₐ, hZchartₐ, hqzeroₐ, hu₀ₐ,
      hqaxisₐ, hu₁ₐ, hZzeroₐ, hZaxisₐ, hminorₐ⟩ :=
    tiltedArc_divisorData_of_alpha (k := k) α q rows chart zero axis a b
      u₀ u₁ hqchart hqzero hu₀ hqaxis hu₁ hminor
  let qₐ : ι → PowerSeries k := fun i => tiltedArc (k := k) α (q i)
  let Zₐ : Matrix ι (Fin d) (PowerSeries k) :=
    tiltedTransverseDerivativeMatrix (k := k) α q
  have hcoords := selected_coordinate_rows_on_tilted_arc
    (k := k) q rows β α hrows
  have hminorMatrix : selectedMinor Zₐ rows = 1 := by
    ext j l n
    change PowerSeries.coeff n
      (tiltedTransverseDerivativeMatrix (k := k) α q (rows j) l) =
        PowerSeries.coeff n (if j = l then (1 : PowerSeries k) else 0)
    rw [hcoords.2.1 j l]
  have hdet : (selectedMinor Zₐ rows).det = 1 := by
    rw [hminorMatrix]
    simp
  let lambda : Fin d → PowerSeries k := fun j => PowerSeries.C (α j)
  have hselected : ∀ j, PowerSeries.derivative k (qₐ (rows j)) =
      Zₐ.mulVec lambda (rows j) := by
    have hmul : (selectedMinor Zₐ rows).mulVec lambda = lambda := by
      rw [hminorMatrix]
      simp
    intro j
    have hrow : Zₐ.mulVec lambda (rows j) = lambda j := by
      change (selectedMinor Zₐ rows).mulVec lambda j = lambda j
      exact congrFun hmul j
    rw [hcoords.2.2 j, hrow]
  rcases exists_formalDivisorAxisLift_of_selected_correction
      (q := qₐ) (Z := Zₐ) rows chart zero axis a b
      (tiltedArc (k := k) α u₀) (tiltedArc (k := k) α u₁) lambda
      hqchartₐ hZchartₐ ha hab hqzeroₐ hu₀ₐ hZzeroₐ hqaxisₐ hZaxisₐ
      hselected hminorₐ with
    ⟨c, tau, C, ell, htauchart, htauselected, hc, hfactor,
      hprimitive, haxis, haxiscolumns, hCB, hell, hellres⟩
  refine ⟨hqzeroₐ, hu₀ₐ, hqaxisₐ, hu₁ₐ, hcoords.1,
    hcoords.2.1, hdet, ?_⟩
  refine ⟨c, tau, C, ell, hc, hcoords.2.2, htauchart,
    htauselected, ?_, hprimitive, haxis, ?_, hCB, hell, hellres⟩
  · intro i
    simpa [lambda] using hfactor i
  · simpa [qₐ, Zₐ] using haxiscolumns


/-- Choose one tilt avoiding the nonzero bad-locus series and delegate all
geometric construction to the fixed-arc theorem above. -/
theorem exists_tilted_local_axis_lift_of_selected_coordinate_rows
    [Infinite k] [CharZero k]
    {d : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (q : ι → MvPowerSeries (Fin (d + 1)) k)
    (bad : MvPowerSeries (Fin (d + 1)) k) (hbad : bad ≠ 0)
    (rows : Fin d ↪ ι) (chart zero axis : ι) (a b : ℕ)
    (β : Fin d → k)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
    (hqchart : q chart = 1)
    (ha : 0 < a) (hab : a < b)
    (hqzero : q zero = (MvPowerSeries.X 0) ^ a * u₀)
    (hu₀ : MvPowerSeries.constantCoeff u₀ ≠ 0)
    (hqaxis : q axis = (MvPowerSeries.X 0) ^ b * u₁)
    (hu₁ : MvPowerSeries.constantCoeff u₁ ≠ 0)
    (hrows : ∀ j, q (rows j) =
      MvPowerSeries.C (β j) + MvPowerSeries.X (Fin.succ j)) :
    ∃ α : Fin d → k,
      tiltedArc (k := k) α bad ≠ 0 ∧
      SelectedCoordinateAxisLiftData (k := k) q rows chart zero axis a b β α u₀ u₁ := by
  obtain ⟨α, havoidPUnit⟩ :=
    exists_tiltedArcPointPUnit_avoidance (k := k) bad hbad
  have havoid := tiltedArc_ne_zero_of_avoidance (k := k) α bad havoidPUnit
  exact ⟨α, havoid,
    tilted_local_axis_lift_of_selected_coordinate_rows_on_arc
      (k := k) q rows chart zero axis a b β α u₀ u₁
      hqchart ha hab hqzero hu₀ hqaxis hu₁ hrows⟩

#print axioms tiltedArc_constantCoeff
#print axioms tilted_minor_constantCoeff
#print axioms exists_tilted_local_axis_lift
#print axioms tilted_local_axis_lift_of_selected_coordinate_rows_on_arc
#print axioms exists_tilted_local_axis_lift_of_selected_coordinate_rows

end

end Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
