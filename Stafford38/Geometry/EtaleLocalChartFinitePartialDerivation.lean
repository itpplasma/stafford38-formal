module
public import Stafford38.Geometry.EtaleCotangentBasis
public import Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
public import Mathlib.RingTheory.MvPowerSeries.Derivative

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Full chart partials before restriction to a tilted arc

The statements here are conditional on an already-given formally-etale
polynomial chart.  The ambient projective-coordinate index is independent of
the local chart dimension.  In particular, all transverse partials are
computed in the multivariate completion before using the existing tilted-arc
map.
-/

namespace Stafford38.Geometry.EtaleLocalChartFinitePartialDerivation

open Module
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift

noncomputable section

universe u v w

variable {k : Type u} [Field k] {d : ℕ} {B : Type v} [CommRing B]
variable [Algebra (MvPolynomial (Fin (d + 1)) k) B] [Algebra k B]
  [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) B]
  [Algebra.FormallyEtale (MvPolynomial (Fin (d + 1)) k) B]

local notation "R" => MvPolynomial (Fin (d + 1)) k

/-- The `B`-valued partial derivation dual to a parameter of an existing
formally-etale polynomial chart. -/
noncomputable def parameterDerivation (i : Fin (d + 1)) : Derivation k B B :=
  Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
    (k := k) (σ := Fin (d + 1)) (B := B) (L := B) i

theorem parameterDerivation_apply_parameter (i j : Fin (d + 1)) :
    parameterDerivation (k := k) (d := d) (B := B) i
      (algebraMap R B (MvPolynomial.X j)) = if j = i then (1 : B) else 0 := by
  exact Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation_apply_parameter
    (k := k) (σ := Fin (d + 1)) (B := B) (L := B) i j

/-- Extending a precompletion parameter derivation to a field-valued point
agrees with the existing Kähler-basis coordinate derivation.  The equality is
deduced from the checked uniqueness theorem using all polynomial parameter
values. -/
theorem parameterDerivation_scalarExtension_eq_coordinate
    {L : Type w} [CommRing L] [Algebra B L] [Algebra k L]
    [IsScalarTower k B L] (i : Fin (d + 1)) :
    (Algebra.linearMap B L).compDer
        (parameterDerivation (k := k) (d := d) (B := B) i) =
      Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Fin (d + 1)) (B := B) (L := L) i := by
  let D : Derivation k B L := (Algebra.linearMap B L).compDer
    (parameterDerivation (k := k) (d := d) (B := B) i)
  have hD : ∀ j, D (algebraMap R B (MvPolynomial.X j)) =
      if j = i then (1 : L) else 0 := by
    intro j
    change algebraMap B L
      (parameterDerivation (k := k) (d := d) (B := B) i
        (algebraMap R B (MvPolynomial.X j))) = _
    rw [parameterDerivation_apply_parameter]
    simp
  change D = _
  calc
    D = Stafford38.Geometry.EtaleCotangentBasis.derivationFromValues
        (k := k) (σ := Fin (d + 1)) (B := B) (L := L)
        (fun j => D (algebraMap R B (MvPolynomial.X j))) :=
      (Stafford38.Geometry.EtaleCotangentBasis.derivation_eq_from_parameter_values D).symm
    _ = Stafford38.Geometry.EtaleCotangentBasis.derivationFromValues
        (k := k) (σ := Fin (d + 1)) (B := B) (L := L)
        (fun j => if j = i then (1 : L) else 0) := by
      congr 1
      funext j
      exact hD j
    _ = Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Fin (d + 1)) (B := B) (L := L) i := rfl

/-- A selected row equal to its centered chart coordinate has transverse
partials equal to the identity and distinguished-parameter partial zero.
The map `rows` may land in any ambient `Fin (n+1)`; no dimension equality with
`d+1` is assumed. -/
theorem selectedRow_parameterDerivatives {n : ℕ}
    (q : Fin (n + 1) → B) (rows : Fin d ↪ Fin (n + 1))
    (β : Fin d → k)
    (hq : ∀ j, q (rows j) = algebraMap k B (β j) +
      algebraMap R B (MvPolynomial.X j.succ)) :
    (∀ i j, parameterDerivation (k := k) (d := d) (B := B) i.succ
        (q (rows j)) = if i = j then (1 : B) else 0) ∧
      (∀ j, parameterDerivation (k := k) (d := d) (B := B) 0
        (q (rows j)) = 0) := by
  constructor
  · intro i j
    rw [hq j]
    simp [Derivation.map_add, parameterDerivation_apply_parameter, eq_comm]
  · intro j
    rw [hq j]
    simp [Derivation.map_add, parameterDerivation_apply_parameter]

/-- The same selected-row formula in the full multivariate completion. -/
theorem selectedRow_completedPartials {n : ℕ}
    (q : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (rows : Fin d ↪ Fin (n + 1)) (β : Fin d → k)
    (hq : ∀ j, q (rows j) = MvPowerSeries.C (β j) +
      MvPowerSeries.X j.succ) :
    (∀ i j, MvPowerSeries.pderiv i.succ (q (rows j)) =
        if i = j then 1 else 0) ∧
      (∀ j, MvPowerSeries.pderiv 0 (q (rows j)) = 0) := by
  constructor
  · intro i j
    rw [hq j]
    by_cases h : i = j
    · subst j
      simp
    · have h' : j.succ ≠ i.succ := by simpa using Ne.symm h
      simp [h, MvPowerSeries.pderiv_X_of_ne, h']
  · intro j
    rw [hq j]
    simp

/-- The canonical tilted arc sends a selected affine chart row to
`β_j + α_j t`, so its first derivative is `α_j`. -/
theorem tiltedArc_X_succ (α : Fin d → k) (j : Fin d) :
    tiltedArc (k := k) α (MvPowerSeries.X j.succ) =
      PowerSeries.C (α j) * PowerSeries.X := by
  change MvPowerSeries.rename (Equiv.equivPUnit Unit).symm
    ((MvPowerSeries.substAlgHom
      (tiltedArcHasSubstPUnit (k := k) α)) (MvPowerSeries.X j.succ)) = _
  rw [MvPowerSeries.substAlgHom_X]
  change MvPowerSeries.rename (Equiv.equivPUnit Unit).symm
    (MvPowerSeries.C (tiltedArcCoefficients (k := k) α j.succ) *
      MvPowerSeries.X (PUnit.unit : PUnit.{1})) = _
  rw [map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
  rw [tiltedArcCoefficients_succ]
  rfl

theorem tiltedArc_derivative_parameter (α : Fin d → k) (i : Fin (d + 1)) :
    PowerSeries.derivative (R := k) (tiltedArc (k := k) α (MvPowerSeries.X i)) =
      PowerSeries.C (tiltedArcCoefficients (k := k) α i) := by
  cases i using Fin.cases with
  | zero =>
      rw [tiltedArc_X_t]
      simp
  | succ j =>
      rw [tiltedArc_X_succ]
      simp only [tiltedArcCoefficients_succ, Derivation.leibniz,
        PowerSeries.derivative_C, PowerSeries.derivative_X]
      simp

theorem selectedRow_tiltedArc_derivative {n : ℕ}
    (q : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (rows : Fin d ↪ Fin (n + 1)) (β α : Fin d → k)
    (hq : ∀ j, q (rows j) = MvPowerSeries.C (β j) +
      MvPowerSeries.X j.succ) :
    ∀ j, PowerSeries.derivative (R := k)
      (tiltedArc (k := k) α (q (rows j))) = PowerSeries.C (α j) := by
  intro j
  rw [hq j]
  have hx := tiltedArc_X_succ (k := k) α j
  have hC : tiltedArc (k := k) α (MvPowerSeries.C (β j)) =
      PowerSeries.C (β j) := by
    change punitToPowerSeries (k := k)
      (tiltedArcMapPUnit (k := k) α (MvPowerSeries.C (β j))) = _
    have hCP : tiltedArcMapPUnit (k := k) α (MvPowerSeries.C (β j)) =
        MvPowerSeries.C (β j) := by
      simp [tiltedArcMapPUnit]
    rw [hCP]
    change MvPowerSeries.rename (Equiv.equivPUnit Unit).symm
      (MvPowerSeries.C (β j)) = _
    rw [MvPowerSeries.rename_C]
    rfl
  change PowerSeries.derivative (R := k)
    (tiltedArcMap (k := k) α
      (MvPowerSeries.C (β j) + MvPowerSeries.X j.succ)) = _
  rw [(tiltedArcMap (k := k) α).map_add]
  change PowerSeries.derivative (R := k)
    (tiltedArc (k := k) α (MvPowerSeries.C (β j)) +
      tiltedArc (k := k) α (MvPowerSeries.X j.succ)) = _
  rw [hC, hx]
  simp only [Derivation.map_add, PowerSeries.derivative_C,
    Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_X,
    zero_add]
  simp

end

end Stafford38.Geometry.EtaleLocalChartFinitePartialDerivation
