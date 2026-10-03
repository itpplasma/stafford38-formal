module
public import Stafford38.Geometry.PrescribedCompletionDerivationCommutation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# The tilted-arc derivative in the actual Option-indexed local chart

The prescribed projective chart is indexed by `Option (Fin d)`.  This file
expresses the derivative of its canonical tilted arc directly in those
coordinate derivations, using the already checked Kähler-basis decomposition
of derivations.
-/

namespace Stafford38.Geometry.ActualOptionArcDerivative

open Stafford38.Geometry.EtaleLocalChartFinitePartialDerivation
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.PrescribedCompletionDerivationCommutation
open Stafford38.Geometry.PrescribedAffineResidueCompletion

noncomputable section

universe u v

variable {k : Type u} [Field k] {d : ℕ} {A : Type v} [CommRing A]
variable [Algebra (MvPolynomial (Option (Fin d)) k) A] [Algebra k A]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) A]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) A]

local notation "R" => MvPolynomial (Option (Fin d)) k

/-- Any one-variable power-series arc whose values on the Option-chart
parameters have the indicated first-order coefficients differentiates by the
corresponding weighted sum of the canonical coordinate derivations. -/
theorem arc_derivative_eq_option_coordinate_sum
    {T : Type*} [CommRing T] [Algebra R T] [Algebra k T]
    [IsScalarTower k R T] [Algebra.FormallyEtale R T]
    (φ : T →ₐ[k] PowerSeries k) (α : Fin d → k)
    (β : Option (Fin d) → k)
    (hcoord : ∀ j : Option (Fin d),
      φ (algebraMap R T (MvPolynomial.X j)) =
        PowerSeries.C (β j) +
          PowerSeries.C (j.elim 1 α) * PowerSeries.X)
    (b : T) :
    PowerSeries.derivative (R := k) (φ b) =
      φ (EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Option (Fin d)) (B := T) (L := T) none b) +
        ∑ j : Fin d, PowerSeries.C (α j) *
          φ (EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := Option (Fin d)) (B := T) (L := T) (some j) b) := by
  letI : Algebra T (PowerSeries k) := φ.toRingHom.toAlgebra
  letI : IsScalarTower k T (PowerSeries k) :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      change algebraMap k (PowerSeries k) c = φ (algebraMap k T c)
      exact (φ.commutes c).symm)
  let φlin : T →ₗ[T] PowerSeries k :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r x => by
        change φ (r * x) = φ r * φ x
        exact φ.map_mul r x }
  let Dleft : Derivation k T (PowerSeries k) :=
    (PowerSeries.derivative (R := k)).compAlgebraMap T
  let Dright : Derivation k T (PowerSeries k) :=
    (φlin.compDer (EtaleCotangentBasis.coordinateDerivation
      (k := k) (σ := Option (Fin d)) (B := T) (L := T) none)) +
      ∑ j : Fin d, PowerSeries.C (α j) •
        (φlin.compDer (EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := T) (L := T) (some j)))
  have hleft (j : Option (Fin d)) :
      Dleft (algebraMap R T (MvPolynomial.X j)) = PowerSeries.C (j.elim 1 α) := by
    change PowerSeries.derivative (R := k)
      (φ (algebraMap R T (MvPolynomial.X j))) = _
    rw [hcoord j]
    cases j <;> simp [Derivation.map_add, Derivation.leibniz]
  have hright (j : Option (Fin d)) :
      Dright (algebraMap R T (MvPolynomial.X j)) = PowerSeries.C (j.elim 1 α) := by
    change (Derivation.coeFnAddMonoidHom
      ((φlin.compDer (EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Option (Fin d)) (B := T) (L := T) none)) +
        ∑ i : Fin d, PowerSeries.C (α i) •
          (φlin.compDer (EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := Option (Fin d)) (B := T) (L := T) (some i)))))
      (algebraMap R T (MvPolynomial.X j)) = _
    rw [map_add, map_sum]
    cases j with
    | none => simp [φlin,
        EtaleCotangentBasis.coordinateDerivation_apply_parameter]
    | some j => simp [φlin, eq_comm,
        EtaleCotangentBasis.coordinateDerivation_apply_parameter]
  have hderiv : Dleft = Dright := by
    calc
      Dleft = EtaleCotangentBasis.derivationFromValues
          (k := k) (σ := Option (Fin d)) (B := T) (L := PowerSeries k)
          (fun j => Dleft (algebraMap R T (MvPolynomial.X j))) :=
        (EtaleCotangentBasis.derivation_eq_from_parameter_values Dleft).symm
      _ = EtaleCotangentBasis.derivationFromValues
          (k := k) (σ := Option (Fin d)) (B := T) (L := PowerSeries k)
          (fun j => Dright (algebraMap R T (MvPolynomial.X j))) := by
        congr 1
        funext j
        rw [hleft j, hright j]
      _ = Dright := EtaleCotangentBasis.derivation_eq_from_parameter_values Dright
  calc
    PowerSeries.derivative (R := k) (φ b) = Dleft b := rfl
    _ = Dright b := congrArg (fun D : Derivation k T (PowerSeries k) => D b) hderiv
    _ = φ (EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := T) (L := T) none b) +
        ∑ j : Fin d, PowerSeries.C (α j) *
          φ (EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := Option (Fin d)) (B := T) (L := T) (some j) b) := by
      change (Derivation.coeFnAddMonoidHom
        ((φlin.compDer (EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := T) (L := T) none)) +
          ∑ j : Fin d, PowerSeries.C (α j) •
            (φlin.compDer (EtaleCotangentBasis.coordinateDerivation
              (k := k) (σ := Option (Fin d)) (B := T) (L := T) (some j)))) b) = _
      rw [map_add, map_sum]
      simp [φlin]

/-- The actual prescribed completion, reindexed by `Fin.succEquiv`, and
restricted along the canonical tilted arc obeys the Option-coordinate
derivative formula. -/
theorem localToFinSuccArc_derivative_eq_option_coordinate_sum
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (α : Fin d → k) (b : Localization.AtPrime M) :
    PowerSeries.derivative (R := k)
      (tiltedArc (k := k) α
        (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM b)) =
      tiltedArc (k := k) α
        (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
          (EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := Option (Fin d)) (B := Localization.AtPrime M)
            (L := Localization.AtPrime M) none b)) +
        ∑ j : Fin d, PowerSeries.C (α j) *
          tiltedArc (k := k) α
            (localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
              (EtaleCotangentBasis.coordinateDerivation
                (k := k) (σ := Option (Fin d)) (B := Localization.AtPrime M)
                (L := Localization.AtPrime M) (some j) b)) := by
  let T := Localization.AtPrime M
  let Φ := localToFinSuccPowerSeries (k := k) (B := A) (d := d) M eM
  let φ : T →ₐ[k] PowerSeries k :=
    { toRingHom := (tiltedArcMap (k := k) α).comp Φ.toRingHom
      commutes' := by
        intro c
        calc
          (tiltedArcMap (k := k) α).comp Φ.toRingHom (algebraMap k T c) =
              tiltedArcMap (k := k) α (MvPowerSeries.C c) := by
            change tiltedArcMap (k := k) α (Φ (algebraMap k T c)) = _
            rw [Φ.commutes c]
            rfl
          _ = algebraMap k (PowerSeries k) c := by
            change tiltedArc (k := k) α (MvPowerSeries.C c) = PowerSeries.C c
            exact Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArc_C α c }
  have hcoord (j : Option (Fin d)) :
      φ (algebraMap R T (MvPolynomial.X j)) =
        PowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM j) +
          PowerSeries.C (j.elim 1 α) * PowerSeries.X := by
    cases j with
    | none =>
        change tiltedArc (k := k) α
          (Φ (algebraMap R T (MvPolynomial.X none))) = _
        have hmap : algebraMap R T (MvPolynomial.X none) =
            algebraMap A T (algebraMap R A (MvPolynomial.X none)) :=
          IsScalarTower.algebraMap_apply R A T _
        rw [hmap, localToFinSuccPowerSeries_none (k := k) (B := A) M eM]
        change tiltedArc (k := k) α
          (MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM none) +
            MvPowerSeries.X (0 : Fin (d + 1))) = _
        calc
          tiltedArc (k := k) α
              (MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM none) +
                MvPowerSeries.X (0 : Fin (d + 1))) =
              tiltedArc (k := k) α
                  (MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM none)) +
                tiltedArc (k := k) α (MvPowerSeries.X (0 : Fin (d + 1))) := by
              exact map_add (tiltedArcMap (k := k) α) _ _
          _ = PowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM none) +
              PowerSeries.C (none.elim 1 α) * PowerSeries.X := by
              rw [Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArc_C,
                Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArc_X_t]
              simp
    | some j =>
        change tiltedArc (k := k) α
          (Φ (algebraMap R T (MvPolynomial.X (some j)))) = _
        have hmap : algebraMap R T (MvPolynomial.X (some j)) =
            algebraMap A T (algebraMap R A (MvPolynomial.X (some j))) :=
          IsScalarTower.algebraMap_apply R A T _
        rw [hmap, localToFinSuccPowerSeries_some (k := k) (B := A) M eM j]
        change tiltedArc (k := k) α
          (MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM (some j)) +
            MvPowerSeries.X j.succ) = _
        calc
          tiltedArc (k := k) α
              (MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM (some j)) +
                MvPowerSeries.X j.succ) =
              tiltedArc (k := k) α
                  (MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM (some j))) +
                tiltedArc (k := k) α (MvPowerSeries.X j.succ) := by
              exact map_add (tiltedArcMap (k := k) α) _ _
          _ = PowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM (some j)) +
              PowerSeries.C ((some j).elim 1 α) * PowerSeries.X := by
              rw [Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArc_C,
                Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArc_X_succ]
              rfl
  have h := arc_derivative_eq_option_coordinate_sum
    (k := k) (d := d) (T := T) φ α
    (β := residueCoordinates (σ := Option (Fin d)) M eM) hcoord b
  simpa [φ, Φ, tiltedArc] using h

end
end Stafford38.Geometry.ActualOptionArcDerivative
