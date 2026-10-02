module
public import Stafford38.Geometry.PrescribedCompletionDerivationCommutation
public import Stafford38.Geometry.EtaleCotangentBasis

@[expose] public section

open Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap
open Stafford38.Geometry.EtaleLocalChartFinitePartialDerivation
open Stafford38.Geometry.PrescribedCompletionDerivationCommutation

set_option autoImplicit false

universe u v

variable {k : Type u} [Field k] {d : ℕ} {A : Type v} [CommRing A]
variable [Algebra (MvPolynomial (Fin (d + 1)) k) A] [Algebra k A]
  [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) A]
  [Algebra.EssFiniteType (MvPolynomial (Fin (d + 1)) k) A]

local notation "R" => MvPolynomial (Fin (d + 1)) k

theorem actual_prescribed_completion_commutes_with_every_parameter_derivation
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (i : Fin (d + 1)) (b : Localization.AtPrime M) :
    MvPowerSeries.pderiv i
        (localToPowerSeries (σ := Fin (d + 1)) M eM b) =
      localToPowerSeries (σ := Fin (d + 1)) M eM
        (parameterDerivation (k := k) (d := d)
          (B := Localization.AtPrime M) i b) :=
  localToPowerSeries_commutes_parameterDerivation M eM i b

theorem actual_option_completion_commutes_with_reindexed_derivation
    {Aₒ : Type v} [CommRing Aₒ]
    [Algebra (MvPolynomial (Option (Fin d)) k) Aₒ] [Algebra k Aₒ]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) Aₒ]
    [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) Aₒ]
    (M : Ideal Aₒ) [M.IsMaximal] (eM : (Aₒ ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (Localization.AtPrime M)]
    (i : Fin (d + 1)) (b : Localization.AtPrime M) :
    MvPowerSeries.pderiv i
        (Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
          (k := k) (B := Aₒ) (d := d) M eM b) =
      Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
        (k := k) (B := Aₒ) (d := d) M eM
        (Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d))
          (B := Localization.AtPrime M) (L := Localization.AtPrime M)
          ((_root_.finSuccEquiv d) i) b) :=
  localToFinSuccPowerSeries_commutes_coordinateDerivation M eM i b

/-- Exercise the Option-indexed chart on a nonlinear local fraction: the
reindexed parameter derivation differentiates a squared numerator times an
actual inverse-unit denominator by Leibniz, and completion commutes with it. -/
theorem actual_option_nonlinear_rational_completion_derivative_oracle
    {Aₒ : Type v} [CommRing Aₒ]
    [Algebra (MvPolynomial (Option (Fin d)) k) Aₒ] [Algebra k Aₒ]
    [IsScalarTower k (MvPolynomial (Option (Fin d)) k) Aₒ]
    [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) Aₒ]
    (M : Ideal Aₒ) [M.IsMaximal] (eM : (Aₒ ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (Localization.AtPrime M)]
    (i : Fin (d + 1)) (p q : Localization.AtPrime M)
    (u : (Localization.AtPrime M)ˣ) :
    let T := Localization.AtPrime M
    let N : T := p ^ 2 + q
    let r : T := (↑(u⁻¹) : T)
    let D : Derivation k T T :=
      Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Option (Fin d)) (B := T) (L := T)
        ((_root_.finSuccEquiv d) i)
    MvPowerSeries.pderiv i
        (Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
          (k := k) (B := Aₒ) (d := d) M eM (N * r)) =
      Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
        (k := k) (B := Aₒ) (d := d) M eM
          (N * D r + r * D N) := by
  let T := Localization.AtPrime M
  let N : T := p ^ 2 + q
  let r : T := (↑(u⁻¹) : T)
  let D : Derivation k T T :=
    Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
      (k := k) (σ := Option (Fin d)) (B := T) (L := T)
      ((_root_.finSuccEquiv d) i)
  have hcomm :=
    localToFinSuccPowerSeries_commutes_coordinateDerivation M eM i (N * r)
  have hLeibniz :
      Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := T) (L := T)
          ((_root_.finSuccEquiv d) i) (N * r) =
        N * D r + r * D N := by
    simpa [D, smul_eq_mul] using D.leibniz N r
  rw [hLeibniz] at hcomm
  simpa [D, N, r] using hcomm

theorem actual_tilted_arc_derivative_is_full_parameter_direction
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (α : Fin d → k) (b : Localization.AtPrime M) :
    PowerSeries.derivative
        (localToPowerSeriesArc (M := M) (B := A) α eM b) =
      localToPowerSeriesArc (M := M) (B := A) α eM
          (parameterDerivation (k := k) (d := d)
            (B := Localization.AtPrime M) 0 b) +
        ∑ j : Fin d, PowerSeries.C (α j) *
          localToPowerSeriesArc (M := M) (B := A) α eM
            (parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) j.succ b) :=
  localToPowerSeriesArc_derivative_eq_parameter_sum M eM α b

theorem actual_tilted_arc_derivative_lands_in_canonical_laurent_field
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (α : Fin d → k) (b : Localization.AtPrime M) :
    algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.derivative (localToPowerSeriesArc (M := M) (B := A) α eM b)) =
      algebraMap (PowerSeries k) (LaurentSeries k)
          (localToPowerSeriesArc (M := M) (B := A) α eM
            (parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) 0 b)) +
        ∑ j : Fin d,
          algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C (α j)) *
            algebraMap (PowerSeries k) (LaurentSeries k)
              (localToPowerSeriesArc (M := M) (B := A) α eM
                (parameterDerivation (k := k) (d := d)
                  (B := Localization.AtPrime M) j.succ b)) :=
  localToArcLaurentSeries_derivative_eq_parameter_sum M eM α b

/-- A nonlinear local fraction is also covered: the parameter derivations act
on a squared numerator times the inverse of an actual unit denominator by the
ordinary Leibniz rule, and the canonical tilted-arc derivative is their
weighted sum. -/
theorem actual_nonlinear_rational_element_derivative_oracle
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (α : Fin d → k) (p q : Localization.AtPrime M)
    (u : (Localization.AtPrime M)ˣ) :
    let N : Localization.AtPrime M := p ^ 2 + q
    let r : Localization.AtPrime M := (↑(u⁻¹) : Localization.AtPrime M)
    PowerSeries.derivative
        (localToPowerSeriesArc (M := M) (B := A) α eM (N * r)) =
      localToPowerSeriesArc (M := M) (B := A) α eM
          (N * parameterDerivation (k := k) (d := d)
            (B := Localization.AtPrime M) 0 r +
            r * parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) 0 N) +
        ∑ j : Fin d, PowerSeries.C (α j) *
          localToPowerSeriesArc (M := M) (B := A) α eM
            (N * parameterDerivation (k := k) (d := d)
                (B := Localization.AtPrime M) j.succ r +
              r * parameterDerivation (k := k) (d := d)
                (B := Localization.AtPrime M) j.succ N) := by
  let N : Localization.AtPrime M := p ^ 2 + q
  let r : Localization.AtPrime M := (↑(u⁻¹) : Localization.AtPrime M)
  have h := localToPowerSeriesArc_derivative_eq_parameter_sum M eM α (N * r)
  have hzero :
      parameterDerivation (k := k) (d := d)
          (B := Localization.AtPrime M) 0 (N * r) =
        N * parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) 0 r +
          r * parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) 0 N := by
    simpa [smul_eq_mul] using
      (parameterDerivation (k := k) (d := d)
        (B := Localization.AtPrime M) 0).leibniz N r
  have hsucc (j : Fin d) :
      parameterDerivation (k := k) (d := d)
          (B := Localization.AtPrime M) j.succ (N * r) =
        N * parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) j.succ r +
          r * parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) j.succ N := by
    simpa [smul_eq_mul] using
      (parameterDerivation (k := k) (d := d)
        (B := Localization.AtPrime M) j.succ).leibniz N r
  change PowerSeries.derivative
      (localToPowerSeriesArc (M := M) (B := A) α eM (N * r)) = _ at h
  rw [hzero] at h
  simp_rw [hsucc] at h
  exact h

#print axioms actual_prescribed_completion_commutes_with_every_parameter_derivation
#print axioms actual_option_completion_commutes_with_reindexed_derivation
#print axioms actual_option_nonlinear_rational_completion_derivative_oracle
#print axioms actual_tilted_arc_derivative_is_full_parameter_direction
#print axioms actual_tilted_arc_derivative_lands_in_canonical_laurent_field
#print axioms actual_nonlinear_rational_element_derivative_oracle
