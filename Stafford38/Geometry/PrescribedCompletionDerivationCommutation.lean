module
public import Stafford38.Geometry.EtaleLocalChartFinitePartialDerivation
public import Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap
public import Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
public import Mathlib.RingTheory.LaurentSeries

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Derivations commute with the canonical completed chart

The completion map here is the prescribed map built from the canonical
completion equivalence, not a caller-supplied homomorphism.  Agreement on the
polynomial parameters and the checked Kähler-basis uniqueness theorem give
agreement on every element of the local ring.
-/

namespace Stafford38.Geometry.PrescribedCompletionDerivationCommutation

open Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap
open Stafford38.Geometry.EtaleLocalChartFinitePartialDerivation
open Stafford38.Geometry.PrescribedAffineResidueCompletion

noncomputable section

universe u v

variable {k : Type u} [Field k] {d : ℕ} {A : Type v} [CommRing A]
variable [Algebra (MvPolynomial (Fin (d + 1)) k) A] [Algebra k A]
  [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) A]
  [Algebra.EssFiniteType (MvPolynomial (Fin (d + 1)) k) A]

local notation "R" => MvPolynomial (Fin (d + 1)) k
local notation "C" => MvPowerSeries (Fin (d + 1)) k

/-- For the actual prescribed completion chart, every polynomial-parameter
derivation commutes with completion.  Thus this is an identity of derivations
on the whole local ring, not only a formula on selected coordinates. -/
theorem localToPowerSeries_commutes_parameterDerivation
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (i : Fin (d + 1)) (b : Localization.AtPrime M) :
    MvPowerSeries.pderiv i
        (PrescribedGroundPointPowerSeriesMap.localToPowerSeries
          (σ := Fin (d + 1)) M eM b) =
      PrescribedGroundPointPowerSeriesMap.localToPowerSeries
        (σ := Fin (d + 1)) M eM
        (parameterDerivation (k := k) (d := d)
          (B := Localization.AtPrime M) i b) := by
  let T := Localization.AtPrime M
  let Φ : T →ₐ[k] C :=
    PrescribedGroundPointPowerSeriesMap.localToPowerSeries
      (σ := Fin (d + 1)) M eM
  letI : Algebra T C := Φ.toRingHom.toAlgebra
  letI : IsScalarTower k T C := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k C c = Φ (algebraMap k T c)
    exact (Φ.commutes c).symm)
  have hΦ (j : Fin (d + 1)) :
      Φ (algebraMap R T (MvPolynomial.X j)) =
        MvPowerSeries.C (residueCoordinates (σ := Fin (d + 1)) M eM j) +
          MvPowerSeries.X j := by
    calc
      Φ (algebraMap R T (MvPolynomial.X j)) =
          Φ (algebraMap A T (algebraMap R A (MvPolynomial.X j))) := by
        exact congrArg Φ (IsScalarTower.algebraMap_apply R A T _)
      _ = originalAlgebraToPowerSeries (σ := Fin (d + 1)) M eM
          (algebraMap R A (MvPolynomial.X j)) := rfl
      _ = MvPowerSeries.C (residueCoordinates (σ := Fin (d + 1)) M eM j) +
          MvPowerSeries.X j :=
        originalAlgebraToPowerSeries_coordinate (σ := Fin (d + 1)) M eM j
  let Dleft : Derivation k T C :=
    (MvPowerSeries.pderiv i).compAlgebraMap T
  let Φlin : T →ₗ[T] C :=
    { toFun := Φ
      map_add' := Φ.map_add
      map_smul' := fun r x => by
        change Φ (r * x) = Φ r * Φ x
        exact Φ.map_mul r x }
  let Dright : Derivation k T C :=
    Φlin.compDer (parameterDerivation (k := k) (d := d) (B := T) i)
  have hleft : ∀ j, Dleft (algebraMap R T (MvPolynomial.X j)) =
      if j = i then (1 : C) else 0 := by
    intro j
    change MvPowerSeries.pderiv i
      (Φ (algebraMap R T (MvPolynomial.X j))) = _
    rw [hΦ j]
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, eq_comm]
  have hright : ∀ j, Dright (algebraMap R T (MvPolynomial.X j)) =
      if j = i then (1 : C) else 0 := by
    intro j
    change Φ (parameterDerivation (k := k) (d := d) (B := T) i
      (algebraMap R T (MvPolynomial.X j))) = _
    rw [parameterDerivation_apply_parameter]
    simp
  have hderiv : Dleft = Dright := by
    calc
      Dleft = EtaleCotangentBasis.derivationFromValues
          (k := k) (σ := Fin (d + 1)) (B := T) (L := C)
          (fun j => Dleft (algebraMap R T (MvPolynomial.X j))) :=
        (EtaleCotangentBasis.derivation_eq_from_parameter_values Dleft).symm
      _ = EtaleCotangentBasis.derivationFromValues
          (k := k) (σ := Fin (d + 1)) (B := T) (L := C)
          (fun j => Dright (algebraMap R T (MvPolynomial.X j))) := by
        congr 1
        funext j
        rw [hleft j, hright j]
      _ = Dright :=
        EtaleCotangentBasis.derivation_eq_from_parameter_values Dright
  change MvPowerSeries.pderiv i (Φ b) =
    Φ (parameterDerivation (k := k) (d := d) (B := T) i b)
  exact congrArg (fun D : Derivation k T C => D b) hderiv

/-- The same full-derivation identity for the actual `Option (Fin d)` chart
after its canonical `finSuccEquiv` reindexing.  The output coordinate `i`
corresponds to the source parameter `finSuccEquiv d i`; no derivative
identities for the renamed completion map are assumed. -/
theorem localToFinSuccPowerSeries_commutes_coordinateDerivation
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
        (EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d))
          (B := Localization.AtPrime M) (L := Localization.AtPrime M)
          ((_root_.finSuccEquiv d) i) b) := by
  let Rₒ := MvPolynomial (Option (Fin d)) k
  let T := Localization.AtPrime M
  let Ψ : T →ₐ[k] MvPowerSeries (Fin (d + 1)) k :=
    Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
      (k := k) (B := Aₒ) (d := d) M eM
  letI : Algebra T (MvPowerSeries (Fin (d + 1)) k) := Ψ.toRingHom.toAlgebra
  letI : IsScalarTower k T (MvPowerSeries (Fin (d + 1)) k) :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      change algebraMap k (MvPowerSeries (Fin (d + 1)) k) c = Ψ (algebraMap k T c)
      exact (Ψ.commutes c).symm)
  have hcoord (j : Option (Fin d)) :
      Ψ (algebraMap Rₒ T (MvPolynomial.X j)) =
        MvPowerSeries.C (residueCoordinates (σ := Option (Fin d)) M eM j) +
          MvPowerSeries.X ((_root_.finSuccEquiv d).symm j) := by
    cases j with
    | none =>
        calc
          Ψ (algebraMap Rₒ T (MvPolynomial.X none)) =
              Ψ (algebraMap Aₒ T (algebraMap Rₒ Aₒ (MvPolynomial.X none))) := by
            exact congrArg Ψ (IsScalarTower.algebraMap_apply Rₒ Aₒ T _)
          _ = Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
                (k := k) (B := Aₒ) (d := d) M eM
                (algebraMap Aₒ T (algebraMap Rₒ Aₒ (MvPolynomial.X none))) := rfl
          _ = _ :=
            Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries_none
              (k := k) (B := Aₒ) (d := d) M eM
    | some j =>
        calc
          Ψ (algebraMap Rₒ T (MvPolynomial.X (some j))) =
              Ψ (algebraMap Aₒ T (algebraMap Rₒ Aₒ (MvPolynomial.X (some j)))) := by
            exact congrArg Ψ (IsScalarTower.algebraMap_apply Rₒ Aₒ T _)
          _ = Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries
                (k := k) (B := Aₒ) (d := d) M eM
                (algebraMap Aₒ T (algebraMap Rₒ Aₒ (MvPolynomial.X (some j)))) := rfl
          _ = _ := by
            simpa using Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries_some
              (k := k) (B := Aₒ) (d := d) M eM j
  let Ψlin : T →ₗ[T] MvPowerSeries (Fin (d + 1)) k :=
    { toFun := Ψ
      map_add' := Ψ.map_add
      map_smul' := fun r x => by
        change Ψ (r * x) = Ψ r * Ψ x
        exact Ψ.map_mul r x }
  let Dleft : Derivation k T (MvPowerSeries (Fin (d + 1)) k) :=
    (MvPowerSeries.pderiv i).compAlgebraMap T
  let Dright : Derivation k T (MvPowerSeries (Fin (d + 1)) k) :=
    Ψlin.compDer (EtaleCotangentBasis.coordinateDerivation
      (k := k) (σ := Option (Fin d)) (B := T)
      (L := T) ((_root_.finSuccEquiv d) i))
  have hleft : ∀ j : Option (Fin d),
      Dleft (algebraMap Rₒ T (MvPolynomial.X j)) =
        if j = (_root_.finSuccEquiv d) i then (1 : MvPowerSeries (Fin (d + 1)) k) else 0 := by
    intro j
    change MvPowerSeries.pderiv i (Ψ (algebraMap Rₒ T (MvPolynomial.X j))) = _
    rw [hcoord j]
    by_cases h : i = (_root_.finSuccEquiv d).symm j
    · subst i
      simp [MvPowerSeries.pderiv_X, Pi.single_apply, eq_comm]
    · have h' : j ≠ (_root_.finSuccEquiv d) i := by
        intro hji
        apply h
        have heq := congrArg (_root_.finSuccEquiv d).symm hji
        simpa using heq.symm
      simp [MvPowerSeries.pderiv_X, Pi.single_apply, h, h']
  have hright : ∀ j : Option (Fin d),
      Dright (algebraMap Rₒ T (MvPolynomial.X j)) =
        if j = (_root_.finSuccEquiv d) i then (1 : MvPowerSeries (Fin (d + 1)) k) else 0 := by
    intro j
    change Ψ (EtaleCotangentBasis.coordinateDerivation
      (k := k) (σ := Option (Fin d)) (B := T)
      (L := T) ((_root_.finSuccEquiv d) i)
      (algebraMap Rₒ T (MvPolynomial.X j))) = _
    rw [EtaleCotangentBasis.coordinateDerivation_apply_parameter]
    simp
  have hderiv : Dleft = Dright := by
    calc
      Dleft = EtaleCotangentBasis.derivationFromValues
          (k := k) (σ := Option (Fin d)) (B := T)
          (L := MvPowerSeries (Fin (d + 1)) k)
          (fun j => Dleft (algebraMap Rₒ T (MvPolynomial.X j))) :=
        (EtaleCotangentBasis.derivation_eq_from_parameter_values Dleft).symm
      _ = EtaleCotangentBasis.derivationFromValues
          (k := k) (σ := Option (Fin d)) (B := T)
          (L := MvPowerSeries (Fin (d + 1)) k)
          (fun j => Dright (algebraMap Rₒ T (MvPolynomial.X j))) := by
        congr 1
        funext j
        rw [hleft j, hright j]
      _ = Dright :=
        EtaleCotangentBasis.derivation_eq_from_parameter_values Dright
  calc
    MvPowerSeries.pderiv i (Ψ b) = Dleft b := rfl
    _ = Dright b := congrArg (fun D : Derivation k T
      (MvPowerSeries (Fin (d + 1)) k) => D b) hderiv
    _ = Ψ (EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Option (Fin d)) (B := T)
        (L := T) ((_root_.finSuccEquiv d) i) b) := by
      change (Ψlin.compDer (EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := Option (Fin d)) (B := T)
        (L := T) ((_root_.finSuccEquiv d) i))) b = _
      rfl

/-- The canonical one-variable tilted arc differentiates every local function
by the corresponding weighted sum of the full chart parameter derivations.
This follows from the same Kähler-basis uniqueness theorem, using the actual
coordinate values of the prescribed arc. -/
theorem localToPowerSeriesArc_derivative_eq_parameter_sum
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (α : Fin d → k) (b : Localization.AtPrime M) :
    PowerSeries.derivative (R := k)
        (PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
          (M := M) (B := A) α eM b) =
      PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
          (M := M) (B := A) α eM
          (parameterDerivation (k := k) (d := d)
            (B := Localization.AtPrime M) 0 b) +
        ∑ j : Fin d, PowerSeries.C (α j) *
          PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
            (M := M) (B := A) α eM
            (parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) j.succ b) := by
  let T := Localization.AtPrime M
  let Ψ : T →ₐ[k] PowerSeries k :=
    PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
      (M := M) (B := A) α eM
  letI : Algebra T (PowerSeries k) := Ψ.toRingHom.toAlgebra
  letI : IsScalarTower k T (PowerSeries k) := IsScalarTower.of_algebraMap_eq
    (fun c => by
      change algebraMap k (PowerSeries k) c = Ψ (algebraMap k T c)
      exact (Ψ.commutes c).symm)
  have hΨ (j : Fin (d + 1)) :
      Ψ (algebraMap R T (MvPolynomial.X j)) =
        PowerSeries.C (residueCoordinates (σ := Fin (d + 1)) M eM j) +
          PowerSeries.C ((Fin.cons 1 α : Fin (d + 1) → k) j) *
            PowerSeries.X := by
    calc
      Ψ (algebraMap R T (MvPolynomial.X j)) =
          Ψ (algebraMap A T (algebraMap R A (MvPolynomial.X j))) := by
        exact congrArg Ψ (IsScalarTower.algebraMap_apply R A T _)
      _ = originalAlgebraToPowerSeriesArc (M := M) (B := A) α eM
          (algebraMap R A (MvPolynomial.X j)) := rfl
      _ = _ := originalAlgebraToPowerSeriesArc_coordinate
        (M := M) (B := A) α eM j
  let Ψlin : T →ₗ[T] PowerSeries k :=
    { toFun := Ψ
      map_add' := Ψ.map_add
      map_smul' := fun r x => by
        change Ψ (r * x) = Ψ r * Ψ x
        exact Ψ.map_mul r x }
  let Dleft : Derivation k T (PowerSeries k) :=
    (PowerSeries.derivative (R := k)).compAlgebraMap T
  let Dright : Derivation k T (PowerSeries k) :=
    (Ψlin.compDer (parameterDerivation (k := k) (d := d) (B := T) 0)) +
      ∑ j : Fin d, PowerSeries.C (α j) •
        (Ψlin.compDer (parameterDerivation (k := k) (d := d)
          (B := T) j.succ))
  have hleft : ∀ j, Dleft (algebraMap R T (MvPolynomial.X j)) =
      PowerSeries.C ((Fin.cons 1 α : Fin (d + 1) → k) j) := by
    intro j
    change PowerSeries.derivative (R := k)
      (Ψ (algebraMap R T (MvPolynomial.X j))) = _
    rw [hΨ j]
    simp [Derivation.map_add, Derivation.leibniz]
  have hparam (i j : Fin (d + 1)) :
      Ψ (parameterDerivation (k := k) (d := d) (B := T) i
        (algebraMap R T (MvPolynomial.X j))) = if j = i then (1 : PowerSeries k) else 0 := by
    change Ψ (parameterDerivation (k := k) (d := d) (B := T) i
      (algebraMap R T (MvPolynomial.X j)) ) = _
    rw [parameterDerivation_apply_parameter]
    simp
  have hright : ∀ j, Dright (algebraMap R T (MvPolynomial.X j)) =
      PowerSeries.C ((Fin.cons 1 α : Fin (d + 1) → k) j) := by
    intro j
    change (Derivation.coeFnAddMonoidHom
      ((Ψlin.compDer (parameterDerivation (k := k) (d := d) (B := T) 0)) +
        ∑ l : Fin d, PowerSeries.C (α l) •
          (Ψlin.compDer (parameterDerivation (k := k) (d := d) (B := T) l.succ))))
      (algebraMap R T (MvPolynomial.X j)) = _
    rw [map_add, map_sum]
    simp [Derivation.smul_apply, hparam, Ψlin, eq_comm]
    cases j using Fin.cases with
    | zero =>
        have hsum : ∑ l : Fin d,
            (if (0 : Fin (d + 1)) = l.succ then PowerSeries.C (α l) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          have hne : (0 : Fin (d + 1)) ≠ l.succ := by
            intro h
            exact Fin.succ_ne_zero l h.symm
          simp [hne]
        rw [hsum]
        simp
    | succ j => simp [Fin.succ_inj]
  have hderiv : Dleft = Dright := by
    calc
      Dleft = EtaleCotangentBasis.derivationFromValues
          (k := k) (σ := Fin (d + 1)) (B := T) (L := PowerSeries k)
          (fun j => Dleft (algebraMap R T (MvPolynomial.X j))) :=
        (EtaleCotangentBasis.derivation_eq_from_parameter_values Dleft).symm
      _ = EtaleCotangentBasis.derivationFromValues
          (k := k) (σ := Fin (d + 1)) (B := T) (L := PowerSeries k)
          (fun j => Dright (algebraMap R T (MvPolynomial.X j))) := by
        congr 1
        funext j
        rw [hleft j, hright j]
      _ = Dright :=
        EtaleCotangentBasis.derivation_eq_from_parameter_values Dright
  calc
    PowerSeries.derivative (R := k) (Ψ b) = Dleft b := rfl
    _ = Dright b := congrArg (fun D : Derivation k T (PowerSeries k) => D b) hderiv
    _ = Ψ (parameterDerivation (k := k) (d := d) (B := T) 0 b) +
        ∑ j : Fin d, PowerSeries.C (α j) *
          Ψ (parameterDerivation (k := k) (d := d) (B := T) j.succ b) := by
      change (Derivation.coeFnAddMonoidHom
        ((Ψlin.compDer (parameterDerivation (k := k) (d := d) (B := T) 0)) +
          ∑ j : Fin d, PowerSeries.C (α j) •
            (Ψlin.compDer (parameterDerivation (k := k) (d := d) (B := T) j.succ)))) b = _
      rw [map_add, map_sum]
      simp [Derivation.smul_apply, Ψlin]

/-- The same actual derivative identity after the canonical inclusion of the
one-variable power-series ring into its fraction field. -/
theorem localToArcFractionField_derivative_eq_parameter_sum
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (α : Fin d → k) (b : Localization.AtPrime M) :
    algebraMap (PowerSeries k) (FractionRing (PowerSeries k))
        (PowerSeries.derivative (R := k)
          (PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
            (M := M) (B := A) α eM b)) =
      algebraMap (PowerSeries k) (FractionRing (PowerSeries k))
        (PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
            (M := M) (B := A) α eM
            (parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) 0 b) +
          ∑ j : Fin d, PowerSeries.C (α j) *
            PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
              (M := M) (B := A) α eM
              (parameterDerivation (k := k) (d := d)
                (B := Localization.AtPrime M) j.succ b)) := by
  exact congrArg (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))
    (localToPowerSeriesArc_derivative_eq_parameter_sum M eM α b)

/-- The same derivative identity in the canonical Laurent-series target used
by the conormal and tangent-limit consumers. -/
theorem localToArcLaurentSeries_derivative_eq_parameter_sum
    (M : Ideal A) [M.IsMaximal] (eM : (A ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)]
    (α : Fin d → k) (b : Localization.AtPrime M) :
    algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.derivative (R := k)
          (PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
            (M := M) (B := A) α eM b)) =
      algebraMap (PowerSeries k) (LaurentSeries k)
          (PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
            (M := M) (B := A) α eM
            (parameterDerivation (k := k) (d := d)
              (B := Localization.AtPrime M) 0 b)) +
        ∑ j : Fin d,
          algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C (α j)) *
            algebraMap (PowerSeries k) (LaurentSeries k)
              (PrescribedGroundPointPowerSeriesMap.localToPowerSeriesArc
                (M := M) (B := A) α eM
                (parameterDerivation (k := k) (d := d)
                  (B := Localization.AtPrime M) j.succ b)) := by
  have h := congrArg (algebraMap (PowerSeries k) (LaurentSeries k))
    (localToPowerSeriesArc_derivative_eq_parameter_sum M eM α b)
  simpa only [map_add, map_sum, map_mul] using h

end

end Stafford38.Geometry.PrescribedCompletionDerivationCommutation
