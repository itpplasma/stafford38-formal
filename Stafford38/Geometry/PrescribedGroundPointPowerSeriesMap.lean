module
public import Stafford38.Geometry.PrescribedCompletionNonzero
public import Stafford38.Geometry.PrescribedAffineResidueCompletionConsumer
public import Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap

noncomputable section

open Stafford38.Geometry.PrescribedAffineResidueCompletion

variable {k σ B : Type*} [Field k] [Fintype σ] [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B]
  [Algebra.EssFiniteType (MvPolynomial σ k) B]
variable (M : Ideal B)

local notation "R" => MvPolynomial σ k
local notation "T" => Localization.AtPrime M
local notation "J" => IsLocalRing.maximalIdeal (Localization.AtPrime M)

/-- Ground scalars pass through the prescribed completion as the same constants
in the multivariate power-series chart. -/
theorem prescribedCompletion_constant
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] (c : k) :
    powerSeriesCompletionAtGroundPoint (σ := σ) M eM (MvPowerSeries.C c) =
      AdicCompletion.of J T (algebraMap k T c) := by
  let x := residueCoordinates (σ := σ) M eM
  let q := Stafford38.Geometry.AffinePointCompletion.pointIdeal x
  letI : q.IsMaximal := residuePoint_isMaximal (σ := σ) M eM
  letI : q.IsPrime := inferInstance
  let ρ := residueEvaluation (σ := σ) M eM
  letI : Algebra R k := ρ.toRingHom.toAlgebra
  letI : IsScalarTower R k k := IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  let eQ := residuePointQuotientEquiv (σ := σ) M eM
  letI : IsScalarTower R k (B ⧸ M) := IsScalarTower.of_algebraMap_eq (fun a => by
    apply eM.injective
    rw [← Ideal.Quotient.mk_algebraMap R M a, eM.commutes]
    change eM (Ideal.Quotient.mk M (algebraMap R B a)) = ρ a
    rfl)
  letI : IsScalarTower R k (R ⧸ q) := IsScalarTower.of_algebraMap_eq (fun a => by
    apply eQ.injective
    calc
      eQ (algebraMap R (R ⧸ q) a) = ρ a := by
        change eQ (Ideal.Quotient.mk q a) = ρ a
        simpa [ρ] using residuePointQuotientEquiv_apply (σ := σ) M eM a
      _ = eQ (algebraMap k (R ⧸ q) (ρ a)) := by
        rw [eQ.commutes]
        rfl)
  have hq : Ideal.under R M = q := by
    simpa [x, q] using residuePoint_under_eq (σ := σ) M eM
  let e := residueEquivOverCoordinates (σ := σ) M eM
  letI : IsScalarTower k R T := inferInstance
  have hscalar : algebraMap R T (MvPolynomial.C c) = algebraMap k T c := by
    change algebraMap R T ((algebraMap k R) c) = algebraMap k T c
    exact (IsScalarTower.algebraMap_apply k R T c).symm
  have hAffine :
      Stafford38.Geometry.AffinePointCompletion.powerSeriesCompletionAtPoint x
          (MvPowerSeries.C c) = AdicCompletion.of q R (MvPolynomial.C c) := by
    simpa [Stafford38.Geometry.AffinePointCompletion.powerSeriesCompletionAtPoint] using
      Stafford38.Geometry.SmoothLocalParameterCompletion.affinePointCompletion_constant_explicit
        x c
  change (Stafford38.Geometry.EtalePointCompletion.completionEquivOfEtaleResidue
    q M hq e) (Stafford38.Geometry.AffinePointCompletion.powerSeriesCompletionAtPoint x
      (MvPowerSeries.C c)) = _
  rw [hAffine]
  rw [← hscalar]
  exact Stafford38.Geometry.PrescribedAffineResidueCompletion.etaleCompletion_apply_of
    q M hq e (MvPolynomial.C c)

/-- The local ring at the prescribed point maps canonically to its power-series
completion chart. The map is the inverse completed-chart equivalence after the
canonical dense map into the local completion. -/
def localToPowerSeries
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    T →ₐ[k] MvPowerSeries σ k := by
  let E := powerSeriesCompletionAtGroundPoint (σ := σ) M eM
  let f : T →+* MvPowerSeries σ k :=
    (E.symm : _ ≃+* _).toRingHom.comp
      (algebraMap T (AdicCompletion J T))
  refine { toRingHom := f, commutes' := ?_ }
  intro c
  apply E.injective
  calc
    E (f (algebraMap k T c)) = AdicCompletion.of J T (algebraMap k T c) := by
      simp [f, AdicCompletion.algebraMap_apply]
    _ = E (algebraMap k (MvPowerSeries σ k) c) := by
      rw [show algebraMap k (MvPowerSeries σ k) c = MvPowerSeries.C c by rfl]
      exact (prescribedCompletion_constant (σ := σ) M eM c).symm

@[simp]
theorem localToPowerSeries_apply
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] (b : T) :
    localToPowerSeries (σ := σ) M eM b =
      (powerSeriesCompletionAtGroundPoint (σ := σ) M eM).symm
        (algebraMap T (AdicCompletion J T) b) := by
  simp [localToPowerSeries, AdicCompletion.algebraMap_apply]

/-- Composition with the original coefficient algebra map gives the prescribed
power-series chart on the source algebra. -/
def originalAlgebraToPowerSeries
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    B →ₐ[k] MvPowerSeries σ k :=
  (localToPowerSeries (σ := σ) M eM).comp (IsScalarTower.toAlgHom k B T)

@[simp]
theorem originalAlgebraToPowerSeries_apply
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] (b : B) :
    originalAlgebraToPowerSeries (σ := σ) M eM b =
      localToPowerSeries (σ := σ) M eM (algebraMap B T b) := rfl

/-- The source coordinate is sent to its residue constant plus the centered formal
variable. This is the coefficient-preserving form of the prescribed-chart map. -/
theorem originalAlgebraToPowerSeries_coordinate
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] (i : σ) :
    originalAlgebraToPowerSeries (σ := σ) M eM
        (algebraMap R B (MvPolynomial.X i)) =
      MvPowerSeries.C (residueCoordinates (σ := σ) M eM i) + MvPowerSeries.X i := by
  let x := residueCoordinates (σ := σ) M eM
  let E := powerSeriesCompletionAtGroundPoint (σ := σ) M eM
  letI : IsScalarTower k R T := inferInstance
  letI : IsScalarTower R B T := inferInstance
  have hscalar : algebraMap R T (MvPolynomial.C (x i)) = algebraMap k T (x i) := by
    change algebraMap R T ((algebraMap k R) (x i)) = algebraMap k T (x i)
    exact (IsScalarTower.algebraMap_apply k R T (x i)).symm
  have hcoordinates :
      algebraMap B T (algebraMap R B (MvPolynomial.X i)) =
        algebraMap k T (x i) +
          algebraMap B T (algebraMap R B
            (MvPolynomial.X i - MvPolynomial.C (x i))) := by
    have hpoly : algebraMap R T (MvPolynomial.X i) =
        algebraMap R T (MvPolynomial.C (x i)) +
          algebraMap R T (MvPolynomial.X i - MvPolynomial.C (x i)) := by
      rw [← map_add]
      congr 1
      ring
    calc
      algebraMap B T (algebraMap R B (MvPolynomial.X i)) =
          algebraMap R T (MvPolynomial.X i) := by
        change ((algebraMap B T).comp (algebraMap R B)) _ = _
        rw [← IsScalarTower.algebraMap_eq R B T]
      _ = algebraMap k T (x i) + algebraMap R T
            (MvPolynomial.X i - MvPolynomial.C (x i)) := by
        rw [hpoly, hscalar]
      _ = algebraMap k T (x i) +
          algebraMap B T (algebraMap R B
            (MvPolynomial.X i - MvPolynomial.C (x i))) := by
        exact congrArg (fun y => algebraMap k T (x i) + y)
          (IsScalarTower.algebraMap_apply R B T _)
  have hcenter : E (MvPowerSeries.X i) =
      AdicCompletion.of J T (algebraMap R T
        (MvPolynomial.X i - MvPolynomial.C (x i))) := by
    simpa [E, x] using
      Stafford38.Geometry.PrescribedAffineResidueCompletionConsumer.prescribedCompletion_centeredGenerator
        (σ := σ) M eM i
  have hcenter' : E (MvPowerSeries.X i) =
      AdicCompletion.of J T (algebraMap B T (algebraMap R B
        (MvPolynomial.X i - MvPolynomial.C (x i)))) := by
    calc
      E (MvPowerSeries.X i) =
          AdicCompletion.of J T (algebraMap R T
            (MvPolynomial.X i - MvPolynomial.C (x i))) := hcenter
      _ = AdicCompletion.of J T (algebraMap B T (algebraMap R B
            (MvPolynomial.X i - MvPolynomial.C (x i)))) := by
        exact congrArg (AdicCompletion.of J T)
          (IsScalarTower.algebraMap_apply R B T _)
  apply E.injective
  calc
    E (originalAlgebraToPowerSeries (σ := σ) M eM
        (algebraMap R B (MvPolynomial.X i))) =
        AdicCompletion.of J T (algebraMap B T (algebraMap R B (MvPolynomial.X i))) := by
      rw [originalAlgebraToPowerSeries_apply, localToPowerSeries_apply]
      change E (E.symm (AdicCompletion.of J T
        (algebraMap B T (algebraMap R B (MvPolynomial.X i))))) = _
      exact E.apply_symm_apply _
    _ = AdicCompletion.of J T
          (algebraMap k T (x i) + algebraMap B T (algebraMap R B
            (MvPolynomial.X i - MvPolynomial.C (x i)))) := by
      exact congrArg (AdicCompletion.of J T) hcoordinates
    _ = AdicCompletion.of J T (algebraMap k T (x i)) +
        AdicCompletion.of J T (algebraMap B T (algebraMap R B
          (MvPolynomial.X i - MvPolynomial.C (x i)))) := by
      simp
    _ = E (MvPowerSeries.C (x i) + MvPowerSeries.X i) := by
      rw [map_add, prescribedCompletion_constant (σ := σ) M eM (x i), hcenter']

/-- The prescribed local map followed by the tilted formal arc. -/
noncomputable def localToTiltedArc {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
  [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)] :
    Localization.AtPrime M →ₐ[k] MvPowerSeries PUnit.{1} k :=
  (MvPowerSeries.substAlgHom
    (Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArcHasSubstPUnit α)).comp
    (localToPowerSeries (σ := Fin (n + 1)) M eM)

/-- The arc map on the original source is the composite of its genuine algebra
map into the local ring with the prescribed completion chart and standard tilt. -/
noncomputable def originalAlgebraToTiltedArc {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
  [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)] :
    B →ₐ[k] MvPowerSeries PUnit.{1} k :=
  (MvPowerSeries.substAlgHom
    (Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArcHasSubstPUnit α)).comp
    (originalAlgebraToPowerSeries (σ := Fin (n + 1)) M eM)

/-- The local ring at the chosen ground point maps to the ordinary one-variable
power-series ring along the canonical tilted arc. -/
noncomputable def localToPowerSeriesArc {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)] :
    Localization.AtPrime M →ₐ[k] PowerSeries k :=
  (Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.punitToPowerSeries (k := k)).toAlgHom.comp
    (localToTiltedArc (M := M) α eM)

@[simp] theorem localToPowerSeriesArc_apply {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)]
    (b : Localization.AtPrime M) :
    localToPowerSeriesArc (M := M) (B := B) α eM b =
      Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArcMap α
        (localToPowerSeries (σ := Fin (n + 1)) M eM b) := by
  rfl

/-- The local tilted arc followed by the canonical field-of-fractions inclusion. -/
noncomputable def localToArcFractionField {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)] :
    Localization.AtPrime M →ₐ[k] FractionRing (PowerSeries k) :=
  (IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))).comp
    (localToPowerSeriesArc (M := M) (B := B) α eM)

/-- The actual source coordinate follows its closed-point residue and then the
chosen tilted direction. -/
theorem originalAlgebraToTiltedArc_coordinate {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)]
    (i : Fin (n + 1)) :
    originalAlgebraToTiltedArc (M := M) α eM
        (algebraMap (MvPolynomial (Fin (n + 1)) k) B (MvPolynomial.X i)) =
      MvPowerSeries.C (residueCoordinates (σ := Fin (n + 1)) M eM i) +
        MvPowerSeries.C ((Fin.cons 1 α : Fin (n + 1) → k) i) *
          MvPowerSeries.X (PUnit.unit : PUnit.{1}) := by
  change (MvPowerSeries.substAlgHom
      (Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArcHasSubstPUnit α))
      (originalAlgebraToPowerSeries (σ := Fin (n + 1)) M eM
        (algebraMap (MvPolynomial (Fin (n + 1)) k) B (MvPolynomial.X i))) = _
  rw [originalAlgebraToPowerSeries_coordinate (σ := Fin (n + 1)) M eM i]
  rw [map_add, MvPowerSeries.substAlgHom_X]
  congr 1
  change (MvPowerSeries.substAlgHom
      (Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArcHasSubstPUnit α))
    (algebraMap k (MvPowerSeries (Fin (n + 1)) k) _) = _
  exact (MvPowerSeries.substAlgHom
      (Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArcHasSubstPUnit α)).commutes _

/-- The prescribed tilted arc expressed in the standard univariate power-series
ring. -/
noncomputable def originalAlgebraToPowerSeriesArc {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)] :
    B →ₐ[k] PowerSeries k :=
  (localToPowerSeriesArc (M := M) α eM).comp (IsScalarTower.toAlgHom k B (Localization.AtPrime M))

noncomputable def originalAlgebraToPowerSeriesArcFractionField {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)] :
    B →ₐ[k] FractionRing (PowerSeries k) :=
  (IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))).comp
    (originalAlgebraToPowerSeriesArc (M := M) (B := B) α eM)

/-- This coefficient-preserving algebra map is exactly the existing tilted-arc
map used by bad-locus avoidance and tangent normalization. -/
@[simp] theorem originalAlgebraToPowerSeriesArc_apply {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)]
    (b : B) :
    originalAlgebraToPowerSeriesArc (M := M) α eM b =
      Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArcMap α
        (originalAlgebraToPowerSeries (σ := Fin (n + 1)) M eM b) := by
  rfl

/-- In one variable, the original coordinates have the expected residue plus
linear-arc values in `PowerSeries k`. -/
theorem originalAlgebraToPowerSeriesArc_coordinate {n : ℕ} (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)]
    (i : Fin (n + 1)) :
    originalAlgebraToPowerSeriesArc (M := M) α eM
        (algebraMap (MvPolynomial (Fin (n + 1)) k) B (MvPolynomial.X i)) =
      PowerSeries.C (residueCoordinates (σ := Fin (n + 1)) M eM i) +
      PowerSeries.C ((Fin.cons 1 α : Fin (n + 1) → k) i) * PowerSeries.X := by
  have h := originalAlgebraToTiltedArc_coordinate (M := M) α eM i
  have hunit : (Equiv.equivPUnit Unit).symm (PUnit.unit : PUnit.{1}) = Unit.unit :=
    Subsingleton.elim _ _
  simpa [originalAlgebraToPowerSeriesArc, localToPowerSeriesArc, localToTiltedArc,
    originalAlgebraToTiltedArc, originalAlgebraToPowerSeries,
    Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.punitToPowerSeries,
    Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tiltedArcPointPUnit,
    MvPowerSeries.renameEquiv, MvPowerSeries.rename_X, hunit,
    PowerSeries.C, PowerSeries.X] using
      congrArg (Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.punitToPowerSeries
        (k := k)) h

theorem originalAlgebraToPowerSeriesArcFractionField_coordinate {n : ℕ}
    (α : Fin n → k)
    [Algebra (MvPolynomial (Fin (n + 1)) k) B]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) B]
    [Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) k) B]
    [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) k) (Localization.AtPrime M)]
    (i : Fin (n + 1)) :
    originalAlgebraToPowerSeriesArcFractionField (M := M) (B := B) α eM
        (algebraMap (MvPolynomial (Fin (n + 1)) k) B (MvPolynomial.X i)) =
      algebraMap (PowerSeries k) (FractionRing (PowerSeries k))
        (PowerSeries.C (residueCoordinates (σ := Fin (n + 1)) M eM i) +
          PowerSeries.C ((Fin.cons 1 α : Fin (n + 1) → k) i) * PowerSeries.X) := by
  change algebraMap (PowerSeries k) (FractionRing (PowerSeries k))
    (originalAlgebraToPowerSeriesArc (M := M) (B := B) α eM
      (algebraMap (MvPolynomial (Fin (n + 1)) k) B (MvPolynomial.X i))) = _
  rw [originalAlgebraToPowerSeriesArc_coordinate]

/-- The genuine local completion chart loses no local-ring elements: its
completion factor is injective by the Noetherian local Krull intersection
property, and the completed coordinate chart is an equivalence. -/
theorem localToPowerSeries_injective
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial σ k) (Localization.AtPrime M)] :
    Function.Injective (localToPowerSeries (σ := σ) M eM) := by
  intro a b hab
  apply PrescribedCompletionNonzero.localizationCompletion_of_injective
    (k := k) (σ := σ) (B := B) M
  have h := congrArg (PrescribedAffineResidueCompletion.powerSeriesCompletionAtGroundPoint
    (σ := σ) M eM) hab
  simpa only [localToPowerSeries_apply, RingEquiv.apply_symm_apply,
    AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply] using h


#print axioms prescribedCompletion_constant
#print axioms originalAlgebraToPowerSeries_coordinate
#print axioms originalAlgebraToTiltedArc_coordinate
#print axioms originalAlgebraToPowerSeriesArc_apply
#print axioms originalAlgebraToPowerSeriesArc_coordinate
#print axioms localToPowerSeriesArc_apply
#print axioms originalAlgebraToPowerSeriesArcFractionField_coordinate

end
end Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap

#print axioms Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.localToPowerSeries_injective
