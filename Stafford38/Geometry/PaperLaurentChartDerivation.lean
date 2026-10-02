import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.LaurentSeries
import Stafford38.LocalizedPolynomialDerivations
import Stafford38.Geometry.FormalDivisorLaurentConormal
import Stafford38.Geometry.PowerSeriesArcTangency
import Stafford38.Geometry.ContinuousPowerSeriesTangentFrame

/-!
# Derivation tangencies in the affine chart of a retained Laurent arc

The retained divisor construction supplies projective coordinates in a
one-variable completion.  Their affine ratios need only exist in its Laurent
fraction field.  This file extends actual power-series derivations through
the localization and computes their affine chart vectors by the quotient
rule.  In particular, it does not identify the projective column with its
dehomogenization.
-/

namespace Stafford38.Geometry.PaperLaurentChartDerivation

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.PowerSeriesArcTangency
open Stafford38.LocalizedPolynomialDerivations

noncomputable section

universe u

variable {k κ : Type u} [Field k] [Field κ] [Algebra k κ]

private theorem algebraMap_ground_to_laurent (c : k) :
    algebraMap k (LaurentSeries κ) c =
      algebraMap (PowerSeries κ) (LaurentSeries κ)
        (algebraMap k (PowerSeries κ) c) := by
  rw [HahnSeries.algebraMap_apply' (Γ := ℤ) (R := κ) (S := k) c]
  rfl

private theorem algebraModule_powerSeriesLaurentTower :
    letI : Module k (LaurentSeries κ) := Algebra.toModule
    letI : SMul k (LaurentSeries κ) :=
      (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
    IsScalarTower k (PowerSeries κ) (LaurentSeries κ) := by
  letI : Module k (LaurentSeries κ) := Algebra.toModule
  letI : SMul k (LaurentSeries κ) :=
    (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
  exact IsScalarTower.of_algebraMap_eq (R := k) (S := PowerSeries κ)
    (A := LaurentSeries κ) algebraMap_ground_to_laurent

/-- Extend a derivation of the retained power-series ring to its Laurent
localization. -/
def extendPowerSeriesDerivation
    (D : Derivation k (PowerSeries κ) (PowerSeries κ)) :
    letI : Module k (LaurentSeries κ) := Algebra.toModule
    letI : SMul k (LaurentSeries κ) :=
      (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
    letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
      algebraModule_powerSeriesLaurentTower
    Derivation k (LaurentSeries κ) (LaurentSeries κ) := by
  letI : Module k (LaurentSeries κ) := Algebra.toModule
  letI : SMul k (LaurentSeries κ) :=
    (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
  letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
    algebraModule_powerSeriesLaurentTower
  exact extendDerivation k (PowerSeries κ) (LaurentSeries κ)
    (Submonoid.powers (PowerSeries.X : PowerSeries κ))
    ((Algebra.linearMap (PowerSeries κ) (LaurentSeries κ)).compDer D)

@[simp]
theorem extendPowerSeriesDerivation_comp
    (D : Derivation k (PowerSeries κ) (PowerSeries κ)) :
    letI : Module k (LaurentSeries κ) := Algebra.toModule
    letI : SMul k (LaurentSeries κ) :=
      (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
    letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
      algebraModule_powerSeriesLaurentTower
    (extendPowerSeriesDerivation D).compAlgebraMap (PowerSeries κ) =
      (Algebra.linearMap (PowerSeries κ) (LaurentSeries κ)).compDer D := by
  letI : Module k (LaurentSeries κ) := Algebra.toModule
  letI : SMul k (LaurentSeries κ) :=
    (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
  letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
    algebraModule_powerSeriesLaurentTower
  exact extendDerivation_compAlgebraMap k (PowerSeries κ) (LaurentSeries κ)
    (Submonoid.powers (PowerSeries.X : PowerSeries κ)) _

theorem extendPowerSeriesDerivation_on_powerSeries
    (D : Derivation k (PowerSeries κ) (PowerSeries κ))
    (f : PowerSeries κ) :
    letI : Module k (LaurentSeries κ) := Algebra.toModule
    letI : SMul k (LaurentSeries κ) :=
      (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
    letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
      algebraModule_powerSeriesLaurentTower
    extendPowerSeriesDerivation D
        (algebraMap (PowerSeries κ) (LaurentSeries κ) f) =
      algebraMap (PowerSeries κ) (LaurentSeries κ) (D f) := by
  letI : Module k (LaurentSeries κ) := Algebra.toModule
  letI : SMul k (LaurentSeries κ) :=
    (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
  letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
    algebraModule_powerSeriesLaurentTower
  have h := DFunLike.congr_fun (extendPowerSeriesDerivation_comp D) f
  change extendPowerSeriesDerivation D
      (algebraMap (PowerSeries κ) (LaurentSeries κ) f) = _ at h
  simpa [LinearMap.compDer] using h

/-- The derivative of the dehomogenized ratio `q_(i+1) / q_0` is the
dehomogenization of the projective derivative column. -/
theorem extendPowerSeriesDerivation_dehomogenizedPoint
    (D : Derivation k (PowerSeries κ) (PowerSeries κ))
    (q : Fin (n + 1) → PowerSeries κ) (hq0 : q 0 ≠ 0) (i : Fin n) :
    letI : Module k (LaurentSeries κ) := Algebra.toModule
    letI : SMul k (LaurentSeries κ) :=
      (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
    letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
      algebraModule_powerSeriesLaurentTower
    extendPowerSeriesDerivation D
        (dehomogenizedPoint (laurentColumn q) i) =
      dehomogenizedTangentColumn (laurentColumn q)
        (laurentColumn (fun a ↦ D (q a))) i := by
  letI : Module k (LaurentSeries κ) := Algebra.toModule
  letI : SMul k (LaurentSeries κ) :=
    (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
  letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
    algebraModule_powerSeriesLaurentTower
  let E := extendPowerSeriesDerivation D
  have hq (a : Fin (n + 1)) :
      E (laurentColumn q a) = laurentColumn (fun b ↦ D (q b)) a := by
    exact extendPowerSeriesDerivation_on_powerSeries D (q a)
  have hden : laurentColumn q 0 ≠ 0 :=
    laurentColumn_ne_zero_of_ne_zero q hq0
  change E (laurentColumn q i.succ / laurentColumn q 0) = _
  rw [Derivation.leibniz_div E]
  rw [hq i.succ, hq 0]
  simp only [dehomogenizedTangentColumn_apply, laurentColumn, smul_eq_mul]
  field_simp [hden]

/-- Any derivation direction of the completed chart is tangent to the actual
affine equation ideal at the Laurent point, provided those equations vanish
there. -/
theorem derivation_chartVector_mem_zariskiTangentSpace
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries κ) (hq0 : q 0 ≠ 0)
    (D : Derivation k (PowerSeries κ) (PowerSeries κ))
    (hbase : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
        (dehomogenizedPoint (laurentColumn q)) f = 0) :
    dehomogenizedTangentColumn (laurentColumn q)
        (laurentColumn (fun a ↦ D (q a))) ∈
        zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ)))) := by
  letI : Module k (LaurentSeries κ) := Algebra.toModule
  letI : SMul k (LaurentSeries κ) :=
    (Algebra.toModule : Module k (LaurentSeries κ)).toSMul
  letI : IsScalarTower k (PowerSeries κ) (LaurentSeries κ) :=
    algebraModule_powerSeriesLaurentTower
  have htan := derivationVector_mem_zariskiTangentSpace_of_eval₂_eq_zero
    (k := k) (S := LaurentSeries κ) (extendPowerSeriesDerivation D)
    I (dehomogenizedPoint (laurentColumn q)) hbase
  have hEq :
      (fun i ↦ extendPowerSeriesDerivation D
        (dehomogenizedPoint (laurentColumn q) i)) =
      dehomogenizedTangentColumn (laurentColumn q)
        (laurentColumn (fun a ↦ D (q a))) := by
    funext i
    exact extendPowerSeriesDerivation_dehomogenizedPoint D q hq0 i
  rw [← hEq]
  exact htan

/-- The coefficientwise residue derivations give actual affine tangent
vectors at the dehomogenized Laurent point. -/
theorem coefficientwise_chartVector_mem_zariskiTangentSpace
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries κ) (hq0 : q 0 ≠ 0)
    (D : Derivation k κ κ)
    (hbase : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
        (dehomogenizedPoint (laurentColumn q)) f = 0) :
    dehomogenizedTangentColumn (laurentColumn q)
        (laurentColumn (fun a ↦ coefficientwiseDerivation D (q a))) ∈
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ)))) :=
  derivation_chartVector_mem_zariskiTangentSpace I q hq0
    (coefficientwiseDerivation D) hbase

/-- The uniformizer derivative also gives an actual affine tangent vector. -/
theorem uniformizer_chartVector_mem_zariskiTangentSpace
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries κ) (hq0 : q 0 ≠ 0)
    (hbase : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
        (dehomogenizedPoint (laurentColumn q)) f = 0) :
    dehomogenizedTangentColumn (laurentColumn q)
        (laurentColumn (fun a ↦ uniformizerDerivation (k := k) (K := κ) (q a))) ∈
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ)))) :=
  derivation_chartVector_mem_zariskiTangentSpace I q hq0
    (uniformizerDerivation (k := k) (K := κ)) hbase

#print axioms extendPowerSeriesDerivation
#print axioms derivation_chartVector_mem_zariskiTangentSpace
#print axioms coefficientwise_chartVector_mem_zariskiTangentSpace
#print axioms uniformizer_chartVector_mem_zariskiTangentSpace

end

end Stafford38.Geometry.PaperLaurentChartDerivation
