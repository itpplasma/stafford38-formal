module
public import Stafford38.Geometry.AffinePointCompletion
public import Stafford38.Geometry.AdicCompletionRingEquiv
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Equiv

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Stafford38.Geometry.SmoothLocalParameterCompletion

noncomputable section

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [Fintype σ]

/-- The actual affine-chart completion map sends the centered polynomial coordinate to the
corresponding formal variable. The public `powerSeriesCompletionAtPoint` is defined by composing
this translation-induced completion equivalence with the canonical power-series completion map. -/
theorem affinePointCompletion_variable_explicit (p : σ → k) (i : σ) :
    let I : Ideal (MvPolynomial σ k) := MvPolynomial.idealOfVars σ k
    let J : Ideal (MvPolynomial σ k) :=
      Stafford38.Geometry.AffinePointCompletion.pointIdeal p
    let e := (Stafford38.Geometry.AffinePointCompletion.translate p).toRingEquiv
    let hJ : J = I.map (e : MvPolynomial σ k →+* MvPolynomial σ k) := by
      change Stafford38.Geometry.AffinePointCompletion.pointIdeal p =
        (MvPolynomial.idealOfVars σ k).map
          ((Stafford38.Geometry.AffinePointCompletion.translate p).toRingEquiv :
            MvPolynomial σ k →+* MvPolynomial σ k)
      simpa only [RingEquiv.toRingHom_eq_coe] using
        Stafford38.Geometry.AffinePointCompletion.pointIdeal_eq_map_translate p
    Stafford38.Geometry.AdicCompletionRingEquiv.ofRingEquiv e I J hJ
      (MvPowerSeries.toAdicCompletion σ k
        (MvPolynomial.toMvPowerSeries (MvPolynomial.X i))) =
      AdicCompletion.of J (MvPolynomial σ k)
        (MvPolynomial.X i - MvPolynomial.C (p i)) := by
  classical
  dsimp
  rw [MvPowerSeries.toAdicCompletion_coe]
  rw [Stafford38.Geometry.AdicCompletionRingEquiv.ofRingEquiv_apply_of]
  simp [Stafford38.Geometry.AffinePointCompletion.translate]

/-- The affine chart completion fixes the ground-field constants. -/
theorem affinePointCompletion_constant_explicit (p : σ → k) (c : k) :
    let I : Ideal (MvPolynomial σ k) := MvPolynomial.idealOfVars σ k
    let J : Ideal (MvPolynomial σ k) :=
      Stafford38.Geometry.AffinePointCompletion.pointIdeal p
    let e := (Stafford38.Geometry.AffinePointCompletion.translate p).toRingEquiv
    let hJ : J = I.map (e : MvPolynomial σ k →+* MvPolynomial σ k) := by
      change Stafford38.Geometry.AffinePointCompletion.pointIdeal p =
        (MvPolynomial.idealOfVars σ k).map
          ((Stafford38.Geometry.AffinePointCompletion.translate p).toRingEquiv :
            MvPolynomial σ k →+* MvPolynomial σ k)
      simpa only [RingEquiv.toRingHom_eq_coe] using
        Stafford38.Geometry.AffinePointCompletion.pointIdeal_eq_map_translate p
    Stafford38.Geometry.AdicCompletionRingEquiv.ofRingEquiv e I J hJ
      (MvPowerSeries.toAdicCompletion σ k (MvPowerSeries.C c)) =
      AdicCompletion.of J (MvPolynomial σ k) (MvPolynomial.C c) := by
  classical
  dsimp
  have hc : MvPowerSeries.C c =
      MvPolynomial.toMvPowerSeries (MvPolynomial.C c : MvPolynomial σ k) := by
    ext d
    simp
  rw [hc, MvPowerSeries.toAdicCompletion_coe]
  rw [Stafford38.Geometry.AdicCompletionRingEquiv.ofRingEquiv_apply_of]
  simp [Stafford38.Geometry.AffinePointCompletion.translate]

end

end Stafford38.Geometry.SmoothLocalParameterCompletion
