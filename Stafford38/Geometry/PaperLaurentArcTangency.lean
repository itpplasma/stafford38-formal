import Stafford38.Geometry.PowerSeriesArcTangency
import Mathlib.RingTheory.LaurentSeries
import Stafford38.Geometry.ScalarExtensionPoints

/-!
# Generic Laurent tangency from retained power-series equations

If a polynomial ideal vanishes identically along a completed power-series
arc, applying any power-series derivation and then passing its chain-rule
identity to the Laurent fraction field gives an actual tangent vector at the
generic Laurent point.  In particular, the coefficientwise residue-field
derivations and the uniformizer derivative are tangent there.
-/

namespace Stafford38.Geometry.PaperLaurentArcTangency

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.Geometry.PowerSeriesArcTangency
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.CoisotropicTranslation

noncomputable section

universe u

variable {k κ : Type u} [Field k] [Field κ] [Algebra k κ]

private theorem differentialCovector_mul
    {m : ℕ} (y v : Fin m → LaurentSeries κ)
    (f g : MvPolynomial (Fin m) (LaurentSeries κ)) :
    differentialCovector y (f * g) v =
      MvPolynomial.eval y f * differentialCovector y g v +
      MvPolynomial.eval y g * differentialCovector y f v := by
  rw [Stafford38.Geometry.AffineConormalSpan.differentialCovector_mul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    differentialCovector_apply, smul_eq_mul]
  ring

private theorem algebraMap_eval₂_eq_eval₂_algebraMap
    {m : ℕ} (q : Fin m → PowerSeries κ)
    (f : MvPolynomial (Fin m) k) :
    algebraMap (PowerSeries κ) (LaurentSeries κ)
        (MvPolynomial.eval₂ (algebraMap k (PowerSeries κ)) q f) =
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries κ))
        (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (q i)) f := by
  have hmap := MvPolynomial.eval₂_comp_left
    (algebraMap (PowerSeries κ) (LaurentSeries κ))
    (algebraMap k (PowerSeries κ)) q f
  have hcoeff :
      (algebraMap (PowerSeries κ) (LaurentSeries κ)).comp
          (algebraMap k (PowerSeries κ)) = algebraMap k (LaurentSeries κ) := by
    ext a
    rw [HahnSeries.algebraMap_apply']
    rfl
  rw [hcoeff] at hmap
  exact hmap

/-- A derivation of the retained power-series ring produces a tangent vector
at the generic Laurent point whenever the actual equations vanish on the
arc. -/
theorem powerSeriesDerivationVector_mem_genericZariskiTangentSpace
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries κ)
    (D : Derivation k (PowerSeries κ) (PowerSeries κ))
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries κ)) q f = 0) :
    (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (D (q i))) ∈
      zariskiTangentSpace
        (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (q i))
        (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ)))) := by
  let y : Fin m → LaurentSeries κ :=
    fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (q i)
  let v : Fin m → LaurentSeries κ :=
    fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (D (q i))
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator]
  intro φ hφ
  have hmap : ∀ g : MvPolynomial (Fin m) (LaurentSeries κ),
      g ∈ I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ))) →
      MvPolynomial.eval y g = 0 ∧ differentialCovector y g v = 0 := by
    intro g hg
    rw [Ideal.map] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨f, hf, rfl⟩
        have heval : MvPolynomial.eval y
            (MvPolynomial.map (algebraMap k (LaurentSeries κ)) f) = 0 := by
          rw [MvPolynomial.eval_map]
          rw [← algebraMap_eval₂_eq_eval₂_algebraMap]
          simpa using congrArg (algebraMap (PowerSeries κ) (LaurentSeries κ))
            (hq f hf)
        have hderiv := derivation_eval₂ D f q
        rw [hq f hf, D.map_zero] at hderiv
        have hsum : ∑ i : Fin m,
            MvPolynomial.eval₂ (algebraMap k (PowerSeries κ)) q
                (MvPolynomial.pderiv i f) * D (q i) = 0 := hderiv.symm
        have hsumL := congrArg (algebraMap (PowerSeries κ) (LaurentSeries κ)) hsum
        simp only [map_zero, map_sum] at hsumL
        have hdifferential : differentialCovector y
            (MvPolynomial.map (algebraMap k (LaurentSeries κ)) f) v = 0 := by
          unfold differentialCovector
          simp only [differentialCovector_apply, differentialAt,
            MvPolynomial.pderiv_map]
          have hterms : ∀ i : Fin m,
              MvPolynomial.eval y
                  (MvPolynomial.map (algebraMap k (LaurentSeries κ))
                    (MvPolynomial.pderiv i f)) * v i =
                algebraMap (PowerSeries κ) (LaurentSeries κ)
                    (MvPolynomial.eval₂ (algebraMap k (PowerSeries κ)) q
                      (MvPolynomial.pderiv i f) * D (q i)) := by
            intro i
            rw [MvPolynomial.eval_map]
            rw [← algebraMap_eval₂_eq_eval₂_algebraMap]
            simp [v]
          change (∑ i : Fin m,
            MvPolynomial.eval y
              (MvPolynomial.map (algebraMap k (LaurentSeries κ))
                (MvPolynomial.pderiv i f)) * v i) = 0
          simp_rw [hterms]
          exact hsumL
        exact ⟨heval, hdifferential⟩
    | zero => simp [differentialCovector, differentialAt, map_zero]
    | add f g hf hg ihf ihg =>
        refine ⟨by rw [MvPolynomial.eval_add, ihf.1, ihg.1, add_zero], ?_⟩
        change (∑ i : Fin m,
          MvPolynomial.eval y (MvPolynomial.pderiv i (f + g)) * v i) = 0
        simp only [map_add, MvPolynomial.eval_add, add_mul]
        rw [Finset.sum_add_distrib]
        have hif : (∑ i : Fin m,
            MvPolynomial.eval y (MvPolynomial.pderiv i f) * v i) = 0 := by
          simpa [differentialCovector, differentialAt] using ihf.2
        have hig : (∑ i : Fin m,
            MvPolynomial.eval y (MvPolynomial.pderiv i g) * v i) = 0 := by
          simpa [differentialCovector, differentialAt] using ihg.2
        rw [hif, hig]
        simp
    | smul a f hf ih =>
        refine ⟨by simpa [MvPolynomial.smul_eq_C_mul, ih.1], ?_⟩
        have hprod := differentialCovector_mul y v a f
        change differentialCovector y (a * f) v = 0
        rw [hprod, ih.1, ih.2]
        simp
  induction hφ using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨g, rfl⟩
      exact (hmap g.1 g.2).2
  | zero => simp
  | add φ ψ hφ hψ ihφ ihψ =>
      change φ v + ψ v = 0
      rw [ihφ, ihψ]
      simp
  | smul a φ hφ ih =>
      change a * φ v = 0
      rw [ih]
      simp

/-- Coefficientwise residue-field derivations are tangent at the generic
Laurent point of an actual retained arc. -/
theorem coefficientwiseDerivation_mem_genericZariskiTangentSpace
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries κ) (D : Derivation k κ κ)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries κ)) q f = 0) :
    (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ)
        (coefficientwiseDerivation D (q i))) ∈
      zariskiTangentSpace
        (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (q i))
        (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ)))) :=
  powerSeriesDerivationVector_mem_genericZariskiTangentSpace
    I q (coefficientwiseDerivation D) hq

/-- The uniformizer derivative is tangent at the generic Laurent point of an
actual retained arc. -/
theorem uniformizerDerivation_mem_genericZariskiTangentSpace
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries κ)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries κ)) q f = 0) :
    (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ)
        (uniformizerDerivation (k := k) (K := κ) (q i))) ∈
      zariskiTangentSpace
        (fun i ↦ algebraMap (PowerSeries κ) (LaurentSeries κ) (q i))
        (I.map (MvPolynomial.map (algebraMap k (LaurentSeries κ)))) :=
  powerSeriesDerivationVector_mem_genericZariskiTangentSpace
    I q (uniformizerDerivation (k := k) (K := κ)) hq

#print axioms powerSeriesDerivationVector_mem_genericZariskiTangentSpace
#print axioms coefficientwiseDerivation_mem_genericZariskiTangentSpace
#print axioms uniformizerDerivation_mem_genericZariskiTangentSpace

end

end Stafford38.Geometry.PaperLaurentArcTangency
