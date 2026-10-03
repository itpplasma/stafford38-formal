import Stafford38.Geometry.NormalizedLatticeProjectiveConeAdapter
import Stafford38.Geometry.GeneralTangentLimitCriterion
import Stafford38.Geometry.FormalDivisorLaurentConormal

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Stafford38.Geometry.DirectSummandInputOfActualChart

open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.PaperDivisorTangent
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.Geometry.NormalizedLatticeProjectiveConeAdapter

noncomputable section

universe u

variable {k E : Type u} [Field k] [CommRing E] {n d : ℕ}
variable {I : Ideal (MvPolynomial (Fin n) k)}
variable [Algebra k E]
variable [Algebra (MvPolynomial (Fin n) k ⧸ I) E]
variable [Algebra (MvPolynomial (Fin n) k) E]
variable [Algebra (MvPolynomial (Option (Fin d)) k) E]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) E]
variable [IsScalarTower k (MvPolynomial (Fin n) k) E]
variable [IsScalarTower k (MvPolynomial (Option (Fin d)) k) E]
variable [IsScalarTower (MvPolynomial (Fin n) k)
  (MvPolynomial (Fin n) k ⧸ I) E]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) E]
variable [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) E]

/-- Package the actual selected chart columns with the normalized lattice
certificate. The Laurent generic-fibre equality is derived from the same
chart's position, transverse, and raw-velocity identities; no tangent-cone
identity is supplied as a hypothesis. -/
theorem directSummandInput_of_actual_chart_columns
    (rho : E →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k E) = algebraMap k (LaurentSeries k)) :
    letI : Algebra E (LaurentSeries k) :=
      RingHom.toAlgebra' rho (by intro x y; exact mul_comm _ _)
    letI : Algebra k (LaurentSeries k) :=
      RingHom.toAlgebra' (algebraMap k (LaurentSeries k))
        (by intro x y; exact mul_comm _ _)
    letI : Module k (LaurentSeries k) := Algebra.toModule
    letI : SMul k (LaurentSeries k) :=
      (Algebra.toModule : Module k (LaurentSeries k)).toSMul
    letI : IsScalarTower k E (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq' hground.symm
    ∀ (qC : Fin (n + 1) → E)
    (q : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) (Fin d) (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (alpha : Fin d → PowerSeries k) (c : ℕ)
    (hcorrection : ∀ i, PowerSeries.derivative (R := k) (q i) - Z.mulVec alpha i =
      (PowerSeries.X : PowerSeries k) ^ c * tau i)
    (hposition : ∀ i, rho (qC i) =
      algebraMap (PowerSeries k) (LaurentSeries k) (q i))
    (htransverse : ∀ j i,
      coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
        (L := LaurentSeries k) (some j) (qC i) =
        algebraMap (PowerSeries k) (LaurentSeries k) (Z i j))
    (hraw : ∀ i, algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.derivative (R := k) (q i)) =
      coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
        (L := LaurentSeries k) none (qC i) +
        ∑ j : Fin d, algebraMap (PowerSeries k) (LaurentSeries k) (alpha j) *
          coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
            (L := LaurentSeries k) (some j) (qC i))
    (hq0chart : algebraMap E (LaurentSeries k) (qC 0) ≠ 0)
    (hchart : ∀ i, qC i.succ = qC 0 *
      algebraMap (MvPolynomial (Fin n) k ⧸ I) E
        (Ideal.Quotient.mk I (MvPolynomial.X i)))
    (chart : Fin (n + 1)) (hqchart : q chart = 1)
    (hq0 : q 0 ≠ 0)
    (axis : Fin n)
    (C : Matrix (FormalTangentColumn (Fin d)) (Fin (n + 1)) (PowerSeries k))
    (hCB : C * formalTangentMatrix q Z tau = 1)
    (haxis : ∀ j, PowerSeries.constantCoeff
      (formalTangentMatrix q Z tau axis.succ j) = 0)
    (hprime : I.IsPrime)
    (hclosure : dehomogenizedPoint (laurentColumn q) ∈
      MvPolynomial.zeroLocus (LaurentSeries k)
        (I.map (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin n))))
    (hsmooth : SmoothAffinePoint
      (I.map (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin n)))
      (dehomogenizedPoint (laurentColumn q))),
    ∃ D : DirectSummandInput (dimY := d + 1) I q
      (normalizedTangentLattice q Z tau), D.axis = axis := by
  intro qC q Z tau alpha c hcorrection hposition htransverse hraw
    hq0chart hchart chart hqchart hq0 axis C hCB haxis hprime hclosure hsmooth
  have hcone := genericFibre_normalizedTangentLattice_eq_actualProjectiveTangentCone
    (rho := rho) hground q Z tau alpha c hcorrection qC
    hposition htransverse hraw hq0chart hchart
  have hq0Laurent : laurentColumn q 0 ≠ 0 :=
    laurentColumn_ne_zero_of_ne_zero q hq0
  have harc : FormalProjectiveArcInClosure I q := by
    refine ⟨⟨chart, ?_⟩, ?_⟩
    · rw [hqchart]
      exact isUnit_one
    · exact (projectiveClosureAtZero_iff
        (I.map (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin n)))
        (laurentColumn q) hq0Laurent).mpr hclosure
  have hcomplemented : IsComplemented (normalizedTangentLattice q Z tau) :=
    normalizedTangentLattice_isComplemented q Z tau C hCB
  have hrank := normalizedTangentLattice_finrank q Z tau C hCB
  have hpoint : (fun i => rho (qC i)) = laurentColumn q := by
    funext i
    exact hposition i
  have hgenericTangentCone : genericFibre (K := LaurentSeries k)
      (normalizedTangentLattice q Z tau) =
      projectiveTangentCone (laurentColumn q)
        (zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
          (I.map (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin n)))) := by
    simpa [hpoint, scalarPolynomialMap] using hcone
  refine ⟨⟨axis, hcomplemented, ?_, hprime, hq0, harc, hsmooth,
    hgenericTangentCone, normalizedTangentLattice_residue_axis q Z tau axis haxis⟩, rfl⟩
  rw [hrank]
  simp [FormalTangentColumn]
  omega

end
end Stafford38.Geometry.DirectSummandInputOfActualChart
