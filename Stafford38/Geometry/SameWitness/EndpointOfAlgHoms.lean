module
public import Stafford38.Geometry.ActualSameWitnessAffineFibreEndpoint

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.ActualAffineSmoothPointFromNumerator
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.ActualSameWitnessAffineFibreEndpoint

noncomputable section

universe u

/-- The affine smooth-fibre axis endpoint depends only on the two étale maps and their common ground field. -/
theorem axis_mem_smoothConormalFibreProjection_closure_of_algHoms
    {k E : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing E] [Algebra k E] {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) k)} [I.IsPrime]
    (φ : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] E)
    (ψ : MvPolynomial (Option (Fin d)) k →ₐ[k] E)
    (hφEtale : letI := φ.toRingHom.toAlgebra
      Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) E)
    (hψEtale : letI := ψ.toRingHom.toAlgebra
      Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) E)
    (rho : E →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k E) = algebraMap k (LaurentSeries k)) :
    letI := ψ.toRingHom.toAlgebra
    letI : IsScalarTower k (MvPolynomial (Option (Fin d)) k) E :=
      IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
    letI : Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) E := hψEtale
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
    (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (rows : Fin d ↪ Fin (n + 1)) (chart : Fin (n + 1)) (axis : Fin n)
    (a b : ℕ) (beta alpha : Fin d → k)
    (u₀ u₁ : MvPowerSeries (Fin (d + 1)) k)
    (hqchartPre : qPre chart = 1)
    (hdata : SelectedCoordinateAxisLiftData qPre rows chart 0 axis.succ
      a b beta alpha u₀ u₁)
    (hposition : ∀ i, rho (qC i) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (tiltedArc alpha (qPre i)))
    (htransverse : ∀ j i,
      coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
        (L := LaurentSeries k) (some j) (qC i) =
        algebraMap (PowerSeries k) (LaurentSeries k)
          (tiltedTransverseDerivativeMatrix alpha qPre i j))
    (hraw : ∀ i,
      algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.derivative (R := k) (tiltedArc alpha (qPre i))) =
      coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
        (L := LaurentSeries k) none (qC i) +
        ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
          (PowerSeries.C (alpha j)) *
            coordinateDerivation (k := k) (σ := Option (Fin d)) (B := E)
              (L := LaurentSeries k) (some j) (qC i))
    (hchart : ∀ i : Fin n,
      qC i.succ = qC 0 * φ (Ideal.Quotient.mk I (MvPolynomial.X i)))
    (p : MvPolynomial (Fin n) k)
    (fbar : MvPolynomial (Fin n) k ⧸ I)
    (hrep : Ideal.Quotient.mk I p = fbar)
    (hsmooth : Algebra.Smooth k (Localization.Away fbar))
    (hnumerator : MvPolynomial.eval
      (laurentColumn (fun i => tiltedArc alpha (qPre i)))
      (MvPolynomial.map (algebraMap k (LaurentSeries k))
        (homogenizeAtZero p)) ≠ 0),
    (fun i : Fin n => if i = axis then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection I)) := by
  intro qC qPre rows chart axis a b beta alpha u₀ u₁ hqchartPre hdata
    hposition htransverse hraw hchart p fbar hrep hsmooth hnumerator
  letI : Algebra (MvPolynomial (Fin n) k ⧸ I) E := φ.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin n) k) E :=
    (φ.toRingHom.comp (Ideal.Quotient.mk I)).toAlgebra
  letI : Algebra (MvPolynomial (Option (Fin d)) k) E :=
    ψ.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) E :=
    IsScalarTower.of_algebraMap_eq' (R := k)
      (S := MvPolynomial (Fin n) k ⧸ I) (A := E) φ.comp_algebraMap.symm
  letI : IsScalarTower k (MvPolynomial (Fin n) k) E :=
    IsScalarTower.of_algebraMap_eq' (R := k)
      (S := MvPolynomial (Fin n) k) (A := E) (by
        ext c
        change algebraMap k E c =
          φ (Ideal.Quotient.mk I (MvPolynomial.C c))
        rw [← φ.commutes c]
        congr 1)
  letI : IsScalarTower k (MvPolynomial (Option (Fin d)) k) E :=
    IsScalarTower.of_algebraMap_eq' (R := k)
      (S := MvPolynomial (Option (Fin d)) k) (A := E) ψ.comp_algebraMap.symm
  letI : IsScalarTower (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I) E :=
    IsScalarTower.of_algebraMap_eq' (R := MvPolynomial (Fin n) k)
      (S := MvPolynomial (Fin n) k ⧸ I) (A := E) (by
        apply RingHom.ext
        intro p
        change φ (Ideal.Quotient.mk I p) = φ (Ideal.Quotient.mk I p)
        rfl)
  letI : Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) E := hφEtale
  letI : Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) E := hψEtale
  have hchart' : ∀ i : Fin n,
      qC i.succ = qC 0 *
        algebraMap (MvPolynomial (Fin n) k ⧸ I) E
          (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    intro i
    calc
      qC i.succ = qC 0 * φ (Ideal.Quotient.mk I (MvPolynomial.X i)) := hchart i
      _ = qC 0 * algebraMap (MvPolynomial (Fin n) k ⧸ I) E
          (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
            congr 1
  exact axis_mem_smoothConormalFibreProjection_closure_of_actual_columns
    rho hground qC qPre rows chart axis a b beta alpha u₀ u₁ hqchartPre
    hdata hposition htransverse hraw hchart' p fbar hrep hsmooth hnumerator

end

end Stafford38.Geometry.SameWitness
