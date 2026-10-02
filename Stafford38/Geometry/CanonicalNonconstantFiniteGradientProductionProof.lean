import Stafford38.Geometry.CanonicalFiniteGradientProjectiveCoordinates
import Stafford38.Geometry.FiniteGradientResidueExtension
import Stafford38.Geometry.FiniteGradientBoundaryProducer
import Stafford38.Geometry.FiniteGradientFromTangentInclusion

/-!
# One-row conormal data and finite-gradient adapters

`RegularizedOneRowConormalData` records the explicit affine conormal identity
used to extract a finite-gradient boundary certificate. This file proves the
finite-support and conormal-span conversion. The actual same-witness
constructor is `PaperActualWitnessConormalData.exists_regularizedOneRowConormalData_of_actual_witness`.
-/

namespace Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.FiniteGradientBoundaryProducer
open Stafford38.Geometry.FiniteGradientFromTangentInclusion
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.FiniteGradientResidueExtension
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.PointwiseConormalContainment
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The reusable one-row package for a normalized retained-place chart.
Its `conormal` field is the explicit affine statement at the completed
Laurent point. The projective and residue fields are retained as certificate
data; the extraction theorem uses `conormal` to find finite gradient
coefficients. `PaperActualWitnessConormalData` constructs it from the same
retained witness. -/
structure RegularizedOneRowConormalData
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin (m + 1) → PowerSeries K) where
  ell : Fin (m + 1) → PowerSeries K
  q_origin_ne : q 0 ≠ 0
  projective_annihilation :
    ∑ i, laurentColumn ell i * laurentColumn q i = 0
  base_vanish :
    ∀ f ∈ I.map (groundPolynomialMap (k := k) (K := K) (Fin m)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0
  conormal :
    coordinateCovector (fun i ↦ laurentColumn ell i.succ) ∈
      affineConormalSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (groundPolynomialMap (k := k) (K := K) (Fin m)))
  residue_axis :
    residueColumn (fun i : Fin m ↦ ell i.succ) =
      (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0)

/-- A regularized one-row conormal datum yields the finite gradient certificate
over the same residue-field extension.  The only mathematical input is the
explicit `RegularizedOneRowConormalData`; all finite equations and Laurent
coefficients are extracted by the checked affine conormal-span theorem. -/
theorem finiteGradientBoundaryCertificateOver_of_regularizedOneRowConormalData
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin (m + 1) → PowerSeries K)
    (W : RegularizedOneRowConormalData (k := k) (K := K) hm I q) :
    Nonempty (FiniteGradientBoundaryCertificateOver
      (k := k) (K := K) m hm I) := by
  let Iext := I.map
    (groundPolynomialMap (k := k) (K := K) (Fin m))
  let y := dehomogenizedPoint (laurentColumn q)
  let xi : Fin m → LaurentSeries K :=
    fun i ↦ laurentColumn W.ell i.succ
  obtain ⟨r, equations, coefficients, hgradient⟩ :=
    exists_fin_gradient_identity_of_mem_affineConormalSpace
      Iext y xi W.conormal
  exact ⟨{
    equationCount := r
    q := q
    ell := W.ell
    q_origin_ne := W.q_origin_ne
    projective_annihilation := W.projective_annihilation
    base_vanish := W.base_vanish
    equations := equations
    coefficients := coefficients
    gradient_identity := by
      intro i
      exact hgradient i
    residue_axis := W.residue_axis
  }⟩

/-- The finite-gradient certificate immediately supplies the terminal
conormal-axis witness.  This is a named adapter so a future retained-place
producer can target the smaller row datum directly. -/
theorem exists_groundConormalAxis_of_regularizedOneRowConormalData
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin (m + 1) → PowerSeries K)
    (W : RegularizedOneRowConormalData (k := k) (K := K) hm I q) :
    ∃ (y : Fin m → LaurentSeries K)
      (xi : Fin m → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) I ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  obtain ⟨certificate⟩ :=
    finiteGradientBoundaryCertificateOver_of_regularizedOneRowConormalData
      (k := k) (K := K) hm I q W
  exact exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver
    (k := k) (K := K) hm I certificate

#print axioms finiteGradientBoundaryCertificateOver_of_regularizedOneRowConormalData
#print axioms exists_groundConormalAxis_of_regularizedOneRowConormalData

end

end Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
