import Stafford38.Geometry.CorrectedNormalizedTangentLattice
import Stafford38.Geometry.EtaleProjectiveTangentComparison
import Stafford38.Geometry.CorrectedVelocitySpan

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.NormalizedLatticeProjectiveConeAdapter

open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.GeneralTangentLimitCriterion
open Stafford38.Geometry.PaperDivisorTangent
open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.GeometryFormalDivisorTangent

noncomputable section

universe u

variable {k C : Type u} [Field k] [CommRing C] {n d : ℕ}
variable {I : Ideal (MvPolynomial (Fin n) k)}
variable [Algebra k C]
variable [Algebra (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra (MvPolynomial (Fin n) k) C]
variable [Algebra (MvPolynomial (Option (Fin d)) k) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k) C]
variable [IsScalarTower k (MvPolynomial (Option (Fin d)) k) C]
variable [IsScalarTower (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) C]

/-- Compare the formal normalized tangent lattice with the projective cone
computed from the actual parameter derivations on the common étale chart.
The arc/chart compatibility inputs are the position, transverse, and raw
velocity column identities. All coordinate derivations and the comparison
cone use one shared map/tower context. -/
theorem genericFibre_normalizedTangentLattice_eq_actualProjectiveTangentCone
    (rho : C →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k C) = algebraMap k (LaurentSeries k)) :
    letI : Algebra C (LaurentSeries k) :=
      RingHom.toAlgebra' rho (by intro x y; exact mul_comm _ _)
    letI : Algebra k (LaurentSeries k) :=
      RingHom.toAlgebra' (algebraMap k (LaurentSeries k)) (by intro x y; exact mul_comm _ _)
    letI : Module k (LaurentSeries k) := Algebra.toModule
    letI : SMul k (LaurentSeries k) :=
      (Algebra.toModule : Module k (LaurentSeries k)).toSMul
    letI : IsScalarTower k C (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq' hground.symm
    ∀ (q : Fin (n + 1) → PowerSeries k)
      (Z : Matrix (Fin (n + 1)) (Fin d) (PowerSeries k))
      (tau : Fin (n + 1) → PowerSeries k)
      (alpha : Fin d → PowerSeries k) (c : ℕ),
      (∀ i, PowerSeries.derivative k (q i) - Z.mulVec alpha i =
        (PowerSeries.X : PowerSeries k) ^ c * tau i) →
      ∀ (qC : Fin (n + 1) → C),
      (∀ i, rho (qC i) = algebraMap (PowerSeries k) (LaurentSeries k) (q i)) →
      (∀ j i, Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := C) (L := LaurentSeries k)
          (some j) (qC i) = algebraMap (PowerSeries k) (LaurentSeries k) (Z i j)) →
      (∀ i, algebraMap (PowerSeries k) (LaurentSeries k)
          (PowerSeries.derivative k (q i)) =
        Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := C) (L := LaurentSeries k)
          (none : Option (Fin d)) (qC i) +
          ∑ j : Fin d, algebraMap (PowerSeries k) (LaurentSeries k) (alpha j) *
            Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
              (k := k) (σ := Option (Fin d)) (B := C) (L := LaurentSeries k)
              (some j) (qC i)) →
      algebraMap C (LaurentSeries k) (qC 0) ≠ 0 →
      (∀ i, qC i.succ = qC 0 *
        algebraMap (MvPolynomial (Fin n) k ⧸ I) C
          (Ideal.Quotient.mk I (MvPolynomial.X i))) →
      genericFibre (normalizedTangentLattice q Z tau) =
        projectiveTangentCone (fun i => rho (qC i))
          (zariskiTangentSpace (dehomogenizedPoint (fun i => rho (qC i)))
            (I.map (MvPolynomial.map (algebraMap k (LaurentSeries k))))) := by
  intro q Z tau alpha c hcorrection qC hposition htransverse hraw hq0 hchart
  classical
  letI : Algebra C (LaurentSeries k) :=
    RingHom.toAlgebra' rho (by intro x y; exact mul_comm _ _)
  letI : Algebra k (LaurentSeries k) :=
    RingHom.toAlgebra' (algebraMap k (LaurentSeries k)) (by intro x y; exact mul_comm _ _)
  letI : Module k (LaurentSeries k) := Algebra.toModule
  letI : SMul k (LaurentSeries k) :=
    (Algebra.toModule : Module k (LaurentSeries k)).toSMul
  letI : IsScalarTower k C (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hground.symm
  let quotientMap : (MvPolynomial (Fin n) k ⧸ I) →+* LaurentSeries k :=
    rho.comp (algebraMap (MvPolynomial (Fin n) k ⧸ I) C)
  let polynomialMap : MvPolynomial (Fin n) k →+* LaurentSeries k :=
    rho.comp (algebraMap (MvPolynomial (Fin n) k) C)
  let chartMap : MvPolynomial (Option (Fin d)) k →+* LaurentSeries k :=
    rho.comp (algebraMap (MvPolynomial (Option (Fin d)) k) C)
  letI : Algebra (MvPolynomial (Fin n) k ⧸ I) (LaurentSeries k) :=
    RingHom.toAlgebra' quotientMap (by intro x y; exact mul_comm _ _)
  letI : Algebra (MvPolynomial (Fin n) k) (LaurentSeries k) :=
    RingHom.toAlgebra' polynomialMap (by intro x y; exact mul_comm _ _)
  letI : Algebra (MvPolynomial (Option (Fin d)) k) (LaurentSeries k) :=
    RingHom.toAlgebra' chartMap (by intro x y; exact mul_comm _ _)

  have hQCL : algebraMap (MvPolynomial (Fin n) k ⧸ I) (LaurentSeries k) =
      (algebraMap C (LaurentSeries k)).comp
        (algebraMap (MvPolynomial (Fin n) k ⧸ I) C) := rfl
  have hPolyCL : algebraMap (MvPolynomial (Fin n) k) (LaurentSeries k) =
      (algebraMap C (LaurentSeries k)).comp
        (algebraMap (MvPolynomial (Fin n) k) C) := rfl
  have hChartCL : algebraMap (MvPolynomial (Option (Fin d)) k) (LaurentSeries k) =
      (algebraMap C (LaurentSeries k)).comp
        (algebraMap (MvPolynomial (Option (Fin d)) k) C) := rfl
  letI : IsScalarTower (MvPolynomial (Fin n) k ⧸ I) C (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hQCL
  letI : IsScalarTower (MvPolynomial (Fin n) k) C (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hPolyCL
  letI : IsScalarTower (MvPolynomial (Option (Fin d)) k) C (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hChartCL

  have hKQ : algebraMap k (LaurentSeries k) =
      (algebraMap (MvPolynomial (Fin n) k ⧸ I) (LaurentSeries k)).comp
        (algebraMap k (MvPolynomial (Fin n) k ⧸ I)) := by
    calc
      algebraMap k (LaurentSeries k) = rho.comp (algebraMap k C) := hground.symm
      _ = rho.comp ((algebraMap (MvPolynomial (Fin n) k ⧸ I) C).comp
            (algebraMap k (MvPolynomial (Fin n) k ⧸ I))) := by
              congr 1
              exact IsScalarTower.algebraMap_eq k
                (MvPolynomial (Fin n) k ⧸ I) C
      _ = (rho.comp (algebraMap (MvPolynomial (Fin n) k ⧸ I) C)).comp
            (algebraMap k (MvPolynomial (Fin n) k ⧸ I)) := rfl
      _ = (algebraMap (MvPolynomial (Fin n) k ⧸ I) (LaurentSeries k)).comp
            (algebraMap k (MvPolynomial (Fin n) k ⧸ I)) := rfl
  letI : IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hKQ

  have hKPoly : algebraMap k (LaurentSeries k) =
      (algebraMap (MvPolynomial (Fin n) k) (LaurentSeries k)).comp
        (algebraMap k (MvPolynomial (Fin n) k)) := by
    calc
      algebraMap k (LaurentSeries k) = rho.comp (algebraMap k C) := hground.symm
      _ = rho.comp ((algebraMap (MvPolynomial (Fin n) k) C).comp
            (algebraMap k (MvPolynomial (Fin n) k))) := by
              congr 1
              exact IsScalarTower.algebraMap_eq k (MvPolynomial (Fin n) k) C
      _ = (rho.comp (algebraMap (MvPolynomial (Fin n) k) C)).comp
            (algebraMap k (MvPolynomial (Fin n) k)) := rfl
      _ = (algebraMap (MvPolynomial (Fin n) k) (LaurentSeries k)).comp
            (algebraMap k (MvPolynomial (Fin n) k)) := rfl
  letI : IsScalarTower k (MvPolynomial (Fin n) k) (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hKPoly

  have hKChart : algebraMap k (LaurentSeries k) =
      (algebraMap (MvPolynomial (Option (Fin d)) k) (LaurentSeries k)).comp
        (algebraMap k (MvPolynomial (Option (Fin d)) k)) := by
    calc
      algebraMap k (LaurentSeries k) = rho.comp (algebraMap k C) := hground.symm
      _ = rho.comp ((algebraMap (MvPolynomial (Option (Fin d)) k) C).comp
            (algebraMap k (MvPolynomial (Option (Fin d)) k))) := by
              congr 1
              exact IsScalarTower.algebraMap_eq k
                (MvPolynomial (Option (Fin d)) k) C
      _ = (rho.comp (algebraMap (MvPolynomial (Option (Fin d)) k) C)).comp
            (algebraMap k (MvPolynomial (Option (Fin d)) k)) := rfl
      _ = (algebraMap (MvPolynomial (Option (Fin d)) k) (LaurentSeries k)).comp
            (algebraMap k (MvPolynomial (Option (Fin d)) k)) := rfl
  letI : IsScalarTower k (MvPolynomial (Option (Fin d)) k) (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hKChart

  have hPolyQ : algebraMap (MvPolynomial (Fin n) k) (LaurentSeries k) =
      (algebraMap (MvPolynomial (Fin n) k ⧸ I) (LaurentSeries k)).comp
        (algebraMap (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I)) := by
    calc
      algebraMap (MvPolynomial (Fin n) k) (LaurentSeries k) =
          (algebraMap C (LaurentSeries k)).comp
            (algebraMap (MvPolynomial (Fin n) k) C) := hPolyCL
      _ = (algebraMap C (LaurentSeries k)).comp
            ((algebraMap (MvPolynomial (Fin n) k ⧸ I) C).comp
              (algebraMap (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I))) := by
                congr 1
                exact IsScalarTower.algebraMap_eq
                  (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I) C
      _ = (algebraMap (MvPolynomial (Fin n) k ⧸ I) (LaurentSeries k)).comp
            (algebraMap (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I)) := rfl
  letI : IsScalarTower (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I) (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' hPolyQ

  let A : PowerSeries k →+* LaurentSeries k :=
    algebraMap (PowerSeries k) (LaurentSeries k)
  let qL : Fin (n + 1) → LaurentSeries k := fun i => A (q i)
  let zL : Fin d → (Fin (n + 1) → LaurentSeries k) := fun j i => A (Z i j)
  let rawL : Fin (n + 1) → LaurentSeries k := fun i =>
    A (PowerSeries.derivative k (q i))
  let dzero : Fin (n + 1) → LaurentSeries k := fun i =>
    Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
      (k := k) (σ := Option (Fin d)) (B := C) (L := LaurentSeries k)
      (none : Option (Fin d)) (qC i)
  let dz : Fin d → (Fin (n + 1) → LaurentSeries k) := fun j i =>
    Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
      (k := k) (σ := Option (Fin d)) (B := C) (L := LaurentSeries k)
      (some j) (qC i)
  let fixed : Option (Fin d) → (Fin (n + 1) → LaurentSeries k)
    | none => qL
    | some j => zL j
  let coeff : Option (Fin d) → LaurentSeries k
    | none => 0
    | some j => A (alpha j)
  let sourceColumns : FormalTangentColumn (Fin d) →
      (Fin (n + 1) → LaurentSeries k) :=
    fun j i => A (formalTangentMatrix q Z
      (fun i => PowerSeries.derivative k (q i)) i j)
  let chartColumns : Option (Option (Fin d)) →
      (Fin (n + 1) → LaurentSeries k)
    | none => fun i => rho (qC i)
    | some j => fun i =>
        Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := C) (L := LaurentSeries k) j (qC i)

  have hgeneric :=
    Stafford38.Geometry.CorrectedNormalizedTangentLattice.genericFibre_normalizedTangentLattice_eq_span_derivative
      q Z tau alpha c hcorrection
  have hsourceSet : Set.range sourceColumns = Set.range fixed ∪ {rawL} := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl u => exact Or.inl ⟨none, rfl⟩
      | inr j =>
        cases j with
        | inl j => exact Or.inl ⟨some j, rfl⟩
        | inr u => exact Or.inr (Set.mem_singleton _)
    · intro hv
      rcases hv with ⟨j, hj⟩ | hv
      · rcases j with _ | j
        · exact ⟨Sum.inl (), hj⟩
        · exact ⟨Sum.inr (Sum.inl j), hj⟩
      · rcases Set.mem_singleton_iff.mp hv with rfl
        exact ⟨Sum.inr (Sum.inr ()), rfl⟩
  have hchartSet : Set.range chartColumns = Set.range fixed ∪ {dzero} := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      rcases j with _ | j
      · refine Or.inl ⟨none, ?_⟩
        funext i
        exact (hposition i).symm
      · cases j with
        | none => exact Or.inr (Set.mem_singleton _)
        | some j =>
            refine Or.inl ⟨some j, ?_⟩
            funext i
            exact (htransverse j i).symm
    · intro hv
      rcases hv with ⟨j, hj⟩ | hv
      · rcases j with _ | j
        · refine ⟨none, ?_⟩
          funext i
          exact (hposition i).trans (congrFun hj i)
        · refine ⟨some (some j), ?_⟩
          funext i
          exact (htransverse j i).trans (congrFun hj i)
      · rcases Set.mem_singleton_iff.mp hv with rfl
        exact ⟨some none, rfl⟩
  have hsum (i : Fin (n + 1)) :
      (∑ a : Option (Fin d), coeff a * fixed a i) =
        ∑ j : Fin d, A (alpha j) * dz j i := by
    rw [Fintype.sum_option]
    simp only [coeff, fixed, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    change A (alpha j) * A (Z i j) = A (alpha j) * dz j i
    exact congrArg (fun x : LaurentSeries k => A (alpha j) * x)
      (htransverse j i).symm
  have hvelocity : rawL - (∑ a, coeff a • fixed a) =
      (1 : LaurentSeries k) • dzero := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, one_mul]
    dsimp only [rawL]
    change A (PowerSeries.derivative k (q i)) -
        ∑ a : Option (Fin d), coeff a * fixed a i = dzero i
    have hraw' : A (PowerSeries.derivative k (q i)) =
        dzero i + ∑ j : Fin d, A (alpha j) * dz j i := by
      simpa [A, dz, dzero] using hraw i
    rw [hsum, hraw']
    ring
  have hspan :
      Submodule.span (LaurentSeries k) (Set.range fixed ∪ {dzero}) =
        Submodule.span (LaurentSeries k) (Set.range fixed ∪ {rawL}) :=
    Stafford38.Geometry.CorrectedVelocitySpan.span_range_union_singleton_eq_of_corrected_velocity
      fixed coeff dzero rawL (1 : LaurentSeries k) (by norm_num) hvelocity
  have hcone :=
    Stafford38.Geometry.EtaleProjectiveTangentComparison.FiniteParameters.projectiveTangentCone_eq_span_chartDerivation_columns
      (σ := Option (Fin d)) (I := I) (C := C) (L := LaurentSeries k)
      (q := qC) hq0 hchart
  have hchartColumns : chartColumns = fun j i =>
      match j with
      | none => rho (qC i)
      | some j => Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Option (Fin d)) (B := C) (L := LaurentSeries k) j (qC i) := by
    funext j i
    cases j <;> rfl
  calc
    genericFibre (normalizedTangentLattice q Z tau) =
        Submodule.span (LaurentSeries k) (Set.range sourceColumns) := by
          simpa [sourceColumns, A] using hgeneric
    _ = Submodule.span (LaurentSeries k) (Set.range fixed ∪ {rawL}) :=
      congrArg (Submodule.span (LaurentSeries k)) hsourceSet
    _ = Submodule.span (LaurentSeries k) (Set.range fixed ∪ {dzero}) := hspan.symm
    _ = Submodule.span (LaurentSeries k) (Set.range chartColumns) := by
      rw [hchartSet]
    _ = projectiveTangentCone (fun i => rho (qC i))
        (zariskiTangentSpace
          (dehomogenizedPoint (fun i => rho (qC i)))
          (I.map (MvPolynomial.map (algebraMap k (LaurentSeries k))))) := by
            have hρ : (algebraMap C (LaurentSeries k) : C →+* LaurentSeries k) = rho := rfl
            rw [hchartColumns, ← hρ]
            convert hcone.symm using 1
            congr 2
            funext j i
            cases j <;> rfl

end
end Stafford38.Geometry.NormalizedLatticeProjectiveConeAdapter
