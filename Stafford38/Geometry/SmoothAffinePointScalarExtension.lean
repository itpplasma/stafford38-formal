import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Stafford38.Geometry.SmoothAffineConormal
import Stafford38.Geometry.ScalarExtensionPoints

set_option autoImplicit false

/-!
# Smooth affine points over the field of an arc

A field-valued point of the original affine quotient that avoids a smooth
principal open is a genuine Mathlib smooth point.  The argument base-changes
the smooth localization to the point's own field, then uses the canonical
polynomial-quotient base-change isomorphism.
-/

namespace Stafford38.Geometry.SmoothAffinePointScalarExtension

open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.ScalarExtensionPoints
open TensorProduct

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}

private noncomputable def quotientScalarEquiv
    (I : Ideal (MvPolynomial (Fin n) k)) :
    (MvPolynomial (Fin n) K ⧸
      I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) ≃ₐ[K]
      K ⊗[k] (MvPolynomial (Fin n) k ⧸ I) := by
  let P := MvPolynomial (Fin n) k
  let PK := MvPolynomial (Fin n) K
  let A := P ⧸ I
  let IK := I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))
  let J := I.map (Algebra.TensorProduct.includeRight :
    P →ₐ[k] K ⊗[k] P)
  let ePoly : K ⊗[k] P ≃ₐ[K] PK :=
    MvPolynomial.algebraTensorAlgEquiv k K
  have hmapAlg :
      (ePoly.toAlgHom.restrictScalars k).comp
        (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P) =
      MvPolynomial.mapAlgHom (Algebra.ofId k K) := by
    apply MvPolynomial.algHom_ext
    intro i
    change ePoly (1 ⊗ₜ[k] (MvPolynomial.X i : P)) =
      MvPolynomial.map (algebraMap k K) (MvPolynomial.X i)
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
    simp
  have hmap : ePoly.toRingHom.comp
      (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P).toRingHom =
      scalarPolynomialMap (k := k) (K := K) (Fin n) := by
    exact congrArg AlgHom.toRingHom hmapAlg
  have hIJ : IK = J.map ePoly.toRingHom := by
    change I.map (scalarPolynomialMap (k := k) (K := K) (Fin n)) =
      (I.map (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P)).map
        ePoly.toRingHom
    rw [← hmap]
    exact (Ideal.map_map
      (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P).toRingHom
      ePoly.toRingHom).symm

  let eQ := Ideal.quotientEquivAlg J IK ePoly hIJ
  let eB := Algebra.TensorProduct.tensorQuotientEquiv
    (R := k) (S := K) (T := P) (A := K) I
  exact (eB.trans eQ).symm


private theorem quotientScalarEquiv_mk
    (I : Ideal (MvPolynomial (Fin n) k)) (f : MvPolynomial (Fin n) k) :
    quotientScalarEquiv (k := k) (K := K) I
      (Ideal.Quotient.mk (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n)))
        (scalarPolynomialMap (k := k) (K := K) (Fin n) f)) =
      (1 : K) ⊗ₜ[k] Ideal.Quotient.mk I f := by
  let P := MvPolynomial (Fin n) k
  let PK := MvPolynomial (Fin n) K
  let J := I.map (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P)
  let IK := I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))
  let ePoly : K ⊗[k] P ≃ₐ[K] PK := MvPolynomial.algebraTensorAlgEquiv k K
  have hpoly : ePoly.symm (scalarPolynomialMap (k := k) (K := K) (Fin n) f) =
      Algebra.TensorProduct.includeRight f := by
    exact MvPolynomial.algebraTensorAlgEquiv_symm_map k K f
  have hmapAlg :
      (ePoly.toAlgHom.restrictScalars k).comp
        (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P) =
      MvPolynomial.mapAlgHom (Algebra.ofId k K) := by
    apply MvPolynomial.algHom_ext
    intro i
    change ePoly (1 ⊗ₜ[k] (MvPolynomial.X i : P)) =
      MvPolynomial.map (algebraMap k K) (MvPolynomial.X i)
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
    simp
  have hmap : ePoly.toRingHom.comp
      (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P).toRingHom =
      scalarPolynomialMap (k := k) (K := K) (Fin n) := by
    exact congrArg AlgHom.toRingHom hmapAlg
  have hIJ : IK = J.map ePoly.toRingHom := by
    change I.map (scalarPolynomialMap (k := k) (K := K) (Fin n)) =
      (I.map (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P)).map
        ePoly.toRingHom
    rw [← hmap]
    exact (Ideal.map_map
      (Algebra.TensorProduct.includeRight : P →ₐ[k] K ⊗[k] P).toRingHom
      ePoly.toRingHom).symm
  let eQ := Ideal.quotientEquivAlg J IK ePoly hIJ
  let eB := Algebra.TensorProduct.tensorQuotientEquiv
    (R := k) (S := K) (T := P) (A := K) I
  have hQ : eQ.symm (Ideal.Quotient.mk IK
      (scalarPolynomialMap (k := k) (K := K) (Fin n) f)) =
      Ideal.Quotient.mk J (Algebra.TensorProduct.includeRight f) := by
    apply eQ.injective
    calc
      eQ (eQ.symm (Ideal.Quotient.mk IK
          (scalarPolynomialMap (k := k) (K := K) (Fin n) f))) =
          Ideal.Quotient.mk IK
            (scalarPolynomialMap (k := k) (K := K) (Fin n) f) :=
        eQ.apply_symm_apply _
      _ = eQ (Ideal.Quotient.mk J
            (Algebra.TensorProduct.includeRight f)) := by
        change Ideal.Quotient.mk IK
            (scalarPolynomialMap (k := k) (K := K) (Fin n) f) =
          Ideal.Quotient.mk IK (ePoly (Algebra.TensorProduct.includeRight f))
        congr 1
        calc
          scalarPolynomialMap (k := k) (K := K) (Fin n) f =
              ePoly (ePoly.symm
                (scalarPolynomialMap (k := k) (K := K) (Fin n) f)) := by
            exact (ePoly.apply_symm_apply _).symm
          _ = ePoly (Algebra.TensorProduct.includeRight f) := by
            rw [← hpoly]
  calc
    eB.symm (eQ.symm (Ideal.Quotient.mk IK
        (scalarPolynomialMap (k := k) (K := K) (Fin n) f))) =
        eB.symm (Ideal.Quotient.mk J
          ((1 : K) ⊗ₜ[k] f)) := by rw [hQ]; congr 1
    _ = (1 : K) ⊗ₜ[k] Ideal.Quotient.mk I f := by
      exact Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul
        (R := k) K P K I (1 : K) f

/-- A smooth principal open over `k` remains smooth at every `K`-point that
avoids its defining equation.  The point is presented by its polynomial
coordinates; no smoothness of the point is assumed. -/
theorem smoothAffinePoint_of_smooth_away
    (I : Ideal (MvPolynomial (Fin n) k))
    (f : MvPolynomial (Fin n) k)
    (hsmooth : Algebra.Smooth k
      (Localization.Away (Ideal.Quotient.mk I f)))
    (y : Fin n → K)
    (hy : ∀ p ∈ I, MvPolynomial.eval₂ (algebraMap k K) y p = 0)
    (hf : MvPolynomial.eval₂ (algebraMap k K) y f ≠ 0) :
    SmoothAffinePoint (k := K)
      (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) y := by
  let P := MvPolynomial (Fin n) k
  let PK := MvPolynomial (Fin n) K
  let A := P ⧸ I
  let IK := I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))
  let fA : A := Ideal.Quotient.mk I f
  let fK : PK ⧸ IK := Ideal.Quotient.mk IK
    (scalarPolynomialMap (k := k) (K := K) (Fin n) f)
  have hker : IK ≤ RingHom.ker (MvPolynomial.aeval y).toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    change MvPolynomial.aeval y (scalarPolynomialMap (k := k) (K := K) (Fin n) q) = 0
    rw [MvPolynomial.aeval_eq_eval, eval_scalarPolynomialMap]
    exact hy q hq
  let e : (PK ⧸ IK) →ₐ[K] K :=
    Ideal.Quotient.liftₐ IK (MvPolynomial.aeval y) (by
      intro q hq
      exact RingHom.mem_ker.mp (hker hq))
  letI : Algebra.FinitePresentation K (PK ⧸ IK) :=
    Algebra.FinitePresentation.quotient IK.fg_of_isNoetherianRing
  have hnonzero : e fK ≠ 0 := by
    change MvPolynomial.eval y (scalarPolynomialMap (k := k) (K := K) (Fin n) f) ≠ 0
    simpa [eval_scalarPolynomialMap] using hf
  have hloc : Algebra.Smooth K (Localization.Away fK) := by
    letI : Algebra.Smooth k (Localization.Away fA) := hsmooth
    have hSmoothTensor : Algebra.Smooth K (K ⊗[k] Localization.Away fA) :=
      Algebra.Smooth.baseChange k (Localization.Away fA) K
    let eAway := IsLocalization.Away.tensorProductEquivTMulRight
      (R := k) (S := K) (A := A) fA (Localization.Away fA)
    let eQuot : (PK ⧸ IK) ≃ₐ[K] K ⊗[k] A :=
      quotientScalarEquiv (k := k) (K := K) I
    have hElement : eQuot fK = (1 : K) ⊗ₜ[k] fA := by
      exact quotientScalarEquiv_mk (k := k) (K := K) I f
    have hAwayTarget : Algebra.Smooth K
        (Localization.Away (eQuot fK)) := by
      rw [hElement]
      letI : Algebra.Smooth K (K ⊗[k] Localization.Away fA) := hSmoothTensor
      exact Algebra.Smooth.of_equiv eAway
    let phi : (PK ⧸ IK) →ₐ[K] Localization.Away (eQuot fK) :=
      (IsScalarTower.toAlgHom K (K ⊗[k] A)
        (Localization.Away (eQuot fK))).comp eQuot.toAlgHom
    letI : Algebra (PK ⧸ IK) (Localization.Away (eQuot fK)) :=
      phi.toRingHom.toAlgebra
    letI : IsScalarTower K (PK ⧸ IK) (Localization.Away (eQuot fK)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        change algebraMap K (Localization.Away (eQuot fK)) x =
          phi (algebraMap K (PK ⧸ IK) x)
        rw [AlgHom.commutes]
    let eLoc := IsLocalization.algEquivOfAlgEquiv
      (A := K) (R := PK ⧸ IK) (M := Submonoid.powers fK)
      (S := Localization.Away fK) (P := K ⊗[k] A)
      (T := Submonoid.powers (eQuot fK))
      (Q := Localization.Away (eQuot fK)) eQuot (by
        simp [Submonoid.map_powers])
    letI : Algebra.Smooth K (Localization.Away (eQuot fK)) := hAwayTarget
    exact Algebra.Smooth.of_equiv eLoc.symm
  refine ⟨e, ?_, ?_⟩
  · intro p
    change (Ideal.Quotient.liftₐ IK (MvPolynomial.aeval y) (by
      intro q hq
      exact RingHom.mem_ker.mp (hker hq))) (Ideal.Quotient.mk IK p) =
      MvPolynomial.aeval y p
    simp [Ideal.Quotient.liftₐ_apply]
  · have hopen : (⟨RingHom.ker e.toRingHom, RingHom.ker_isPrime e⟩ :
        PrimeSpectrum (PK ⧸ IK)) ∈ PrimeSpectrum.basicOpen fK := by
      rw [PrimeSpectrum.mem_basicOpen]
      intro hker
      exact hnonzero (RingHom.mem_ker.mp hker)
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hloc) hopen

/-- A field-valued point of the original affine quotient which avoids a
smooth principal open is itself a genuine Mathlib smooth point over its field
of values.  The coordinates in the conclusion are the images of the original
affine generators; no projective-chart quotient is identified with the
original coordinate ring. -/
theorem smoothAffinePoint_of_quotient_point_avoiding_smooth_away
    {L : Type*} [Field L] [Algebra k L]
    (I : Ideal (MvPolynomial (Fin n) k))
    (fbar : MvPolynomial (Fin n) k ⧸ I)
    (hsmooth : Algebra.Smooth k (Localization.Away fbar))
    (φ : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] L)
    (havoid : φ fbar ≠ 0) :
    SmoothAffinePoint (k := L)
      (I.map (scalarPolynomialMap (k := k) (K := L) (Fin n)))
      (fun i ↦ φ (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
  obtain ⟨f, hfbar⟩ := Ideal.Quotient.mk_surjective fbar
  have havoid_f : φ (Ideal.Quotient.mk I f) ≠ 0 := by
    simpa only [hfbar] using havoid
  let φP : MvPolynomial (Fin n) k →ₐ[k] L :=
    φ.comp (Ideal.Quotient.mkₐ k I)
  have hI : ∀ p ∈ I, φP p = 0 := by
    intro p hp
    change φ (Ideal.Quotient.mk I p) = 0
    have hmk : Ideal.Quotient.mk I p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [hmk, map_zero]
  have hf : φP f ≠ 0 := by
    simpa [φP] using havoid_f
  have heval : ∀ p : MvPolynomial (Fin n) k,
      MvPolynomial.eval₂ (algebraMap k L)
          (fun i ↦ φP (MvPolynomial.X i)) p = φP p := by
    intro p
    have hunique := MvPolynomial.aeval_unique φP
    have hpoint : φP = MvPolynomial.aeval (fun i ↦ φP (MvPolynomial.X i)) := by
      convert hunique using 1 <;> rfl
    have heq := congrArg (fun ψ : MvPolynomial (Fin n) k →ₐ[k] L => ψ p)
      hpoint.symm
    simpa only [MvPolynomial.aeval_def] using heq
  have hy : ∀ p ∈ I,
      MvPolynomial.eval₂ (algebraMap k L)
        (fun i ↦ φ (Ideal.Quotient.mk I (MvPolynomial.X i))) p = 0 := by
    intro p hp
    change MvPolynomial.eval₂ (algebraMap k L)
      (fun i ↦ φP (MvPolynomial.X i)) p = 0
    rw [heval, hI p hp]
  have hfL : MvPolynomial.eval₂ (algebraMap k L)
      (fun i ↦ φ (Ideal.Quotient.mk I (MvPolynomial.X i))) f ≠ 0 := by
    change MvPolynomial.eval₂ (algebraMap k L)
      (fun i ↦ φP (MvPolynomial.X i)) f ≠ 0
    rw [heval]
    exact hf
  have hhsmooth : Algebra.Smooth k
      (Localization.Away (Ideal.Quotient.mk I f)) := by
    cases hfbar
    exact hsmooth
  exact smoothAffinePoint_of_smooth_away (k := k) (K := L)
    I f hhsmooth
    (fun i ↦ φ (Ideal.Quotient.mk I (MvPolynomial.X i)))
    hy hfL

/-- On a prime affine variety over a perfect field, the generic smooth-open
producer supplies a principal open that can be used with the point-map
criterion above.  This keeps the open in the original affine quotient, so a
caller may feed it the map obtained from the actual chart-overlap ratios. -/
theorem exists_generic_smooth_open_point_criterion
    {L : Type*} [Field L] [Algebra k L]
    (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime] [PerfectField k]
    (φ : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] L) :
    ∃ g : (MvPolynomial (Fin n) k ⧸ I), g ≠ 0 ∧
      Algebra.Smooth k (Localization.Away g) ∧
      ∀ _ : φ g ≠ 0,
        SmoothAffinePoint (k := L)
          (I.map (scalarPolynomialMap (k := k) (K := L) (Fin n)))
          (fun i ↦ φ (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
  obtain ⟨g, hg, hsmooth⟩ :=
    Stafford38.Geometry.exists_nonzero_smooth_away_quotient I
  exact ⟨g, hg, hsmooth, fun havoid =>
    smoothAffinePoint_of_quotient_point_avoiding_smooth_away
      (k := k) I g hsmooth φ havoid⟩


end
end Stafford38.Geometry.SmoothAffinePointScalarExtension
