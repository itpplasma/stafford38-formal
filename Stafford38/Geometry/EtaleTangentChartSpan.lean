import Stafford38.Geometry.EtaleCotangentBasis
import Stafford38.Geometry.EtaleTangentKernel
import Stafford38.Geometry.EtaleDerivationExtension
import Stafford38.Geometry.GenericPointKaehlerConormal
import Mathlib.Algebra.MvPolynomial.Derivation

set_option autoImplicit false
open scoped TensorProduct

namespace Stafford38.Geometry.EtaleTangentChartSpan

noncomputable section

namespace FiniteParameters

variable {k : Type*} [Field k]
variable {n : ℕ}
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {I : Ideal (MvPolynomial (Fin n) k)}
variable {C L : Type*} [CommRing C] [Field L]
variable [Algebra k C] [Algebra (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra C L] [Algebra (MvPolynomial (Fin n) k ⧸ I) L] [Algebra k L]
variable [IsScalarTower (MvPolynomial (Fin n) k ⧸ I) C L]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) L] [IsScalarTower k C L]
variable [Algebra (MvPolynomial (Fin n) k) L]
variable [IsScalarTower k (MvPolynomial (Fin n) k) L]
variable [IsScalarTower (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I) L]
variable [Algebra (MvPolynomial (σ) k) C]
variable [IsScalarTower k (MvPolynomial (σ) k) C]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra.FormallyEtale (MvPolynomial (σ) k) C]

/-- Every equation-defined tangent vector factors through an actual formally
étale polynomial chart.  Its coordinates are a linear combination of the
parameter-coordinate derivations of that chart.  The source chart algebra `C`
may be a further localization of a local étale chart, provided both formal
étale structures are retained. -/
theorem tangentVector_eq_sum_parameterDerivations
    (q v : Fin n → L)
    (hq : ∀ i, q i = algebraMap C L
      (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i))))
    (hv : v ∈ Stafford38.Geometry.AffineConormalSpan.zariskiTangentSpace q
      (I.map (MvPolynomial.map (algebraMap k L))))
    : ∃ coeff : σ → L, ∀ i,
      v i = ∑ j, coeff j *
        Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := σ) (B := C) (L := L) j
          (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
            (Ideal.Quotient.mk I (MvPolynomial.X i)) ) := by
  have hi : ∀ i, algebraMap (MvPolynomial (Fin n) k) L
      (MvPolynomial.X i) = q i := by
    intro i
    calc
      algebraMap (MvPolynomial (Fin n) k) L (MvPolynomial.X i) =
          algebraMap (MvPolynomial (Fin n) k ⧸ I) L
            (algebraMap (MvPolynomial (Fin n) k)
              (MvPolynomial (Fin n) k ⧸ I) (MvPolynomial.X i)) :=
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k)
          (MvPolynomial (Fin n) k ⧸ I) L (MvPolynomial.X i)
      _ = algebraMap C L (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
          (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
        rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k ⧸ I) C L]
        simp only [Ideal.Quotient.algebraMap_eq]
      _ = q i := (hq i).symm
  have halgHom : IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) L =
      MvPolynomial.aeval q := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [IsScalarTower.coe_toAlgHom', MvPolynomial.aeval_X]
    exact hi i
  have halg : ∀ p : MvPolynomial (Fin n) k,
      algebraMap (MvPolynomial (Fin n) k) L p = MvPolynomial.aeval q p := by
    intro p
    exact congrArg (fun f : MvPolynomial (Fin n) k →ₐ[k] L => f p) halgHom
  let D : Derivation k (MvPolynomial (Fin n) k) L := MvPolynomial.mkDerivation k v
  have hDI : ∀ f ∈ I, D f = 0 := by
    intro f hf
    exact Stafford38.Geometry.EtaleTangentKernel.mkDerivation_vanishes_of_mem_zariskiTangentSpace
      I q v halg hv f hf
  let DA : Derivation k (MvPolynomial (Fin n) k ⧸ I) L :=
    Stafford38.Geometry.GenericPointKaehlerConormal.quotientDerivation D hDI
  let DC : Derivation k C L :=
    Stafford38.Geometry.EtaleDerivationExtension.extendDerivation DA
  refine ⟨fun j => DC
      (algebraMap (MvPolynomial (σ) k) C (MvPolynomial.X j)), ?_⟩
  intro i
  have hcomp : DC (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
      (Ideal.Quotient.mk I (MvPolynomial.X i))) =
      D (MvPolynomial.X i) := by
    calc
      DC (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i))) =
          DA (Ideal.Quotient.mk I (MvPolynomial.X i)) :=
        Stafford38.Geometry.EtaleDerivationExtension.extendDerivation_algebraMap DA _
      _ = D (MvPolynomial.X i) :=
        Stafford38.Geometry.GenericPointKaehlerConormal.quotientDerivation_mk D hDI _
  have hcomp' : D (MvPolynomial.X i) =
      DC (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
    simpa [D, MvPolynomial.mkDerivation_X] using hcomp.symm
  have hsum_eval :
      (∑ j, DC (algebraMap (MvPolynomial (σ) k) C
        (MvPolynomial.X j)) •
          Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := σ) (B := C) (L := L) j)
        (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
          (Ideal.Quotient.mk I (MvPolynomial.X i))) =
      ∑ j, DC (algebraMap (MvPolynomial (σ) k) C
        (MvPolynomial.X j)) *
          Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := σ) (B := C) (L := L) j
          (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
            (Ideal.Quotient.mk I (MvPolynomial.X i)) ) := by
    change Derivation.coeFnAddMonoidHom (∑ j, _) _ = _
    rw [map_sum]
    simp [Derivation.coeFnAddMonoidHom, smul_eq_mul]
  have hdecomp :=
    Stafford38.Geometry.EtaleCotangentBasis.derivation_eq_sum_coordinateDerivations
      (k := k) (σ := σ) (B := C) (L := L) DC
  calc
    v i = D (MvPolynomial.X i) := by simp [D]
    _ = DC (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i))) := hcomp'
    _ = (∑ j, (DC (algebraMap (MvPolynomial (σ) k) C
        (MvPolynomial.X j)) •
          Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := σ) (B := C) (L := L) j))
          (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
            (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
      exact congrArg (fun E : Derivation k C L =>
        E (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
          (Ideal.Quotient.mk I (MvPolynomial.X i)))) hdecomp
    _ = ∑ j, DC (algebraMap (MvPolynomial (σ) k) C
        (MvPolynomial.X j)) *
          Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
            (k := k) (σ := σ) (B := C) (L := L) j
          (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
            (Ideal.Quotient.mk I (MvPolynomial.X i))) := hsum_eval


/-- The genuine parameter derivations of a common étale chart span exactly
 the equation-defined tangent space of the original affine presentation.
 The ambient number of coordinates and the number of parameters are independent. -/
theorem zariskiTangentSpace_eq_span_parameterDerivations
    [Algebra (MvPolynomial (Fin n) k) C]
    [IsScalarTower k (MvPolynomial (Fin n) k) C]
    [IsScalarTower (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I) C]
    [IsScalarTower (MvPolynomial (Fin n) k) C L]
    (q : Fin n → L)
    (hq : ∀ i, q i = algebraMap C L
      (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i)))) :
    Stafford38.Geometry.AffineConormalSpan.zariskiTangentSpace q
      (I.map (MvPolynomial.map (algebraMap k L))) =
      Submodule.span L (Set.range fun j : σ => fun i : Fin n =>
        Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := σ) (B := C) (L := L) j
          (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
            (Ideal.Quotient.mk I (MvPolynomial.X i)))) := by
  classical
  let cols : σ → Fin n → L := fun j i =>
    Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
      (k := k) (σ := σ) (B := C) (L := L) j
      (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i)))
  change _ = Submodule.span L (Set.range cols)
  have halg : ∀ p : MvPolynomial (Fin n) k,
      algebraMap (MvPolynomial (Fin n) k) L p = MvPolynomial.aeval q p := by
    have hhom : IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) L =
        MvPolynomial.aeval q := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [IsScalarTower.coe_toAlgHom', MvPolynomial.aeval_X, hq i]
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k) C L,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k)
          (MvPolynomial (Fin n) k ⧸ I) C]
      simp only [Ideal.Quotient.algebraMap_eq]
    intro p
    exact congrArg (fun f : MvPolynomial (Fin n) k →ₐ[k] L => f p) hhom
  have hI : ∀ f ∈ I, algebraMap (MvPolynomial (Fin n) k) C f = 0 := by
    intro f hf
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I) C]
    simp only [Ideal.Quotient.algebraMap_eq]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  apply le_antisymm
  · intro v hv
    obtain ⟨coeff, hcoeff⟩ := tangentVector_eq_sum_parameterDerivations (σ := σ) q v hq hv
    have hvrepr : v = ∑ j, coeff j • cols j := by
      ext i
      simpa [cols, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoeff i
    rw [hvrepr]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have h := Stafford38.Geometry.EtaleTangentKernel.chartDerivation_mem_zariskiTangentSpace
      (Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
        (k := k) (σ := σ) (B := C) (L := L) j) I q halg hI
    have heq : cols j = (fun i =>
        (Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := σ) (B := C) (L := L) j).compAlgebraMap
            (MvPolynomial (Fin n) k) (MvPolynomial.X i)) := by
      ext i
      simp only [cols, Derivation.compAlgebraMap_apply,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k)
          (MvPolynomial (Fin n) k ⧸ I) C, Ideal.Quotient.algebraMap_eq]
    exact heq ▸ h

end FiniteParameters

variable {k : Type*} [Field k]
variable {n r : ℕ}
variable {I : Ideal (MvPolynomial (Fin n) k)}
variable {C L : Type*} [CommRing C] [Field L]
variable [Algebra k C] [Algebra (MvPolynomial (Fin n) k ⧸ I) C]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra C L] [Algebra (MvPolynomial (Fin n) k ⧸ I) L] [Algebra k L]
variable [IsScalarTower (MvPolynomial (Fin n) k ⧸ I) C L]
variable [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) L] [IsScalarTower k C L]
variable [Algebra (MvPolynomial (Fin n) k) L]
variable [IsScalarTower k (MvPolynomial (Fin n) k) L]
variable [IsScalarTower (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I) L]
variable [Algebra (MvPolynomial (Fin r) k) C]
variable [IsScalarTower k (MvPolynomial (Fin r) k) C]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) C]
variable [Algebra.FormallyEtale (MvPolynomial (Fin r) k) C]

/-- Finite-index compatibility specialization of the canonical arbitrary-parameter theorem. -/
theorem tangentVector_eq_sum_parameterDerivations
    (q v : Fin n → L)
    (hq : ∀ i, q i = algebraMap C L
      (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i))))
    (hv : v ∈ Stafford38.Geometry.AffineConormalSpan.zariskiTangentSpace q
      (I.map (MvPolynomial.map (algebraMap k L))))
    : ∃ coeff : Fin r → L, ∀ i,
      v i = ∑ j, coeff j *
        Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Fin r) (B := C) (L := L) j
          (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
            (Ideal.Quotient.mk I (MvPolynomial.X i)) ) :=
  FiniteParameters.tangentVector_eq_sum_parameterDerivations (σ := Fin r) q v hq hv

/-- Finite-index compatibility specialization of the canonical arbitrary-parameter theorem. -/
theorem zariskiTangentSpace_eq_span_parameterDerivations
    [Algebra (MvPolynomial (Fin n) k) C]
    [IsScalarTower k (MvPolynomial (Fin n) k) C]
    [IsScalarTower (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I) C]
    [IsScalarTower (MvPolynomial (Fin n) k) C L]
    (q : Fin n → L)
    (hq : ∀ i, q i = algebraMap C L
      (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
        (Ideal.Quotient.mk I (MvPolynomial.X i)))) :
    Stafford38.Geometry.AffineConormalSpan.zariskiTangentSpace q
      (I.map (MvPolynomial.map (algebraMap k L))) =
      Submodule.span L (Set.range fun j : Fin r => fun i : Fin n =>
        Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation
          (k := k) (σ := Fin r) (B := C) (L := L) j
          (algebraMap (MvPolynomial (Fin n) k ⧸ I) C
            (Ideal.Quotient.mk I (MvPolynomial.X i)))) :=
  FiniteParameters.zariskiTangentSpace_eq_span_parameterDerivations (σ := Fin r) q hq

end

end Stafford38.Geometry.EtaleTangentChartSpan
