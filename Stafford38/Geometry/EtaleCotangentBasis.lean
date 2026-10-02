import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Basis.Basic

set_option autoImplicit false

open scoped TensorProduct
open Module

namespace Stafford38.Geometry.EtaleCotangentBasis

universe u v w

variable {k : Type u} [CommRing k]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]
variable {B : Type w} [CommRing B]
variable [Algebra (MvPolynomial σ k) B]
variable [Algebra k B] [IsScalarTower k (MvPolynomial σ k) B]
variable [Algebra.FormallyEtale (MvPolynomial σ k) B]

/-- Polynomial coordinate differentials remain a basis after a formally étale extension. -/
noncomputable def basisOfFormallyEtale :
    Basis σ B Ω[B⁄k] := by
  exact (Algebra.TensorProduct.basis B
    (KaehlerDifferential.mvPolynomialBasis k σ)).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k
        (MvPolynomial σ k) B)

/-- The transported basis is represented by the actual images of the polynomial coordinates. -/
theorem basisOfFormallyEtale_apply (i : σ) :
    basisOfFormallyEtale (k := k) (σ := σ) i =
      KaehlerDifferential.D k B
        (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i)) := by
  let E := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k
    (MvPolynomial σ k) B
  have hb : (Algebra.TensorProduct.basis B
      (KaehlerDifferential.mvPolynomialBasis k σ)) i =
      1 ⊗ₜ[MvPolynomial σ k]
        KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i) := by
    simp [Algebra.TensorProduct.basis_apply,
      KaehlerDifferential.mvPolynomialBasis_apply]
  change E ((Algebra.TensorProduct.basis B
      (KaehlerDifferential.mvPolynomialBasis k σ)) i) = _
  rw [← E.apply_symm_apply (KaehlerDifferential.D k B
    (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i)))]
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  exact congrArg E hb

/-- The transported coordinate basis remains a basis after any field-valued scalar extension. -/
noncomputable def basisAfterPoint
    {L : Type*} [Field L] [Algebra B L] :
    Basis σ L (L ⊗[B] Ω[B⁄k]) :=
  Algebra.TensorProduct.basis L (basisOfFormallyEtale (k := k) (σ := σ))


/-- Its scalar-extended basis vectors are the scalar extensions of the actual coordinate differentials. -/
theorem basisAfterPoint_apply
    {L : Type*} [Field L] [Algebra B L] (i : σ) :
    basisAfterPoint (k := k) (σ := σ) (B := B) (L := L) i =
      1 ⊗ₜ[B] KaehlerDifferential.D k B
        (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i)) := by
  change (Algebra.TensorProduct.basis L
      (basisOfFormallyEtale (k := k) (σ := σ))) i = _
  rw [Algebra.TensorProduct.basis_apply, basisOfFormallyEtale_apply]

/-- Dual basis functionals define actual derivations on the étale algebra. -/
noncomputable def coordinateDerivation
    {L : Type*} [CommRing L] [Algebra B L] [Algebra k L]
    [IsScalarTower k B L] (i : σ) : Derivation k B L :=
  KaehlerDifferential.linearMapEquivDerivation k B
    ((basisOfFormallyEtale (k := k) (σ := σ)).constr B
      (fun j => if j = i then (1 : L) else 0))

/-- The derivation specified by its values on the étale polynomial parameters. -/
noncomputable def derivationFromValues
    {L : Type*} [CommRing L] [Algebra B L] [Algebra k L]
    [IsScalarTower k B L] (v : σ → L) : Derivation k B L :=
  KaehlerDifferential.linearMapEquivDerivation k B
    ((basisOfFormallyEtale (k := k) (σ := σ)).constr B v)

theorem coordinateDerivation_apply_parameter
    {L : Type*} [CommRing L] [Algebra B L] [Algebra k L]
    [IsScalarTower k B L] (i j : σ) :
    coordinateDerivation (k := k) (σ := σ) i
      (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j)) =
        if j = i then (1 : L) else 0 := by
  rw [coordinateDerivation,
    KaehlerDifferential.linearMapEquivDerivation_apply_apply,
    ← basisOfFormallyEtale_apply, Basis.constr_basis]

/-- The coordinate values of `derivationFromValues` are exactly the supplied values. -/
theorem derivationFromValues_apply_parameter
    {L : Type*} [CommRing L] [Algebra B L] [Algebra k L]
    [IsScalarTower k B L] (v : σ → L) (i : σ) :
    derivationFromValues (k := k) (σ := σ) (B := B) v
      (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i)) = v i := by
  rw [derivationFromValues,
    KaehlerDifferential.linearMapEquivDerivation_apply_apply,
    ← basisOfFormallyEtale_apply, Basis.constr_basis]

/-- Every derivation is uniquely determined by, and reconstructed from, its
values on the polynomial parameters.  Thus the displayed derivations are an
actual basis of the tangent directions, not merely candidate vectors. -/
theorem derivation_eq_from_parameter_values
    {L : Type*} [CommRing L] [Algebra B L] [Algebra k L]
    [IsScalarTower k B L] (D : Derivation k B L) :
    derivationFromValues (k := k) (σ := σ) (B := B)
      (fun i => D (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i))) = D := by
  let E : (Ω[B⁄k] →ₗ[B] L) ≃ₗ[B] Derivation k B L :=
    KaehlerDifferential.linearMapEquivDerivation k B
  let b : Basis σ B Ω[B⁄k] := basisOfFormallyEtale (k := k) (σ := σ)
  let v := fun i => D (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i))
  let D' := derivationFromValues (k := k) (σ := σ) (B := B) v
  calc
    D' = E (E.symm D') := (E.apply_symm_apply _).symm
    _ = E (E.symm D) := by
      congr 1
      apply b.ext
      intro i
      change (E.symm D') (basisOfFormallyEtale (k := k) (σ := σ) i) =
        (E.symm D) (basisOfFormallyEtale (k := k) (σ := σ) i)
      have hbi := basisOfFormallyEtale_apply (k := k) (σ := σ) (B := B) i
      rw [hbi]
      simp only [E, KaehlerDifferential.linearMapEquivDerivation_symm_apply,
        Derivation.liftKaehlerDifferential_comp_D]
      rw [derivationFromValues_apply_parameter]
    _ = D := E.apply_symm_apply D

/-- Applying a scalar-extension map to a coordinate derivative gives the
coordinate derivative with values in the target algebra. -/
theorem coordinateDerivation_algebraMap
    {L : Type*} [CommRing L] [Algebra B L] [Algebra k L]
    [IsScalarTower k B L] [IsScalarTower B L L]
    (i : σ) (b : B) :
    algebraMap B L (coordinateDerivation (k := k) (σ := σ) (B := B) (L := B) i b) =
      coordinateDerivation (k := k) (σ := σ) (B := B) (L := L) i b := by
  let D : Derivation k B L := (Algebra.linearMap B L).compDer
    (coordinateDerivation (k := k) (σ := σ) (B := B) (L := B) i)
  have hD : D = coordinateDerivation (k := k) (σ := σ) (B := B) (L := L) i := by
    rw [← derivation_eq_from_parameter_values (k := k) (σ := σ) (B := B) D,
      ← derivation_eq_from_parameter_values (k := k) (σ := σ) (B := B)
        (coordinateDerivation (k := k) (σ := σ) (B := B) (L := L) i)]
    congr 1
    funext j
    change algebraMap B L
      (coordinateDerivation (k := k) (σ := σ) (B := B) (L := B) i
        (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j))) =
      coordinateDerivation (k := k) (σ := σ) (B := B) (L := L) i
        (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j))
    rw [coordinateDerivation_apply_parameter, coordinateDerivation_apply_parameter]
    split_ifs <;> simp
  exact congrArg (fun E : Derivation k B L => E b) hD

/-- If two formally-etale charts carry the same polynomial parameters to one
another, the coordinate derivation on the larger chart restricts to the
coordinate derivation on the smaller chart.  The proof uses only the
parameter-value uniqueness above; no separate uniqueness argument is needed. -/
theorem coordinateDerivation_compAlgebraMap
    {C : Type*} [CommRing C]
    [Algebra (MvPolynomial σ k) C] [Algebra k C]
    [IsScalarTower k (MvPolynomial σ k) C]
    [Algebra.FormallyEtale (MvPolynomial σ k) C]
    [Algebra B C] [IsScalarTower k B C] [IsScalarTower B C C]
    (hparam : ∀ j : σ,
      algebraMap B C (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j)) =
        algebraMap (MvPolynomial σ k) C (MvPolynomial.X j))
    (i : σ) :
    (Algebra.linearMap B C).compDer
        (coordinateDerivation (k := k) (σ := σ) (B := B) (L := B) i) =
      (coordinateDerivation (k := k) (σ := σ) (B := C) (L := C) i).compAlgebraMap B := by
  let Dleft : Derivation k B C :=
    (Algebra.linearMap B C).compDer
      (coordinateDerivation (k := k) (σ := σ) (B := B) (L := B) i)
  let Dright : Derivation k B C :=
    (coordinateDerivation (k := k) (σ := σ) (B := C) (L := C) i).compAlgebraMap B
  have hleft (j : σ) :
      Dleft (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j)) =
        if j = i then (1 : C) else 0 := by
    change algebraMap B C
      (coordinateDerivation (k := k) (σ := σ) (B := B) (L := B) i
        (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j))) = _
    rw [coordinateDerivation_apply_parameter]
    simp
  have hright (j : σ) :
      Dright (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j)) =
        if j = i then (1 : C) else 0 := by
    change coordinateDerivation (k := k) (σ := σ) (B := C) (L := C) i
      (algebraMap B C (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j))) = _
    rw [hparam j]
    exact coordinateDerivation_apply_parameter (k := k) (σ := σ) i j
  change Dleft = Dright
  calc
    Dleft = derivationFromValues (k := k) (σ := σ) (B := B) (L := C)
        (fun j => Dleft (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j))) :=
      (derivation_eq_from_parameter_values Dleft).symm
    _ = derivationFromValues (k := k) (σ := σ) (B := B) (L := C)
        (fun j => Dright (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j))) := by
      congr 1
      funext j
      rw [hleft j, hright j]
    _ = Dright := derivation_eq_from_parameter_values Dright

/-- The coordinate derivations form a basis: every derivation is their finite
linear combination with coefficients given by its parameter derivatives. -/
theorem derivation_eq_sum_coordinateDerivations
    {L : Type*} [CommRing L] [Algebra B L] [Algebra k L]
    [IsScalarTower k B L] (D : Derivation k B L) :
    D = ∑ i, D (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i)) •
      coordinateDerivation (k := k) (σ := σ) (B := B) i := by
  let E : Derivation k B L := ∑ i, D (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i)) •
    coordinateDerivation (k := k) (σ := σ) (B := B) i
  have hcoord : ∀ j, E (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j)) =
      D (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j)) := by
    intro j
    change (Derivation.coeFnAddMonoidHom
      (∑ i, D (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i)) •
        coordinateDerivation (k := k) (σ := σ) (B := B) i))
        (algebraMap (MvPolynomial σ k) B (MvPolynomial.X j)) = _
    rw [map_sum]
    simp [Derivation.smul_apply, coordinateDerivation_apply_parameter]
  calc
    D = derivationFromValues (k := k) (σ := σ) (B := B)
        (fun i => D (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i))) :=
          (derivation_eq_from_parameter_values D).symm
    _ = derivationFromValues (k := k) (σ := σ) (B := B)
        (fun i => E (algebraMap (MvPolynomial σ k) B (MvPolynomial.X i))) := by
          congr 1
          funext i
          exact (hcoord i).symm
    _ = E := derivation_eq_from_parameter_values E


end Stafford38.Geometry.EtaleCotangentBasis
