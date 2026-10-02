module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.Basic

public section
set_option autoImplicit false

open scoped TensorProduct
open IntermediateField
universe u

namespace Stafford38.Geometry
noncomputable section

/-- A finite transcendence basis gives a basis of the Kähler differentials of the whole field.

The construction starts with the standard basis over a multivariable polynomial ring, localizes
to its fraction field, transports across the transcendence-basis rational-function equivalence,
and then base-changes across the algebraic separable extension. -/
def kaehlerDifferentialBasisOfTranscendenceBasis
    (k L : Type u) [Field k] [CharZero k] [Field L] [Algebra k L]
    (ι : Type u) [Fintype ι] (x : ι → L) (hx : IsTranscendenceBasis k x) :
    Module.Basis ι L (KaehlerDifferential k L) := by
  let S := MvPolynomial ι k
  let A := FractionRing S
  let E := IntermediateField.adjoin k (Set.range x)
  let e : A ≃ₐ[k] E := hx.1.aevalEquivField
  letI : Algebra S A := inferInstance
  letI : IsFractionRing S A := inferInstance
  haveI : Algebra.FormallyEtale S A := Algebra.FormallyEtale.of_isLocalization
    (nonZeroDivisors S)
  let loc : A ⊗[S] KaehlerDifferential k S ≃ₗ[A] KaehlerDifferential k A :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S A
  let bA : Module.Basis ι A (KaehlerDifferential k A) :=
    (KaehlerDifferential.mvPolynomialBasis k ι).baseChange A |>.map loc
  letI : Algebra A E := e.toRingHom.toAlgebra
  haveI : IsScalarTower k A E := .of_algebraMap_eq fun z => (e.commutes z).symm
  letI : Algebra E A := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower k E A := .of_algebraMap_eq fun z => (e.symm.commutes z).symm
  let f : KaehlerDifferential k A →ₛₗ[e.toRingHom] KaehlerDifferential k E := {
    toFun := KaehlerDifferential.map k k A E
    map_add' := by intro a b; exact (KaehlerDifferential.map k k A E).map_add a b
    map_smul' := by
      intro a z
      change KaehlerDifferential.map k k A E (a • z) = e a • _
      rw [map_smul]
      rfl }
  let g : KaehlerDifferential k E →ₛₗ[e.symm.toRingHom] KaehlerDifferential k A := {
    toFun := KaehlerDifferential.map k k E A
    map_add' := by intro a b; exact (KaehlerDifferential.map k k E A).map_add a b
    map_smul' := by
      intro a z
      change KaehlerDifferential.map k k E A (a • z) = e.symm a • _
      rw [map_smul]
      rfl }
  let gf : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A := {
    toFun := fun z => g (f z)
    map_add' := by intro a b; simp only [f.map_add, g.map_add]
    map_smul' := by
      intro a z
      calc
        g (f (a • z)) = g (e.toRingHom a • f z) := by rw [f.map_smulₛₗ]
        _ = e.symm.toRingHom (e.toRingHom a) • g (f z) := by rw [g.map_smulₛₗ]
        _ = a • g (f z) := by
          have h : e.symm.toRingEquiv.toRingHom (e.toRingEquiv.toRingHom a) = a :=
            e.toRingEquiv.symm_apply_apply a
          rw [h] }
  let fg : KaehlerDifferential k E →ₗ[E] KaehlerDifferential k E := {
    toFun := fun z => f (g z)
    map_add' := by intro a b; simp only [g.map_add, f.map_add]
    map_smul' := by
      intro a z
      calc
        f (g (a • z)) = f (e.symm.toRingHom a • g z) := by rw [g.map_smulₛₗ]
        _ = e.toRingHom (e.symm.toRingHom a) • f (g z) := by rw [f.map_smulₛₗ]
        _ = a • f (g z) := by
          have h : e.toRingEquiv.toRingHom (e.symm.toRingEquiv.toRingHom a) = a :=
            e.toRingEquiv.apply_symm_apply a
          rw [h] }
  have hgf : gf = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    change KaehlerDifferential.map k k E A
      (KaehlerDifferential.map k k A E (KaehlerDifferential.D k A z)) = _
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D]
    congr 1
    exact e.symm_apply_apply z
  have hfg : fg = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    change KaehlerDifferential.map k k A E
      (KaehlerDifferential.map k k E A (KaehlerDifferential.D k E z)) = _
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D]
    congr 1
    exact e.apply_symm_apply z
  have hbij : Function.Bijective f := by
    constructor
    · intro a b h
      have h' := congrArg g h
      have ha : g (f a) = a := by
        have hh := congrArg (fun h : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A => h a) hgf
        simpa [gf] using hh
      have hb : g (f b) = b := by
        have hh := congrArg (fun h : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A => h b) hgf
        simpa [gf] using hh
      simpa only [ha, hb] using h'
    · intro b
      refine ⟨g b, ?_⟩
      have hb : f (g b) = b := by
        have hh := congrArg (fun h : KaehlerDifferential k E →ₗ[E] KaehlerDifferential k E => h b) hfg
        simpa [fg] using hh
      exact hb
  let fA : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k E := {
    toFun := f
    map_add' := f.map_add
    map_smul' := by intro a z; exact f.map_smulₛₗ a z }
  let fAEquiv : KaehlerDifferential k A ≃ₗ[A] KaehlerDifferential k E :=
    LinearEquiv.ofBijective fA hbij
  let bEA : Module.Basis ι A (KaehlerDifferential k E) := bA.map fAEquiv
  let bE : Module.Basis ι E (KaehlerDifferential k E) :=
    bEA.mapCoeffs e.toRingEquiv (by intro a z; rfl)
  haveI : Algebra.IsAlgebraic E L := hx.isAlgebraic_field
  haveI : Algebra.IsIntegral E L := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  haveI : Algebra.IsSeparable E L := inferInstance
  haveI : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_isSeparable E L
  let et : L ⊗[E] KaehlerDifferential k E ≃ₗ[L] KaehlerDifferential k L :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k E L
  exact (bE.baseChange L).map et

/-- The dimension is the cardinality of a finite transcendence basis. -/
theorem kaehlerFinrankOfTranscendenceBasis
    (k L : Type u) [Field k] [CharZero k] [Field L] [Algebra k L]
    (ι : Type u) [Fintype ι] (x : ι → L) (hx : IsTranscendenceBasis k x) :
    Module.finrank L (KaehlerDifferential k L) = Fintype.card ι :=
  Module.finrank_eq_card_basis (kaehlerDifferentialBasisOfTranscendenceBasis k L ι x hx)

/-- The Kähler differential module of such a field extension is finite-dimensional. -/
theorem kaehlerFiniteOfTranscendenceBasis
    (k L : Type u) [Field k] [CharZero k] [Field L] [Algebra k L]
    (ι : Type u) [Fintype ι] (x : ι → L) (hx : IsTranscendenceBasis k x) :
    Module.Finite L (KaehlerDifferential k L) :=
  Module.Finite.of_basis (kaehlerDifferentialBasisOfTranscendenceBasis k L ι x hx)

end
end Stafford38.Geometry
