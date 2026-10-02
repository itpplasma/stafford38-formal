import Stafford38.Geometry.SelectedResidueCoefficientLocalization
import Stafford38.Geometry.SameWitnessRelativeTranscendenceDegree
import Stafford38.Geometry.SameWitnessTranscendenceDegreeBound
import Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis
import Stafford38.Geometry.ActualChartValuationImage

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ActualChartRelativeDegree

open IsLocalRing
open Stafford38.Geometry.MvPolynomialFractionFieldTranscendenceBasis
open Stafford38.Geometry.SameWitnessRelativeTranscendenceDegree

universe u

/-- A selected finite residue basis, lifted into a chart algebra inside a
valuation ring, produces relative transcendence degree one whenever the same
valuation has the total-degree bound and a nonzero maximal parameter. -/
theorem component_field_trdeg_one_of_selected_residue_basis
    {k F : Type u} [Field k] [CharZero k] [Field F] [Algebra k F]
    (Q : Subalgebra k F) (V : ValuationSubring F)
    [IsLocalRing V.toSubring] [Algebra k V.toSubring]
    [Algebra k (ResidueField V.toSubring)]
    [IsScalarTower k V.toSubring (ResidueField V.toSubring)]
    (hground : ∀ c : k,
      (algebraMap k V.toSubring c : F) = algebraMap k F c)
    (hQV : Q.toSubring ≤ V.toSubring)
    {t : Set (ResidueField V.toSubring)}
    (htFinite : t.Finite)
    (htBasis : IsTranscendenceBasis k ((↑) : t → ResidueField V.toSubring))
    (x : t → Q)
    (hx : ∀ z : t, residue V.toSubring
      ⟨(x z : F), hQV (x z).property⟩ = (z : ResidueField V.toSubring))
    (hbound : Algebra.trdeg k F ≤ Algebra.trdeg k (ResidueField V.toSubring) + 1)
    (parameter : V.toSubring) (hparameter0 : parameter ≠ 0)
    (hparameterMax : parameter ∈ maximalIdeal V.toSubring) :
    let A : Subalgebra k Q := Algebra.adjoin k (Set.range x)
    ∃ (eA : MvPolynomial t k ≃ₐ[k] A)
      (fA : A →ₐ[k] V.toSubring)
      (iA : A →ₐ[k] FractionRing (MvPolynomial t k))
      (g : FractionRing (MvPolynomial t k) →ₐ[k] ResidueField V.toSubring)
      (fEV : FractionRing (MvPolynomial t k) →ₐ[k] V.toSubring)
      (fEF : FractionRing (MvPolynomial t k) →ₐ[k] F),
      Function.Injective g ∧
      (∀ z : t, ((eA (MvPolynomial.X z) : A) : Q) = x z) ∧
      (∀ z : t, fA (eA (MvPolynomial.X z)) =
        (⟨(x z : F), hQV (x z).property⟩ : V.toSubring)) ∧
      (∀ z : t, g (algebraMap (MvPolynomial t k)
        (FractionRing (MvPolynomial t k)) (MvPolynomial.X z)) = (z : ResidueField V.toSubring)) ∧
      (IsLocalRing.residue V.toSubring).comp fEV.toRingHom = g.toRingHom ∧
      fEV.toRingHom.comp iA.toRingHom = fA.toRingHom ∧
      (∀ p : MvPolynomial t k,
        iA (eA p) = algebraMap (MvPolynomial t k) (FractionRing (MvPolynomial t k)) p) ∧
      (∀ p : MvPolynomial t k,
        fEF (algebraMap (MvPolynomial t k) (FractionRing (MvPolynomial t k)) p) =
          (((eA p : A) : Q) : F)) ∧
      letI : Algebra (FractionRing (MvPolynomial t k)) F := fEF.toRingHom.toAlgebra
      Algebra.trdeg (FractionRing (MvPolynomial t k)) F = 1 := by
  classical
  let A : Subalgebra k Q := Algebra.adjoin k (Set.range x)
  let κ := ResidueField V.toSubring
  letI : Algebra V.toSubring F := V.toSubring.subtype.toAlgebra
  letI : IsScalarTower k V.toSubring F := IsScalarTower.of_algebraMap_eq fun c =>
    (hground c).symm
  obtain ⟨eA, fA, iA, g, fEV, hg, hrange, hgenA, hfA, hgenG,
      hiA, hresE, hfE⟩ :=
    Stafford38.Geometry.SelectedResidueCoefficientLocalization.exists_selected_fraction_field_maps
      Q V hground hQV htBasis x hx
  let E := FractionRing (MvPolynomial t k)
  letI : Field E := FractionRing.field (MvPolynomial t k)
  letI : Algebra E κ := g.toRingHom.toAlgebra
  have hvars : IsTranscendenceBasis k (fun z : t =>
      algebraMap E κ (algebraMap (MvPolynomial t k) E (MvPolynomial.X z))) := by
    change IsTranscendenceBasis k
      (fun z : t => g (algebraMap (MvPolynomial t k) E (MvPolynomial.X z)))
    have hfun : (fun z : t =>
        g (algebraMap (MvPolynomial t k) E (MvPolynomial.X z))) =
        ((↑) : t → κ) := by
      funext z
      exact hgenG z
    rw [hfun]
    exact htBasis
  have hκalg : Algebra.IsAlgebraic E κ :=
    isAlgebraic_fractionRing_of_variable_images_isTranscendenceBasis hvars
  letI : Algebra E V.toSubring := fEV.toRingHom.toAlgebra
  let fEF : E →ₐ[k] F := {
    toRingHom := (algebraMap V.toSubring F).comp fEV.toRingHom
    commutes' := by
      intro c
      change algebraMap V.toSubring F (fEV (algebraMap k E c)) = algebraMap k F c
      rw [fEV.commutes]
      exact hground c
  }
  letI : Algebra E F := fEF.toRingHom.toAlgebra
  letI : IsScalarTower E V.toSubring F :=
    IsScalarTower.of_algebraMap_eq fun z => rfl
  letI : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq fun c =>
    (fEF.commutes c).symm
  letI : IsScalarTower k E κ := IsScalarTower.of_algebraMap_eq fun c =>
    (g.commutes c).symm
  letI : Fintype t := htFinite.fintype
  let basis : ULift.{u} t → E := fun i =>
    algebraMap (MvPolynomial t k) E (MvPolynomial.X i.down)
  have hbasis : IsTranscendenceBasis k basis :=
    standardVariables_isTranscendenceBasis_of_fintype
  have hVF : Function.Injective (algebraMap V.toSubring F) := by
    intro a b hab
    change (a : F) = (b : F) at hab
    exact Subtype.val_injective hab
  let qV : Q →ₐ[k] V.toSubring :=
    Stafford38.Geometry.SelectedResidueCoefficientLocalization.chartAlgebraToValuation
      Q V hground hQV
  let evQ : MvPolynomial t k →ₐ[k] Q := MvPolynomial.aeval x
  have heAeval : ∀ p : MvPolynomial t k, (eA p : A) = evQ p := by
    have hmaps : (Subalgebra.val A).comp eA.toAlgHom = evQ := by
      apply MvPolynomial.algHom_ext
      intro z
      change ((eA (MvPolynomial.X z) : A) : Q) =
        MvPolynomial.aeval x (MvPolynomial.X z)
      rw [MvPolynomial.aeval_X]
      exact hgenA z
    intro p
    exact AlgHom.congr_fun hmaps p
  have hfAeval : ∀ p : MvPolynomial t k,
      fA (eA p) = qV (evQ p) := by
    have hmaps : fA.comp eA.toAlgHom = qV.comp evQ := by
      apply MvPolynomial.algHom_ext
      intro z
      change fA (eA (MvPolynomial.X z)) =
        qV (MvPolynomial.aeval x (MvPolynomial.X z))
      rw [MvPolynomial.aeval_X]
      rw [hfA z]
      apply Subtype.ext
      rfl
    intro p
    exact AlgHom.congr_fun hmaps p
  have hgen : ∀ p : MvPolynomial t k,
      fEF (algebraMap (MvPolynomial t k) E p) = (((eA p : A) : Q) : F) := by
    intro p
    have hcompose : fEV (iA (eA p)) = fA (eA p) := by
      have h := congrArg (fun φ : A →+* V.toSubring => φ (eA p)) hfE
      change fEV.toRingHom (iA.toRingHom (eA p)) = fA.toRingHom (eA p)
      exact h
    calc
      fEF (algebraMap (MvPolynomial t k) E p) =
          algebraMap V.toSubring F (fEV (algebraMap (MvPolynomial t k) E p)) := rfl
      _ = algebraMap V.toSubring F (fEV (iA (eA p))) := by rw [hiA p]
      _ = algebraMap V.toSubring F (fA (eA p)) := by rw [hcompose]
      _ = (((eA p : A) : Q) : F) := by
        rw [hfAeval p, heAeval p]
        rfl
  refine ⟨eA, fA, iA, g, fEV, fEF, hg, hgenA, hfA, hgenG,
    hresE, hfE, hiA, hgen, ?_⟩
  exact eq_one_of_same_total_bound_of_finite_basis_and_parameter
      basis hbasis hVF parameter hparameter0 hparameterMax hκalg hbound

open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ChartGenericPointFractionRing
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.SameWitnessTranscendenceDegreeBound

/-- The retained projective chart supplies the hypotheses of the generic
relative-degree bridge for every selected residue basis from that witness.
The coefficient-field map is returned so its algebra structure is explicit. -/
theorem same_witness_component_trdeg_one_from_basis
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let U := W.place.valuation
    let V := U.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k V := C.groundCoeff.toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
      ∀ (t : Set κ), t.Finite → IsTranscendenceBasis k ((↑) : t → κ) →
      (index : t → Fin m) →
      (∀ z : t, residue V (C.q ((chartAffineCoordinateEquiv C.chart) (index z)).1) =
        (z : κ)) →
      let Q : Subalgebra k F := Algebra.adjoin k (Set.range
        (chartGenericPoint P C.chart (chartAffineCoordinateEquiv C.chart)))
      let hQV : Q.toSubring ≤ V := by
        intro z hz
        exact Stafford38.Geometry.ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring
          hm P w z hz
      let x : t → Q := fun z =>
        ⟨chartGenericPoint P C.chart (chartAffineCoordinateEquiv C.chart) (index z),
          Algebra.subset_adjoin (R := k) (A := F)
            (Set.mem_range_self (index z))⟩
      let A : Subalgebra k Q := Algebra.adjoin k (Set.range x)
      ∃ (eA : MvPolynomial t k ≃ₐ[k] A)
        (fA : A →ₐ[k] V) (iA : A →ₐ[k] FractionRing (MvPolynomial t k))
        (g : FractionRing (MvPolynomial t k) →ₐ[k] κ)
        (fEV : FractionRing (MvPolynomial t k) →ₐ[k] V)
        (fEF : FractionRing (MvPolynomial t k) →ₐ[k] F),
        Function.Injective g ∧
        (∀ z : t, ((eA (MvPolynomial.X z) : A) : Q) = x z) ∧
        (∀ z : t, fA (eA (MvPolynomial.X z)) =
          (⟨(x z : F), hQV (x z).property⟩ : V)) ∧
        (∀ z : t, g (algebraMap (MvPolynomial t k)
          (FractionRing (MvPolynomial t k)) (MvPolynomial.X z)) = (z : κ)) ∧
        (IsLocalRing.residue V).comp fEV.toRingHom = g.toRingHom ∧
        fEV.toRingHom.comp iA.toRingHom = fA.toRingHom ∧
        (∀ p : MvPolynomial t k,
          iA (eA p) = algebraMap (MvPolynomial t k)
            (FractionRing (MvPolynomial t k)) p) ∧
        (∀ p : MvPolynomial t k,
          fEF (algebraMap (MvPolynomial t k) (FractionRing (MvPolynomial t k)) p) =
            (((eA p : A) : Q) : F)) ∧
        letI : Algebra (FractionRing (MvPolynomial t k)) F := fEF.toRingHom.toAlgebra
        Algebra.trdeg (FractionRing (MvPolynomial t k)) F = 1 := by
  classical
  dsimp only
  intro t htFinite htBasis index hres
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let U := W.place.valuation
  let V := U.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k V := C.groundCoeff.toAlgebra
  letI : Algebra V F := V.subtype.toAlgebra
  letI : IsScalarTower k V F := C.groundTower
  let κ := ResidueField V
  let retained : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : Algebra k κ := retained
  have hretainedMap : @algebraMap k κ _ _ retained =
      (residue V).comp C.groundCoeff := by
    simpa [C, W, V, κ, C.groundCoeff_eq_retained] using w.retainedGroundMap
  letI : IsScalarTower k V κ := IsScalarTower.of_algebraMap_eq fun c => by
    have h := RingHom.congr_fun hretainedMap c
    change algebraMap k κ c = residue V (C.groundCoeff c)
    exact h
  let e := chartAffineCoordinateEquiv C.chart
  let Q : Subalgebra k F := Algebra.adjoin k (Set.range
    (chartGenericPoint P C.chart e))
  have hQV : Q.toSubring ≤ V := by
    intro z hz
    exact Stafford38.Geometry.ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring
      hm P w z hz
  have hground : ∀ c : k,
      (algebraMap k V c : F) = algebraMap k F c := by
    intro c
    exact DFunLike.congr_fun C.groundCoeff_commutes c
  let x : t → Q := fun z =>
    ⟨chartGenericPoint P C.chart e (index z),
      Algebra.subset_adjoin (R := k) (A := F) (Set.mem_range_self (index z))⟩
  have hx : ∀ z : t, residue V
      ⟨(x z : F), hQV (x z).property⟩ = (z : κ) := by
    intro z
    have hnorm := chartGenericPoint_eq_normalized_lift
      (P := P) (V := V) C.chart e C.q C.scale C.chart_one C.q_commonScale
    have hxV : (⟨(x z : F), hQV (x z).property⟩ : V) = C.q (e (index z)).1 := by
      apply Subtype.ext
      change chartGenericPoint P C.chart e (index z) = (C.q (e (index z)).1 : F)
      exact congrFun hnorm (index z)
    rw [hxV]
    exact hres z
  have hbound : Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1 :=
    component_trdeg_le_residue_trdeg_add_one_of_witness hm P w
  have hparameterMax : C.q 0 ∈ maximalIdeal V := witness_q0_mem_maximal hm P w
  exact component_field_trdeg_one_of_selected_residue_basis
    Q U hground hQV htFinite htBasis x hx hbound (C.q 0) C.q0_ne hparameterMax

#print axioms component_field_trdeg_one_of_selected_residue_basis
#print axioms same_witness_component_trdeg_one_from_basis

end Stafford38.Geometry.ActualChartRelativeDegree
