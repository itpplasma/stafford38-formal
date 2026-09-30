import Stafford38.Characteristic.CanonicalOldTangentialFiniteness
import Stafford38.Characteristic.CanonicalNormalAxisSupport

/-!
# The distinguished coordinate hyperplane is noncharacteristic

For an ideal in the symbol ring, restriction to `x₀ = 0` has coordinate ring
`R / (J + (x₀))`.  As a module this is the cokernel of multiplication by
`x₀` on `R / J`.  We use that cokernel presentation to express finiteness of
the projection to the cotangent space of the hyperplane.
-/

namespace Stafford38.NoncharacteristicHyperplane

open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalOldTangentialFiniteness
open Stafford38.Characteristic.CanonicalNormalAxisSupport
open Stafford38.Characteristic.CanonicalTangentialRingEquivalence
open Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicInitialIdeal
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

variable {k : Type*} [Field k]

/-- The coordinate-ring map from the cotangent space of the hyperplane to the
ambient symbol ring, omitting both the normal coordinate and normal covariable. -/
def tangentialSymbolMap (n : ℕ) :
    oldTangentialCoeffRing (k := k) n →+* SymbolRing k (n + 1) :=
  ((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C).comp
    (oldSymbolTangentialAlgEquiv (k := k) n).toRingHom

/-- The natural tangential-coordinate action on the coordinate ring of a
closed subset of the cotangent bundle restricted to `x₀ = 0`. -/
noncomputable instance restrictedSymbolRing_tangentialModule
    (n : ℕ) (J : Ideal (SymbolRing k (n + 1))) :
    Module (oldTangentialCoeffRing (k := k) n)
      (SymbolRing k (n + 1) ⧸ J) :=
  Module.compHom (SymbolRing k (n + 1) ⧸ J)
    ((Ideal.Quotient.mk J).comp (tangentialSymbolMap (k := k) n))

/-- Multiplication by the normal base coordinate on the restricted
characteristic coordinate ring, viewed as a linear map over the tangential
coordinate ring. -/
def restrictedCoordinateAction (n : ℕ)
    (J : Ideal (SymbolRing k (n + 1))) :
    (SymbolRing k (n + 1) ⧸ J) →ₗ[oldTangentialCoeffRing (k := k) n]
      (SymbolRing k (n + 1) ⧸ J) where
  toFun z := (MvPolynomial.X (.inl (0 : Fin (n + 1))) :
      SymbolRing k (n + 1)) • z
  map_add' := smul_add _
  map_smul' := by
    intro a z
    change (MvPolynomial.X (.inl (0 : Fin (n + 1))) :
        SymbolRing k (n + 1)) •
          (((Ideal.Quotient.mk J) (tangentialSymbolMap (k := k) n a)) • z) =
      ((Ideal.Quotient.mk J) (tangentialSymbolMap (k := k) n a) •
        ((MvPolynomial.X (.inl (0 : Fin (n + 1))) :
          SymbolRing k (n + 1)) • z))
    exact smul_comm _ _ _

/-- `J` is noncharacteristic for the distinguished coordinate hyperplane when
the coordinate ring of its restricted zero locus is finite over the
coordinate ring of `T^*H`.  The quotient-module presentation here is
canonically the ring `R / (J + (x₀))`. -/
def IsNoncharacteristic (n : ℕ)
    (J : Ideal (SymbolRing k (n + 1))) : Prop :=
  Module.Finite (oldTangentialCoeffRing (k := k) n)
    ((SymbolRing k (n + 1) ⧸ J) ⧸
      LinearMap.range (restrictedCoordinateAction (k := k) n J))

/-- The coordinate ring obtained by restricting `V(J)` to `x₀ = 0`. -/
def restrictedCoordinateIdeal (n : ℕ) (J : Ideal (SymbolRing k (n + 1))) :
    Ideal (SymbolRing k (n + 1)) :=
  J ⊔ Ideal.span ({(MvPolynomial.X (.inl (0 : Fin (n + 1))) :
    SymbolRing k (n + 1))} : Set (SymbolRing k (n + 1)))

/-- The tangential-coordinate action on the literal restricted coordinate ring. -/
noncomputable instance restrictedCoordinateQuotient_tangentialModule
    (n : ℕ) (J : Ideal (SymbolRing k (n + 1))) :
    Module (oldTangentialCoeffRing (k := k) n)
      (SymbolRing k (n + 1) ⧸ restrictedCoordinateIdeal (k := k) n J) :=
  Module.compHom _
    ((Ideal.Quotient.mk (restrictedCoordinateIdeal (k := k) n J)).comp
      (tangentialSymbolMap (k := k) n))

/-- The cokernel presentation maps onto the literal coordinate ring of the
restricted zero locus. -/
noncomputable def cokerToRestrictedCoordinateRing (n : ℕ)
    (J : Ideal (SymbolRing k (n + 1))) :
    ((SymbolRing k (n + 1) ⧸ J) ⧸
      LinearMap.range (restrictedCoordinateAction (k := k) n J)) →ₗ[
        oldTangentialCoeffRing (k := k) n]
      (SymbolRing k (n + 1) ⧸ restrictedCoordinateIdeal (k := k) n J) := by
  let R := SymbolRing k (n + 1)
  let T := oldTangentialCoeffRing (k := k) n
  let K := restrictedCoordinateIdeal (k := k) n J
  let ψ : R ⧸ J →+* R ⧸ K :=
    Ideal.Quotient.lift J (Ideal.Quotient.mk K) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (le_sup_left : J ≤ K) ha)
  let g : R ⧸ J →ₗ[T] R ⧸ K :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := by
        intro a z
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) z
        change ψ ((Ideal.Quotient.mk J (tangentialSymbolMap (k := k) n a)) *
            Ideal.Quotient.mk J r) =
          (Ideal.Quotient.mk K (tangentialSymbolMap (k := k) n a)) *
            ψ (Ideal.Quotient.mk J r)
        rw [map_mul]
        simp [ψ] }
  have hkill : (LinearMap.range (restrictedCoordinateAction (k := k) n J)) ≤ g.ker := by
    rintro z ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) w
    change ψ ((MvPolynomial.X (.inl (0 : Fin (n + 1))) : R) •
        Ideal.Quotient.mk J r) = 0
    change ψ (Ideal.Quotient.mk J
      ((MvPolynomial.X (.inl (0 : Fin (n + 1))) : R) * r)) = 0
    change Ideal.Quotient.mk K
      ((MvPolynomial.X (.inl (0 : Fin (n + 1))) : R) * r) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (le_sup_right : Ideal.span ({_} : Set R) ≤ K)
      (Ideal.mul_mem_right r _ (Ideal.subset_span (by simp)))
  exact Submodule.liftQ _ g hkill

/-- The map from the cokernel presentation sends the class of `r` to its class
in the literal restricted coordinate ring. -/
theorem cokerToRestrictedCoordinateRing_mk (n : ℕ)
    (J : Ideal (SymbolRing k (n + 1))) :
    ∀ r : SymbolRing k (n + 1),
      cokerToRestrictedCoordinateRing (k := k) n J
        (Submodule.Quotient.mk (Ideal.Quotient.mk J r)) =
      Ideal.Quotient.mk (restrictedCoordinateIdeal (k := k) n J) r := by
  intro r
  let R := SymbolRing k (n + 1)
  let K := restrictedCoordinateIdeal (k := k) n J
  have hJ : ∀ a ∈ J, (Ideal.Quotient.mk K) a = 0 := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (le_sup_left : J ≤ K) ha
  unfold cokerToRestrictedCoordinateRing
  rw [Submodule.liftQ_apply]
  change (Ideal.Quotient.lift J (Ideal.Quotient.mk K) hJ)
      (Ideal.Quotient.mk J r) = Ideal.Quotient.mk K r
  rw [Ideal.Quotient.lift_mk]

/-- Every point of the literal restricted coordinate ring has a representative
in the cokernel presentation. -/
theorem cokerToRestrictedCoordinateRing_surjective (n : ℕ)
    (J : Ideal (SymbolRing k (n + 1))) :
    Function.Surjective (cokerToRestrictedCoordinateRing (k := k) n J) := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := restrictedCoordinateIdeal (k := k) n J) z
  exact ⟨Submodule.Quotient.mk (Ideal.Quotient.mk J r),
    cokerToRestrictedCoordinateRing_mk (k := k) n J r⟩

/-- The only classes killed by restriction to `x₀ = 0` are the classes
generated by multiplication by `x₀`. -/
theorem cokerToRestrictedCoordinateRing_injective (n : ℕ)
    (J : Ideal (SymbolRing k (n + 1))) :
    Function.Injective (cokerToRestrictedCoordinateRing (k := k) n J) := by
  let R := SymbolRing k (n + 1)
  let T := oldTangentialCoeffRing (k := k) n
  let K := restrictedCoordinateIdeal (k := k) n J
  let x : R := MvPolynomial.X (.inl (0 : Fin (n + 1)))
  let f := restrictedCoordinateAction (k := k) n J
  intro z₁ z₂ heq
  have hzero : cokerToRestrictedCoordinateRing (k := k) n J (z₁ - z₂) = 0 := by
    rw [map_sub, heq, sub_self]
  have hz : z₁ - z₂ = 0 := by
    obtain ⟨q, hq⟩ := Submodule.mkQ_surjective f.range (z₁ - z₂)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) q
    have hmapzero : cokerToRestrictedCoordinateRing (k := k) n J
        (Submodule.Quotient.mk (Ideal.Quotient.mk J r)) = 0 := by
      calc
        _ = cokerToRestrictedCoordinateRing (k := k) n J (z₁ - z₂) :=
          congrArg (cokerToRestrictedCoordinateRing (k := k) n J) hq
        _ = 0 := hzero
    have htarget : Ideal.Quotient.mk K r = 0 := by
      rw [← cokerToRestrictedCoordinateRing_mk (k := k) n J r]
      exact hmapzero
    have hrK : r ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp htarget
    rcases Submodule.mem_sup.mp hrK with ⟨j, hj, s, hs, hjs⟩
    rcases Ideal.mem_span_singleton'.mp hs with ⟨a, has⟩
    have hrange : (Ideal.Quotient.mk J r) ∈ f.range := by
      refine ⟨Ideal.Quotient.mk J a, ?_⟩
      change Ideal.Quotient.mk J (x * a) = Ideal.Quotient.mk J r
      rw [← hjs, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add]
      rw [← has, mul_comm]
    have := (Submodule.Quotient.mk_eq_zero f.range).mpr hrange
    exact hq.symm.trans this
  exact sub_eq_zero.mp hz

/-- The cokernel presentation and the literal restricted coordinate ring are
canonically linearly equivalent over the hyperplane cotangent coordinates. -/
noncomputable def cokerToRestrictedCoordinateRingEquiv (n : ℕ)
    (J : Ideal (SymbolRing k (n + 1))) :
    ((SymbolRing k (n + 1) ⧸ J) ⧸
      LinearMap.range (restrictedCoordinateAction (k := k) n J)) ≃ₗ[
        oldTangentialCoeffRing (k := k) n]
      (SymbolRing k (n + 1) ⧸ restrictedCoordinateIdeal (k := k) n J) :=
  LinearEquiv.ofBijective (cokerToRestrictedCoordinateRing (k := k) n J)
    ⟨cokerToRestrictedCoordinateRing_injective (k := k) n J,
      cokerToRestrictedCoordinateRing_surjective (k := k) n J⟩

/-- The cokernel definition is equivalent to finiteness of the literal
restricted coordinate ring `R/(J+(x₀))`. -/
theorem isNoncharacteristic_iff_finite_restrictedCoordinateQuotient (n : ℕ)
    (J : Ideal (SymbolRing k (n + 1))) :
    IsNoncharacteristic (k := k) n J ↔
      Module.Finite (oldTangentialCoeffRing (k := k) n)
        (SymbolRing k (n + 1) ⧸ restrictedCoordinateIdeal (k := k) n J) := by
  unfold IsNoncharacteristic
  let e := cokerToRestrictedCoordinateRingEquiv (k := k) n J
  constructor
  · intro h
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  · intro h
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- For the canonical characteristic ideal, restriction to `x₀ = 0` is finite
over `T^*H`. -/
theorem canonical_isNoncharacteristic_annihilator
    {n N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    IsNoncharacteristic (k := k) n
      (Module.annihilator (SymbolRing k (n + 1))
        (OrderAssociatedGradedModule k
          (canonicalRightIdeal (presentedCoordinate k n) d N))) := by
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  let E := OrderAssociatedGradedModule k I
  let R := SymbolRing k (n + 1)
  let T := oldTangentialCoeffRing (k := k) n
  let J := Module.annihilator R E
  let Q := R ⧸ J
  let x : R := MvPolynomial.X (.inl (0 : Fin (n + 1)))
  let fE := oldCoordinateMap (k := k) n E
  let fQ := restrictedCoordinateAction (k := k) n J
  let e0 := orderAssociatedGradedLinearEquivCharacteristic k I
  have hAnn : J = orderInitialIdeal k I := by
    dsimp [J]
    exact annihilator_orderAssociatedGradedModule k I
  let eQ : E ≃ₗ[R] Q :=
    e0.trans (Ideal.quotientEquivAlgOfEq R hAnn.symm).toLinearEquiv
  letI : Module T E := oldCoeffModule (k := k) n E
  let eT : E ≃ₗ[T] Q :=
    { toFun := eQ
      invFun := eQ.symm
      left_inv := eQ.left_inv
      right_inv := eQ.right_inv
      map_add' := eQ.map_add
      map_smul' := by
        intro a z
        change eQ ((tangentialSymbolMap (k := k) n a) • z) =
          ((Ideal.Quotient.mk J) (tangentialSymbolMap (k := k) n a)) • eQ z
        exact eQ.map_smul _ _ }
  let hfinite := canonical_finite_old_coordinate_kernel_cokernel
    (k := k) (n := n) (N := N) (d := d) hd
  have hfiniteCoker : Module.Finite T (E ⧸ fE.range) := by
    simpa only [fE] using hfinite.2
  let F : E →ₗ[T] Q ⧸ fQ.range :=
    { toFun := fun z => Submodule.Quotient.mk (eT z)
      map_add' := by intro z w; simp [eT.map_add]
      map_smul' := by
        intro a z
        change Submodule.Quotient.mk (eT (a • z)) =
          a • Submodule.Quotient.mk (eT z)
        rw [eT.map_smul]
        exact (Submodule.mkQ fQ.range).map_smul a (eT z) }
  have hkill : fE.range ≤ F.ker := by
    rintro z ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (eT (fE w)) = 0
    rw [oldCoordinateMap_apply]
    change Submodule.Quotient.mk (eT (x • w)) = 0
    change Submodule.Quotient.mk (eQ (x • w)) = 0
    rw [eQ.map_smul]
    rw [Submodule.Quotient.mk_eq_zero]
    change fQ (eQ w) ∈ fQ.range
    exact ⟨eQ w, rfl⟩
  let Fbar : E ⧸ fE.range →ₗ[T] Q ⧸ fQ.range :=
    Submodule.liftQ fE.range F hkill
  have hsurj : Function.Surjective Fbar := by
    intro z
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective fQ.range z
    obtain ⟨w, hw⟩ := eQ.surjective q
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    change Fbar (Submodule.Quotient.mk w) = Submodule.Quotient.mk q
    dsimp [Fbar]
    change Submodule.Quotient.mk (eT w) = Submodule.Quotient.mk q
    simpa [eT] using
      congrArg (fun q' : Q => (Submodule.Quotient.mk q' : Q ⧸ fQ.range)) hw
  unfold IsNoncharacteristic
  exact Module.Finite.of_surjective Fbar hsurj

/-- The actual coordinate ring of the restricted canonical characteristic
variety is finite over the cotangent-coordinate ring of the hyperplane. -/
theorem canonical_finite_restrictedCoordinateQuotient
    {n N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Module.Finite (oldTangentialCoeffRing (k := k) n)
      (SymbolRing k (n + 1) ⧸ restrictedCoordinateIdeal (k := k) n
        (Module.annihilator (SymbolRing k (n + 1))
          (OrderAssociatedGradedModule k
            (canonicalRightIdeal (presentedCoordinate k n) d N)))) := by
  let J := Module.annihilator (SymbolRing k (n + 1))
    (OrderAssociatedGradedModule k
      (canonicalRightIdeal (presentedCoordinate k n) d N))
  have hfinite : IsNoncharacteristic (k := k) n J := by
    simpa [J] using canonical_isNoncharacteristic_annihilator (k := k) hd
  unfold IsNoncharacteristic at hfinite
  exact Module.Finite.of_surjective
    (cokerToRestrictedCoordinateRing (k := k) n J)
    (cokerToRestrictedCoordinateRing_surjective (k := k) n J)

/-- In the canonical support, vanishing of every tangential covariable forces
the distinguished normal covariable to vanish as well.  The conclusion does
not require the base point to lie on `x₀ = 0`. -/
theorem canonicalSupport_conormal_subset_zeroSection
    {n N : ℕ} (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p : PrimeSpectrum (SymbolRing k (n + 1))}
    (hp : p ∈ orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N))
    (htan : ∀ i : Fin (n + 1), i ≠ 0 →
      MvPolynomial.X (.inr i) ∈ p.asIdeal) :
    MvPolynomial.X (.inr (0 : Fin (n + 1))) ∈ p.asIdeal := by
  exact CanonicalNormalAxisSupport.normalMomentum_mem_of_mem_canonicalSupport
    d hd hp htan

#print axioms canonical_isNoncharacteristic_annihilator
#print axioms cokerToRestrictedCoordinateRing_mk
#print axioms cokerToRestrictedCoordinateRing_surjective
#print axioms cokerToRestrictedCoordinateRing_injective
#print axioms cokerToRestrictedCoordinateRingEquiv
#print axioms isNoncharacteristic_iff_finite_restrictedCoordinateQuotient
#print axioms canonical_finite_restrictedCoordinateQuotient
#print axioms canonicalSupport_conormal_subset_zeroSection

end
end Stafford38.NoncharacteristicHyperplane
