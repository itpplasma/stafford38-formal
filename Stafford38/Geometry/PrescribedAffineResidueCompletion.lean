import Stafford38.Geometry.AffinePointCompletion
import Stafford38.Geometry.EtalePointCompletion

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Stafford38.Geometry.PrescribedAffineResidueCompletion

noncomputable section

variable {k σ B : Type*} [Field k] [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B]

local notation "R" => MvPolynomial σ k

/-- The point of affine coordinate space read from the chosen residue map at `M`. -/
def residueCoordinates (M : Ideal B) (eM : (B ⧸ M) ≃ₐ[k] k) : σ → k :=
  fun i => eM (Ideal.Quotient.mkₐ k M (algebraMap R B (MvPolynomial.X i)))

/-- The original coordinate map followed by the chosen residue identification. -/
def residueEvaluation (M : Ideal B) (eM : (B ⧸ M) ≃ₐ[k] k) : R →ₐ[k] k :=
  eM.toAlgHom.comp
    ((Ideal.Quotient.mkₐ k M).comp (IsScalarTower.toAlgHom k R B))

theorem residueEvaluation_eq_aeval (M : Ideal B) (eM : (B ⧸ M) ≃ₐ[k] k) :
    residueEvaluation (σ := σ) M eM =
      MvPolynomial.aeval (residueCoordinates (σ := σ) M eM) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [residueEvaluation, residueCoordinates]

theorem pointIdeal_eq_residueEvaluation_ker (M : Ideal B)
    (eM : (B ⧸ M) ≃ₐ[k] k) :
    Stafford38.Geometry.AffinePointCompletion.pointIdeal (residueCoordinates (σ := σ) M eM) =
      RingHom.ker (residueEvaluation (σ := σ) M eM) := by
  change RingHom.ker ((MvPolynomial.aeval (residueCoordinates (σ := σ) M eM)).toRingHom) =
    RingHom.ker (residueEvaluation (σ := σ) M eM : R →+* k)
  exact congrArg RingHom.ker
    (congrArg AlgHom.toRingHom (residueEvaluation_eq_aeval (σ := σ) M eM)).symm

theorem residueEvaluation_surjective (M : Ideal B) (eM : (B ⧸ M) ≃ₐ[k] k) :
    Function.Surjective (residueEvaluation (σ := σ) M eM) := by
  intro c
  refine ⟨MvPolynomial.C c, ?_⟩
  simp [residueEvaluation]

/-- The residue point gives the actual maximal ideal of the polynomial coordinate ring. -/
theorem residuePoint_isMaximal (M : Ideal B) (eM : (B ⧸ M) ≃ₐ[k] k) :
    (Stafford38.Geometry.AffinePointCompletion.pointIdeal (residueCoordinates (σ := σ) M eM)).IsMaximal := by
  rw [pointIdeal_eq_residueEvaluation_ker (σ := σ)]
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  obtain ⟨a, ha⟩ := residueEvaluation_surjective (σ := σ) M eM c
  exact ⟨a, ha⟩

/-- The polynomial coordinate ring modulo the residue point is the ground field. -/
noncomputable def residuePointQuotientEquiv (M : Ideal B)
    (eM : (B ⧸ M) ≃ₐ[k] k) :
    (R ⧸ Stafford38.Geometry.AffinePointCompletion.pointIdeal (residueCoordinates (σ := σ) M eM)) ≃ₐ[k] k := by
  let hq := pointIdeal_eq_residueEvaluation_ker (σ := σ) M eM
  exact (Ideal.quotientEquivAlgOfEq k hq).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (residueEvaluation_surjective (σ := σ) M eM))

theorem residuePointQuotientEquiv_apply (M : Ideal B)
    (eM : (B ⧸ M) ≃ₐ[k] k) (a : R) :
    residuePointQuotientEquiv (σ := σ) M eM
      (Ideal.Quotient.mk
        (Stafford38.Geometry.AffinePointCompletion.pointIdeal
          (residueCoordinates (σ := σ) M eM)) a) =
      residueEvaluation (σ := σ) M eM a := by
  let hq := pointIdeal_eq_residueEvaluation_ker (σ := σ) M eM
  change ((Ideal.quotientEquivAlgOfEq k hq).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (residueEvaluation_surjective (σ := σ) M eM)))
      (Ideal.Quotient.mk (Stafford38.Geometry.AffinePointCompletion.pointIdeal
        (residueCoordinates (σ := σ) M eM)) a) = _
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk
    (residueEvaluation_surjective (σ := σ) M eM) a

/-- At an actual ground-rational point of the original `R`-algebra, the residue
equivalence over `R` is induced by the same evaluation map. The quotient-kernel
equivalence and the supplied `B/M ≃ k` are the only ingredients. -/
noncomputable def residueEquivOverCoordinates
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra R k] [IsScalarTower R k k]
    [IsScalarTower R k (B ⧸ M)]
    [IsScalarTower R k
      (R ⧸ Stafford38.Geometry.AffinePointCompletion.pointIdeal
        (residueCoordinates (σ := σ) M eM))] :
    (B ⧸ M) ≃ₐ[R]
      (R ⧸ Stafford38.Geometry.AffinePointCompletion.pointIdeal (residueCoordinates M eM)) := by
  let eQ := residuePointQuotientEquiv (σ := σ) M eM
  let eM' : (B ⧸ M) ≃ₐ[R] k := eM.restrictScalars R
  let eQ' : (R ⧸ Stafford38.Geometry.AffinePointCompletion.pointIdeal
    (residueCoordinates (σ := σ) M eM)) ≃ₐ[R] k := eQ.restrictScalars R
  exact eM'.trans eQ'.symm

/-- The contraction of the chosen maximal ideal is precisely evaluation at its
residue-coordinate point in the original polynomial ring. -/
theorem residuePoint_under_eq (M : Ideal B) (eM : (B ⧸ M) ≃ₐ[k] k) :
    Ideal.under R M = Stafford38.Geometry.AffinePointCompletion.pointIdeal
      (residueCoordinates (σ := σ) M eM) := by
  let ρ := residueEvaluation (σ := σ) M eM
  have hker : Ideal.under R M = RingHom.ker ρ := by
    ext a
    change algebraMap R B a ∈ M ↔ ρ a = 0
    constructor
    · intro ha
      have hmk : Ideal.Quotient.mk M (algebraMap R B a) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ha
      simp [ρ, residueEvaluation, hmk]
    · intro ha
      have hmk : Ideal.Quotient.mk M (algebraMap R B a) = 0 :=
        eM.injective (by simpa [ρ, residueEvaluation] using ha)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  have hpoint : Stafford38.Geometry.AffinePointCompletion.pointIdeal
      (residueCoordinates (σ := σ) M eM) = RingHom.ker ρ := by
    simpa [ρ] using pointIdeal_eq_residueEvaluation_ker (σ := σ) M eM
  exact hker.trans hpoint.symm

/-- The affine point completion and the formally-etale local completion compose using
the original coordinate map and the actual residue point. The hypothesis `hEt` is
the local formal-etaleness at the chosen closed point. -/
noncomputable def powerSeriesCompletionAtGroundPoint
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Fintype σ]
    [Algebra.EssFiniteType R B]
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    MvPowerSeries σ k ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime M))
        (Localization.AtPrime M) := by
  let x := residueCoordinates (σ := σ) M eM
  let q := Stafford38.Geometry.AffinePointCompletion.pointIdeal x
  letI : q.IsMaximal := residuePoint_isMaximal (σ := σ) M eM
  letI : q.IsPrime := inferInstance
  let ρ := residueEvaluation (σ := σ) M eM
  letI : Algebra R k := ρ.toRingHom.toAlgebra
  letI : IsScalarTower R k k := IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  let eQ := residuePointQuotientEquiv (σ := σ) M eM
  letI : IsScalarTower R k (B ⧸ M) := IsScalarTower.of_algebraMap_eq (fun a => by
    apply eM.injective
    rw [← Ideal.Quotient.mk_algebraMap R M a, eM.commutes]
    change eM (Ideal.Quotient.mk M (algebraMap R B a)) = ρ a
    rfl)
  letI : IsScalarTower R k (R ⧸ q) := IsScalarTower.of_algebraMap_eq (fun a => by
    apply eQ.injective
    calc
      eQ (algebraMap R (R ⧸ q) a) = ρ a := by
        change eQ (Ideal.Quotient.mk q a) = ρ a
        simpa [ρ] using residuePointQuotientEquiv_apply (σ := σ) M eM a
      _ = eQ (algebraMap k (R ⧸ q) (ρ a)) := by
        rw [eQ.commutes]
        rfl)
  have hq : Ideal.under R M = q := by
    simpa [x, q] using residuePoint_under_eq (σ := σ) M eM
  let e := residueEquivOverCoordinates (σ := σ) M eM
  exact (Stafford38.Geometry.AffinePointCompletion.powerSeriesCompletionAtPoint x).trans
    (Stafford38.Geometry.EtalePointCompletion.completionEquivOfEtaleResidue q M hq e)

/-- The second stage of the prescribed-point completion map sends a polynomial class
to the class of the same polynomial under the original coordinate algebra map. -/
theorem etaleCompletion_apply_of
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.EssFiniteType A B]
    (q : Ideal A) [q.IsPrime] (p : Ideal B) [p.IsPrime] [p.IsMaximal]
    (hq : Ideal.under A p = q)
    (e : (B ⧸ p) ≃ₐ[A] (A ⧸ q))
    [Algebra.FormallyEtale A (Localization.AtPrime p)] (a : A) :
    Stafford38.Geometry.EtalePointCompletion.completionEquivOfEtaleResidue
      q p hq e (AdicCompletion.of q A a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) (algebraMap A (Localization.AtPrime p) a) := by
  change Stafford38.Geometry.AdicCompletionMap.mapOfRingHom
      (algebraMap A (Localization.AtPrime p)) q
      (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Stafford38.Geometry.EtalePointCompletion.maximalIdeal_eq_map_of_formallyEtale
        q p hq)
      (AdicCompletion.of q A a) = _
  exact Stafford38.Geometry.AdicCompletionMap.mapOfRingHom_apply_of
    (algebraMap A (Localization.AtPrime p)) q
    (IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (Stafford38.Geometry.EtalePointCompletion.maximalIdeal_eq_map_of_formallyEtale
      q p hq) a

end
end Stafford38.Geometry.PrescribedAffineResidueCompletion
