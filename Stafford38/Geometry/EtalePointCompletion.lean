module
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Stafford38.Geometry.FormallyEtaleCompletion
public import Stafford38.Geometry.FormallyEtaleCompletionEquivalence

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Stafford38.Geometry.EtalePointCompletion

noncomputable section

/-- At a prime over `q`, formal unramifiedness identifies the maximal ideal of the
local target with the image of `q`. -/
theorem maximalIdeal_eq_map_of_formallyEtale
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.EssFiniteType R B]
    (q : Ideal R) [q.IsPrime] (p : Ideal B) [p.IsPrime]
    (hq : Ideal.under R p = q)
    [Algebra.FormallyEtale R (Localization.AtPrime p)] :
    IsLocalRing.maximalIdeal (Localization.AtPrime p) =
      q.map (algebraMap R (Localization.AtPrime p)) := by
  letI : p.LiesOver q := (Ideal.liesOver_iff p q).mpr hq.symm
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime p) :=
    Localization.AtPrime.algebraOfLiesOver q p
  letI : IsScalarTower R (Localization.AtPrime q) (Localization.AtPrime p) := inferInstance
  letI : Algebra.FormallyUnramified R (Localization.AtPrime p) := inferInstance
  letI : Algebra.EssFiniteType (Localization.AtPrime q) (Localization.AtPrime p) :=
    Algebra.EssFiniteType.of_comp R (Localization.AtPrime q) (Localization.AtPrime p)
  letI : Algebra.FormallyUnramified (Localization.AtPrime q) (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.localization_base q.primeCompl
  have hmax := Algebra.FormallyUnramified.map_maximalIdeal
    (R := Localization.AtPrime q) (S := Localization.AtPrime p)
  calc
    IsLocalRing.maximalIdeal (Localization.AtPrime p) =
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)).map
          (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) := hmax.symm
    _ = (q.map (algebraMap R (Localization.AtPrime q))).map
          (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) := by
      rw [IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)]
    _ = q.map (algebraMap R (Localization.AtPrime p)) := by
      rw [Ideal.map_map]
      congr 1
      exact (IsScalarTower.algebraMap_eq R (Localization.AtPrime q)
        (Localization.AtPrime p)).symm

/-- Passing from a prime quotient to the residue quotient of its localization does not
change the residue algebra when the prime is maximal. -/
noncomputable def quotientAtPrimeAlgEquiv
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal B) [p.IsMaximal] :
    (B ⧸ p) ≃ₐ[R]
      (Localization.AtPrime p) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  let T := Localization.AtPrime p
  let J := IsLocalRing.maximalIdeal T
  let f : B →ₐ[R] T := IsScalarTower.toAlgHom R B T
  have hUnder : Ideal.under B J = p := IsLocalization.AtPrime.under_maximalIdeal T p
  have hle : p ≤ J.comap f := by
    change p ≤ J.under B
    rw [hUnder]
  let g : B ⧸ p →ₐ[R] T ⧸ J := Ideal.quotientMapₐ J f hle
  have hinj : Function.Injective g := by
    apply Ideal.quotientMap_injective' (H := hle)
    change J.under B ≤ p
    rw [hUnder]
  have hsurj : Function.Surjective g := by
    change Function.Surjective
      (Ideal.quotientMap J (algebraMap B T) hle)
    have hMaxUnder : (J.under B).IsMaximal := by
      simpa [hUnder] using (inferInstance : p.IsMaximal)
    exact IsLocalization.surjective_quotientMap_of_maximal_of_localization
      p.primeCompl T (I := J) (J := p)
      (H := by rw [hUnder]) hMaxUnder
  exact AlgEquiv.ofBijective g ⟨hinj, hsurj⟩

private theorem quotientAtPrimeAlgEquiv_mk
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal B) [p.IsMaximal] (b : B) :
    quotientAtPrimeAlgEquiv (R := R) (B := B) p (Ideal.Quotient.mk p b) =
      Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (algebraMap B (Localization.AtPrime p) b) := by
  let T := Localization.AtPrime p
  let J := IsLocalRing.maximalIdeal T
  let f : B →ₐ[R] T := IsScalarTower.toAlgHom R B T
  have hUnder : Ideal.under B J = p := IsLocalization.AtPrime.under_maximalIdeal T p
  have hle : p ≤ J.comap f := by
    change p ≤ J.under B
    rw [hUnder]
  change (Ideal.quotientMapₐ J f hle) (Ideal.Quotient.mk p b) =
    Ideal.Quotient.mkₐ R J (f b)
  exact Ideal.quotient_map_mkₐ J f hle

private theorem reverseStage_apply_mk
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (I : Ideal R) (J : Ideal T) (hJ : J = I.map (algebraMap R T))
    (ψ : T →ₐ[R] AdicCompletion I R) (b : T) :
    Stafford38.Geometry.FormallyEtaleCompletionEquivalence.reverseStage I J hJ ψ 1
        (Ideal.Quotient.mkₐ R (J ^ 1) b) = AdicCompletion.evalₐ I 1 (ψ b) := by
  let u : T →ₐ[R] R ⧸ I ^ 1 := (AdicCompletion.evalₐ I 1).comp ψ
  have hker : (I ^ 1).map (algebraMap R T) ≤ RingHom.ker (u : T →+* R ⧸ I ^ 1) := by
    apply (Ideal.map_le_iff_le_comap).2
    intro a ha
    change AdicCompletion.evalₐ I 1 (ψ (algebraMap R T a)) = 0
    rw [ψ.commutes]
    have ha' : a ∈ I := by simpa only [Submodule.pow_one] using ha
    simp [Ideal.Quotient.eq_zero_iff_mem, ha']
  have hpow : (I ^ 1).map (algebraMap R T) = J ^ 1 := by
    rw [Ideal.map_pow, hJ]
  have hkill : ∀ x ∈ J ^ 1, u x = 0 := by
    intro x hx
    apply RingHom.mem_ker.mp
    exact hker (hpow.symm ▸ hx)
  have hcomp := Ideal.Quotient.liftₐ_comp (R₁ := R) (J ^ 1) u hkill
  change ((Ideal.Quotient.liftₐ (R₁ := R) (J ^ 1) u hkill).comp
      (Ideal.Quotient.mkₐ R (J ^ 1))) b = _
  exact DFunLike.congr_fun hcomp b

/-- The completion of the coordinate ring at a rational point agrees with the
completion of the etale local chart above that point. -/
noncomputable def completionEquivOfEtaleResidue
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.EssFiniteType R B]
    (q : Ideal R) [q.IsPrime] (p : Ideal B) [p.IsPrime] [p.IsMaximal]
    (hq : Ideal.under R p = q)
    (e : (B ⧸ p) ≃ₐ[R] (R ⧸ q))
    [Algebra.FormallyEtale R (Localization.AtPrime p)] :
    AdicCompletion q R ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) := by
  let J : Ideal (Localization.AtPrime p) :=
    IsLocalRing.maximalIdeal (Localization.AtPrime p)
  have hJ : J = q.map (algebraMap R (Localization.AtPrime p)) :=
    maximalIdeal_eq_map_of_formallyEtale q p hq
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime p) := inferInstance
  haveI : Algebra.FormallySmooth R (Localization.AtPrime p) := inferInstance
  let locRes : (B ⧸ p) ≃ₐ[R]
      (Localization.AtPrime p) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    quotientAtPrimeAlgEquiv (R := R) (B := B) p
  let residueEquiv := locRes.symm.trans e
  let qeq := Ideal.quotientEquivAlgOfEq R (Submodule.pow_one q)
  let jMap := Ideal.quotientEquivAlgOfEq R (Submodule.pow_one J)
  let residueEquiv1 :=
    jMap.trans residueEquiv |>.trans qeq.symm
  have hjMap (b : Localization.AtPrime p) :
      jMap (Ideal.Quotient.mkₐ R (J ^ 1) b) = Ideal.Quotient.mkₐ R J b := by
    dsimp only [jMap]
    change Ideal.quotientEquivAlgOfEq R (Submodule.pow_one J)
        (Ideal.Quotient.mk (J ^ 1) b) = Ideal.Quotient.mk J b
    exact Ideal.quotientEquivAlgOfEq_mk (R₁ := R) (h := Submodule.pow_one J) b
  let r : Localization.AtPrime p →ₐ[R] R ⧸ q :=
    residueEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  let liftExists :=
    Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq (R := R) (I := q) r
  let ψ := Classical.choose liftExists
  have hψ := Classical.choose_spec liftExists
  have hG :
      Stafford38.Geometry.FormallyEtaleCompletionEquivalence.reverseStage q J hJ ψ 1 =
        residueEquiv1.toAlgHom := by
    apply Ideal.Quotient.algHom_ext R
    apply AlgHom.ext
    intro b
    change Stafford38.Geometry.FormallyEtaleCompletionEquivalence.reverseStage q J hJ ψ 1
        (Ideal.Quotient.mkₐ R (J ^ 1) b) = residueEquiv1
          (Ideal.Quotient.mkₐ R (J ^ 1) b)
    rw [reverseStage_apply_mk]
    apply qeq.injective
    calc
      qeq (AdicCompletion.evalₐ q 1 (ψ b)) =
          AdicCompletion.evalOneₐ q (ψ b) := by
        change (qeq.toAlgHom) _ = _
        rw [Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ]
        exact AdicCompletion.factorₐ_evalₐ_one q (ψ b)
      _ = r b := DFunLike.congr_fun hψ b
      _ = residueEquiv (Ideal.Quotient.mk J b) := by
        rfl
      _ = qeq (residueEquiv1 (Ideal.Quotient.mkₐ R (J ^ 1) b)) := by
        dsimp only [residueEquiv1]
        simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
        exact (congrArg residueEquiv (hjMap b)).symm
  have hF :
      Stafford38.Geometry.FormallyEtaleCompletionEquivalence.forwardStage q J hJ 1 =
        residueEquiv1.symm.toAlgHom := by
    apply Ideal.Quotient.algHom_ext R
    apply AlgHom.ext
    intro a
    change Ideal.Quotient.mkₐ R (J ^ 1) (algebraMap R (Localization.AtPrime p) a) =
      residueEquiv1.symm (Ideal.Quotient.mkₐ R (q ^ 1) a)
    have hloc : locRes.symm
        (Ideal.Quotient.mkₐ R J (algebraMap R (Localization.AtPrime p) a)) =
          Ideal.Quotient.mkₐ R p (algebraMap R B a) := by
      apply locRes.injective
      rw [AlgEquiv.apply_symm_apply]
      change Ideal.Quotient.mkₐ R J (algebraMap R (Localization.AtPrime p) a) =
        quotientAtPrimeAlgEquiv (R := R) (B := B) p
          (Ideal.Quotient.mk p (algebraMap R B a))
      rw [quotientAtPrimeAlgEquiv_mk]
      congr 1
    have he : e (Ideal.Quotient.mkₐ R p (algebraMap R B a)) =
        Ideal.Quotient.mkₐ R q a := by
      exact e.commutes a
    apply residueEquiv1.injective
    rw [AlgEquiv.apply_symm_apply]
    change qeq.symm
      (residueEquiv (jMap
        (Ideal.Quotient.mkₐ R (J ^ 1) (algebraMap R (Localization.AtPrime p) a)))) = _
    rw [hjMap]
    dsimp only [residueEquiv]
    rw [AlgEquiv.trans_apply]
    rw [hloc, he]
    apply qeq.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (Ideal.quotientEquivAlgOfEq_mk (R₁ := R)
      (h := Submodule.pow_one q) a).symm
  have hres :
      (Stafford38.Geometry.FormallyEtaleCompletionEquivalence.forwardStage q J hJ 1).comp
          (Stafford38.Geometry.FormallyEtaleCompletionEquivalence.reverseStage q J hJ ψ 1) =
        AlgHom.id R ((Localization.AtPrime p) ⧸ (J ^ 1)) := by
    rw [hF, hG]
    apply AlgHom.ext
    intro x
    simp
  exact Stafford38.Geometry.FormallyEtaleCompletionEquivalence.formalEtaleCompletionEquiv
    q J hJ ψ hres

end
end Stafford38.Geometry.EtalePointCompletion
