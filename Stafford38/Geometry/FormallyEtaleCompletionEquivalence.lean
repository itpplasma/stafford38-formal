module
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Stafford38.Geometry.AdicCompletionMap

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Stafford38.Geometry.FormallyEtaleCompletionEquivalence

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (I : Ideal A) (J : Ideal B)

private theorem factor_evalₐ_comp (m n : ℕ) (hmn : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  apply AdicCompletion.induction_on I A x
  intro c
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  apply Ideal.Quotient.eq.mpr
  have hc : c.val m - c.val n ∈ I ^ m := by
    have hc' := SModEq.sub_mem.mp (c.property hmn)
    simpa [smul_eq_mul, Ideal.mul_top] using hc'
  simpa using (I ^ m).neg_mem hc

def baseAlgHom : A →ₐ[A] B := IsScalarTower.toAlgHom A A B

theorem idealPowMap_eq (n : ℕ) (hJ : J = I.map (algebraMap A B)) :
    (I ^ n).map (algebraMap A B) = J ^ n := by
  rw [Ideal.map_pow, hJ]

/-- The map on finite quotients induced by the original algebra map. -/
def forwardStage (hJ : J = I.map (algebraMap A B)) (n : ℕ) :
    A ⧸ I ^ n →ₐ[A] B ⧸ J ^ n :=
  Ideal.quotientMapₐ (R₁ := A) (I := I ^ n) (J ^ n) baseAlgHom
    ((Ideal.map_le_iff_le_comap).mp (by rw [← idealPowMap_eq I J n hJ]; exact le_rfl))

private theorem forwardStage_compatible (hJ : J = I.map (algebraMap A B))
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
        (forwardStage I J hJ n) =
      (forwardStage I J hJ m).comp
        (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)) := by
  apply Ideal.Quotient.algHom_ext A
  ext a

/-- A lift to the base completion induces maps in the reverse direction at every
finite quotient level. -/
def reverseStage (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A) (n : ℕ) : B ⧸ J ^ n →ₐ[A] A ⧸ I ^ n := by
  let u : B →ₐ[A] A ⧸ I ^ n := (AdicCompletion.evalₐ I n).comp ψ
  have hkill : ∀ b ∈ J ^ n, u b = 0 := by
    have hker : (I ^ n).map (algebraMap A B) ≤ RingHom.ker (u : B →+* A ⧸ I ^ n) := by
      apply (Ideal.map_le_iff_le_comap).2
      intro a ha
      change AdicCompletion.evalₐ I n (ψ (algebraMap A B a)) = 0
      rw [ψ.commutes]
      simp [Ideal.Quotient.eq_zero_iff_mem, ha]
    rw [← idealPowMap_eq I J n hJ]
    exact fun b hb => RingHom.mem_ker.mp (hker hb)
  exact Ideal.Quotient.liftₐ (R₁ := A) (J ^ n) u hkill

private theorem reverseStage_mk (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A) (n : ℕ) (b : B) :
    reverseStage I J hJ ψ n (Ideal.Quotient.mkₐ A (J ^ n) b) =
      AdicCompletion.evalₐ I n (ψ b) := by
  let u : B →ₐ[A] A ⧸ I ^ n := (AdicCompletion.evalₐ I n).comp ψ
  have hkill : ∀ x ∈ J ^ n, u x = 0 := by
    unfold u
    have hker : (I ^ n).map (algebraMap A B) ≤
        RingHom.ker ((AdicCompletion.evalₐ I n).comp ψ : B →+* A ⧸ I ^ n) := by
      apply (Ideal.map_le_iff_le_comap).2
      intro a ha
      change AdicCompletion.evalₐ I n (ψ (algebraMap A B a)) = 0
      rw [ψ.commutes]
      simp [Ideal.Quotient.eq_zero_iff_mem, ha]
    rw [← idealPowMap_eq I J n hJ]
    exact fun x hx => RingHom.mem_ker.mp (hker hx)
  have hcomp := Ideal.Quotient.liftₐ_comp (R₁ := A) (J ^ n) u hkill
  change ((Ideal.Quotient.liftₐ (R₁ := A) (J ^ n) u hkill).comp
      (Ideal.Quotient.mkₐ A (J ^ n))) b = _
  exact DFunLike.congr_fun hcomp b

private theorem reverseStage_compatible (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
        (reverseStage I J hJ ψ n) =
      (reverseStage I J hJ ψ m).comp
        (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)) := by
  apply Ideal.Quotient.algHom_ext A
  ext b
  calc
    Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)
        (reverseStage I J hJ ψ n (Ideal.Quotient.mkₐ A (J ^ n) b)) =
      Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)
        (AdicCompletion.evalₐ I n (ψ b)) := by
      rw [reverseStage_mk]
    _ = AdicCompletion.evalₐ I m (ψ b) := factor_evalₐ_comp I m n hmn (ψ b)
    _ = reverseStage I J hJ ψ m (Ideal.Quotient.mkₐ A (J ^ m) b) := by
      exact (reverseStage_mk I J hJ ψ m b).symm

theorem reverseCompletionMap_compatible (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp
        (((reverseStage I J hJ ψ n).toRingHom).comp (AdicCompletion.evalₐ J n).toRingHom) =
      ((reverseStage I J hJ ψ m).toRingHom).comp (AdicCompletion.evalₐ J m).toRingHom := by
  ext x
  change Ideal.Quotient.factorPow I hmn
      (reverseStage I J hJ ψ n (AdicCompletion.evalₐ J n x)) =
    reverseStage I J hJ ψ m (AdicCompletion.evalₐ J m x)
  have hstage := DFunLike.congr_fun
    (reverseStage_compatible I J hJ ψ hmn) (AdicCompletion.evalₐ J n x)
  calc
    Ideal.Quotient.factorPow I hmn
        (reverseStage I J hJ ψ n (AdicCompletion.evalₐ J n x)) =
      reverseStage I J hJ ψ m
        (Ideal.Quotient.factorPow J hmn (AdicCompletion.evalₐ J n x)) := hstage
    _ = reverseStage I J hJ ψ m (AdicCompletion.evalₐ J m x) := by
      congr 1
      exact factor_evalₐ_comp J m n hmn x

/-- The reverse map on completions induced by the supplied lift to the base completion. -/
def reverseCompletionMap (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A) :
    AdicCompletion J B →+* AdicCompletion I A :=
  AdicCompletion.liftRingHom I
    (fun n => ((reverseStage I J hJ ψ n).toRingHom).comp
      (AdicCompletion.evalₐ J n).toRingHom)
    (reverseCompletionMap_compatible I J hJ ψ)

private theorem eval_reverseCompletionMap (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A) (n : ℕ) (x : AdicCompletion J B) :
    AdicCompletion.evalₐ I n (reverseCompletionMap I J hJ ψ x) =
      reverseStage I J hJ ψ n (AdicCompletion.evalₐ J n x) := by
  simpa [reverseCompletionMap] using
    (AdicCompletion.evalₐ_liftRingHom I
      (fun k => ((reverseStage I J hJ ψ k).toRingHom).comp
        (AdicCompletion.evalₐ J k).toRingHom)
      (reverseCompletionMap_compatible I J hJ ψ)
      n x)

private theorem reverse_forward_stage (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A) (n : ℕ) :
    (reverseStage I J hJ ψ n).comp (forwardStage I J hJ n) =
      AlgHom.id A (A ⧸ I ^ n) := by
  apply Ideal.Quotient.algHom_ext A
  ext a

private theorem factor_to_first_power_ker_nilpotent (n : ℕ) :
    IsNilpotent (RingHom.ker
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right
        (show 1 ≤ n + 1 by omega)) :
          B ⧸ J ^ (n + 1) →+* B ⧸ J ^ 1)) := by
  let hpow : J ^ (n + 1) ≤ J ^ 1 :=
    Ideal.pow_le_pow_right (show 1 ≤ n + 1 by omega)
  change IsNilpotent (RingHom.ker (Ideal.Quotient.factor hpow))
  rw [Ideal.Quotient.factor_ker hpow]
  refine ⟨n + 1, ?_⟩
  rw [← Ideal.map_pow]
  have hp : (J ^ 1) ^ (n + 1) = J ^ (n + 1) := by simp
  rw [hp]
  simp

private theorem forward_reverse_stage
    [Algebra.FormallyUnramified A B]
    (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A)
    (hres : (forwardStage I J hJ 1).comp (reverseStage I J hJ ψ 1) =
      AlgHom.id A (B ⧸ J ^ 1)) (n : ℕ) :
    (forwardStage I J hJ n).comp (reverseStage I J hJ ψ n) =
      AlgHom.id A (B ⧸ J ^ n) := by
  cases n with
  | zero =>
    apply AlgHom.ext
    intro b
    haveI : Subsingleton (B ⧸ J ^ 0) := by simp
    exact Subsingleton.elim _ _
  | succ k =>
    let hn : 1 ≤ k + 1 := by omega
    let f : B ⧸ J ^ (k + 1) →+* B ⧸ J ^ 1 :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hn)
    have hnil : IsNilpotent (RingHom.ker f) := by
      simpa [f, hn] using factor_to_first_power_ker_nilpotent (J := J) k
    let g₁ : B →ₐ[A] B ⧸ J ^ (k + 1) :=
      ((forwardStage I J hJ (k + 1)).comp (reverseStage I J hJ ψ (k + 1))).comp
        (Ideal.Quotient.mkₐ A (J ^ (k + 1)))
    let g₂ : B →ₐ[A] B ⧸ J ^ (k + 1) := Ideal.Quotient.mkₐ A (J ^ (k + 1))
    have hred : f.comp (g₁ : B →+* B ⧸ J ^ (k + 1)) =
        f.comp (g₂ : B →+* B ⧸ J ^ (k + 1)) := by
      ext b
      change f (forwardStage I J hJ (k + 1)
          (reverseStage I J hJ ψ (k + 1) (Ideal.Quotient.mkₐ A (J ^ (k + 1)) b))) =
        Ideal.Quotient.mk (J ^ 1) b
      calc
        f (forwardStage I J hJ (k + 1)
            (reverseStage I J hJ ψ (k + 1) (Ideal.Quotient.mkₐ A (J ^ (k + 1)) b))) =
            forwardStage I J hJ 1
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right hn)
              (reverseStage I J hJ ψ (k + 1)
                (Ideal.Quotient.mkₐ A (J ^ (k + 1)) b))) := by
            exact DFunLike.congr_fun
              (forwardStage_compatible I J hJ hn)
              (reverseStage I J hJ ψ (k + 1) (Ideal.Quotient.mkₐ A (J ^ (k + 1)) b))
        _ = forwardStage I J hJ 1
            (reverseStage I J hJ ψ 1 (Ideal.Quotient.mkₐ A (J ^ 1) b)) := by
            congr 1
            exact DFunLike.congr_fun
              (reverseStage_compatible I J hJ ψ hn)
              (Ideal.Quotient.mkₐ A (J ^ (k + 1)) b)
        _ = Ideal.Quotient.mk (J ^ 1) b := by
            have h := DFunLike.congr_fun hres (Ideal.Quotient.mkₐ A (J ^ 1) b)
            simpa using h
    have huniq := Algebra.FormallyUnramified.lift_unique_of_ringHom
      (R := A) (A := B) f hnil g₁ g₂ hred
    apply Ideal.Quotient.algHom_ext A
    ext b
    exact DFunLike.congr_fun huniq b

/-- The map on completions induced by `A → B`. -/
def forwardCompletionMap (hJ : J = I.map (algebraMap A B)) :
    AdicCompletion I A →+* AdicCompletion J B :=
  Stafford38.Geometry.AdicCompletionMap.mapOfRingHom (algebraMap A B) I J hJ

private theorem eval_forwardCompletionMap (hJ : J = I.map (algebraMap A B))
    (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (forwardCompletionMap I J hJ x) =
      forwardStage I J hJ n (AdicCompletion.evalₐ I n x) := by
  simpa [forwardCompletionMap, forwardStage, baseAlgHom, Ideal.quotientMapₐ] using
    (Stafford38.Geometry.AdicCompletionMap.eval_mapOfRingHom
      (algebraMap A B) I J hJ x n)

theorem forward_reverse_completion
    [Algebra.FormallyUnramified A B]
    (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A)
    (hres : (forwardStage I J hJ 1).comp (reverseStage I J hJ ψ 1) =
      AlgHom.id A (B ⧸ J ^ 1))
    (x : AdicCompletion J B) :
    forwardCompletionMap I J hJ (reverseCompletionMap I J hJ ψ x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_forwardCompletionMap, eval_reverseCompletionMap]
  exact DFunLike.congr_fun (forward_reverse_stage I J hJ ψ hres n)
    (AdicCompletion.evalₐ J n x)

theorem reverse_forward_completion
    (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A)
    (x : AdicCompletion I A) :
    reverseCompletionMap I J hJ ψ (forwardCompletionMap I J hJ x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_reverseCompletionMap, eval_forwardCompletionMap]
  exact DFunLike.congr_fun (reverse_forward_stage I J hJ ψ n)
    (AdicCompletion.evalₐ I n x)

/-- A formally unramified algebra with an adic residue retraction has
isomorphic completions. The explicit `ψ` and first-quotient identity are the
lift and residue-identification data required by this comparison. -/
noncomputable def formalEtaleCompletionEquiv
    [Algebra.FormallyUnramified A B]
    (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A)
    (hres : (forwardStage I J hJ 1).comp (reverseStage I J hJ ψ 1) =
      AlgHom.id A (B ⧸ J ^ 1)) :
    AdicCompletion I A ≃+* AdicCompletion J B where
  toFun := forwardCompletionMap I J hJ
  invFun := reverseCompletionMap I J hJ ψ
  left_inv := reverse_forward_completion I J hJ ψ
  right_inv := forward_reverse_completion I J hJ ψ hres
  map_mul' := (forwardCompletionMap I J hJ).map_mul
  map_add' := (forwardCompletionMap I J hJ).map_add

end
end Stafford38.Geometry.FormallyEtaleCompletionEquivalence
