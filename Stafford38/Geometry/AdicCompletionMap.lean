module
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.AdicCompletionMap

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B]

/-- A ring map taking the adic ideal onto the target ideal induces a map of
adic completions. -/
def mapOfRingHom (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map f) : AdicCompletion I A →+* AdicCompletion J B := by
  classical
  let stage : (n : ℕ) → AdicCompletion I A →+* B ⧸ J ^ n := fun n =>
    (Ideal.quotientMap (J ^ n) f (by
      have hpow : (I ^ n).map f = J ^ n := by rw [Ideal.map_pow, hJ]
      intro a ha
      rw [← hpow]
      exact Ideal.mem_map_of_mem f ha)).comp (AdicCompletion.evalₐ I n).toRingHom
  have hstage : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow J hle).comp (stage n) = stage m := by
    intro m n hle
    ext x
    apply AdicCompletion.induction_on I A x
    intro c
    simp only [stage, RingHom.comp_apply]
    change Ideal.Quotient.mk (J ^ m) (f (c n)) =
      Ideal.Quotient.mk (J ^ m) (f (c m))
    apply Ideal.Quotient.eq.mpr
    have hc : c m - c n ∈ I ^ m := by
      have hc' := SModEq.sub_mem.mp (c.property hle)
      simpa [smul_eq_mul, Ideal.mul_top] using hc'
    have hneg : c n - c m ∈ I ^ m := by simpa using (I ^ m).neg_mem hc
    have hmap : f (c n) - f (c m) ∈ (I ^ m).map f := by
      simpa only [map_sub] using Ideal.mem_map_of_mem f hneg
    have hpow : (I ^ m).map f = J ^ m := by rw [Ideal.map_pow, hJ]
    rw [hpow] at hmap
    exact hmap
  exact AdicCompletion.liftRingHom J stage hstage

theorem eval_mapOfRingHom (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map f) (x : AdicCompletion I A) (n : ℕ) :
    AdicCompletion.evalₐ J n (mapOfRingHom f I J hJ x) =
      Ideal.quotientMap (J ^ n) f (by
        have hpow : (I ^ n).map f = J ^ n := by rw [Ideal.map_pow, hJ]
        intro a ha
        rw [← hpow]
        exact Ideal.mem_map_of_mem f ha) (AdicCompletion.evalₐ I n x) := by
  classical
  unfold mapOfRingHom
  simp only [AdicCompletion.evalₐ_liftRingHom]
  rfl

@[simp]
theorem mapOfRingHom_apply_of (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map f) (a : A) :
    mapOfRingHom f I J hJ (AdicCompletion.of I A a) =
      AdicCompletion.of J B (f a) := by
  classical
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_mapOfRingHom]
  simp

theorem mapOfRingHom_comp {C : Type*} [CommRing C]
    (f : A →+* B) (g : B →+* C) (I : Ideal A) (J : Ideal B) (K : Ideal C)
    (hJ : J = I.map f) (hK : K = J.map g) :
    (mapOfRingHom g J K hK).comp (mapOfRingHom f I J hJ) =
      mapOfRingHom (g.comp f) I K (by rw [hK, hJ, Ideal.map_map]) := by
  have hIK : K = I.map (g.comp f) := by rw [hK, hJ, Ideal.map_map]
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ K n
      (mapOfRingHom g J K hK (mapOfRingHom f I J hJ x)) = _
  rw [eval_mapOfRingHom, eval_mapOfRingHom]
  let qf : A ⧸ I ^ n →+* B ⧸ J ^ n :=
    Ideal.quotientMap (J ^ n) f (by
      have hpow : (I ^ n).map f = J ^ n := by rw [Ideal.map_pow, hJ]
      intro a ha; rw [← hpow]; exact Ideal.mem_map_of_mem f ha)
  let qg : B ⧸ J ^ n →+* C ⧸ K ^ n :=
    Ideal.quotientMap (K ^ n) g (by
      have hpow : (J ^ n).map g = K ^ n := by rw [Ideal.map_pow, hK]
      intro b hb; rw [← hpow]; exact Ideal.mem_map_of_mem g hb)
  let qcomp : A ⧸ I ^ n →+* C ⧸ K ^ n :=
    Ideal.quotientMap (K ^ n) (g.comp f) (by
      have hpow : (I ^ n).map (g.comp f) = K ^ n := by rw [Ideal.map_pow, hIK]
      intro a ha; rw [← hpow]; exact Ideal.mem_map_of_mem (g.comp f) ha)
  rw [eval_mapOfRingHom (g.comp f) I K hIK x n]
  change qg (qf (AdicCompletion.evalₐ I n x)) =
    qcomp (AdicCompletion.evalₐ I n x)
  have hq : qg.comp qf = qcomp := by
    apply RingHom.ext
    intro y
    induction y using Quotient.inductionOn' with
    | h a =>
      change Ideal.Quotient.mk (K ^ n) (g (f a)) =
        Ideal.Quotient.mk (K ^ n) ((g.comp f) a)
      simp
  exact RingHom.congr_fun hq _

end
end Stafford38.Geometry.AdicCompletionMap
