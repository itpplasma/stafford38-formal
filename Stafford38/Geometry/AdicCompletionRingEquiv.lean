module
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Stafford38.Geometry.AdicCompletionMap

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.AdicCompletionRingEquiv

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B]

/-- An isomorphism of rings carrying one adic ideal to another induces an
isomorphism of the corresponding adic completions. -/
def mapOfRingEquiv (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map (e : A →+* B)) :
    AdicCompletion I A →+* AdicCompletion J B :=
  Stafford38.Geometry.AdicCompletionMap.mapOfRingHom (e : A →+* B) I J hJ

/-- Evaluation at a finite quotient commutes with the canonical completion map. -/
theorem eval_mapOfRingEquiv (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map (e : A →+* B)) (x : AdicCompletion I A) (n : ℕ) :
    AdicCompletion.evalₐ J n (mapOfRingEquiv e I J hJ x) =
      Ideal.quotientEquiv (I ^ n) (J ^ n) e (by rw [hJ, Ideal.map_pow])
        (AdicCompletion.evalₐ I n x) := by
  rw [mapOfRingEquiv, Stafford38.Geometry.AdicCompletionMap.eval_mapOfRingHom]
  rfl

/-- The canonical map sends the dense polynomial copy through the given ring
equivalence. -/
@[simp]
theorem mapOfRingEquiv_apply_of (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map (e : A →+* B)) (a : A) :
    mapOfRingEquiv e I J hJ (AdicCompletion.of I A a) =
      AdicCompletion.of J B (e a) := by
  exact Stafford38.Geometry.AdicCompletionMap.mapOfRingHom_apply_of
    (e : A →+* B) I J hJ a

/-- A ring equivalence carrying the defining ideals induces an equivalence of
adic completions. -/
def ofRingEquiv (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map (e : A →+* B)) :
    AdicCompletion I A ≃+* AdicCompletion J B := by
  classical
  let q (n : ℕ) : A ⧸ I ^ n ≃+* B ⧸ J ^ n :=
    Ideal.quotientEquiv (I ^ n) (J ^ n) e (by rw [hJ, Ideal.map_pow])
  let forward : AdicCompletion I A →+* AdicCompletion J B :=
    mapOfRingEquiv e I J hJ
  have hforward (x : AdicCompletion I A) (n : ℕ) :
      AdicCompletion.evalₐ J n (forward x) = q n (AdicCompletion.evalₐ I n x) := by
    simpa [forward, q] using eval_mapOfRingEquiv e I J hJ x n
  have hJinv : I = J.map (e.symm : B →+* A) := by
    rw [hJ, Ideal.map_map]; simp
  let backward : AdicCompletion J B →+* AdicCompletion I A :=
    mapOfRingEquiv e.symm J I hJinv
  have hbackward (x : AdicCompletion J B) (n : ℕ) :
      AdicCompletion.evalₐ I n (backward x) = (q n).symm (AdicCompletion.evalₐ J n x) := by
    simpa [backward, q] using eval_mapOfRingEquiv e.symm J I hJinv x n
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_
      map_mul' := forward.map_mul
      map_add' := forward.map_add }
  · intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hbackward, hforward]
    exact (q n).symm_apply_apply _
  · intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hforward, hbackward]
    exact (q n).apply_symm_apply _

/-- Evaluation of the completion equivalence is the finite-quotient map induced by
the original ring equivalence. -/
theorem eval_ofRingEquiv (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map (e : A →+* B)) (x : AdicCompletion I A) (n : ℕ) :
    AdicCompletion.evalₐ J n (ofRingEquiv e I J hJ x) =
      Ideal.quotientEquiv (I ^ n) (J ^ n) e (by rw [hJ, Ideal.map_pow])
        (AdicCompletion.evalₐ I n x) := by
  have hfun : (fun y => ofRingEquiv e I J hJ y) = mapOfRingEquiv e I J hJ := by
    funext y
    rfl
  rw [congrFun hfun x]
  exact eval_mapOfRingEquiv e I J hJ x n

/-- The completion equivalence sends the dense polynomial copy through the given
ring equivalence. -/
@[simp]
theorem ofRingEquiv_apply_of (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map (e : A →+* B)) (a : A) :
    ofRingEquiv e I J hJ (AdicCompletion.of I A a) =
      AdicCompletion.of J B (e a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_ofRingEquiv, AdicCompletion.evalₐ_of]
  simp

end
end Stafford38.Geometry.AdicCompletionRingEquiv
