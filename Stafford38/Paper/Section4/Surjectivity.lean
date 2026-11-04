module

public import Stafford38.Paper.Section4.Residue
public import Stafford38.Weyl.EulerRemainder

@[expose] public section

/-!
# Proposition 4.3: right multiplication by `x₁` on `Q = A_n/𝓘` is surjective

The printed proof works with `q A_{≥0}`, the classes `q r` of the elements
`r ∈ A_{≥0}`, where `q` is the class of `1`.  Its paragraphs are: `q ∈ (qA_{≥0})x₁`;
`qA_{≥0} = (qA_{≥0})x₁` by normality; `qA_{≥0}` is stable under `p` and under
`C = A_{n-1}[x₁]`; hence `qA_{≥0} = Q`.  They are stated below for a ring with a
right ideal, then applied to the presented Weyl algebra.
-/

namespace Stafford38.Paper.Section4

open Stafford38.EulerSurjectivity
open Stafford38.WeylEulerSubring
open Stafford38.WeylEulerResidue
open Stafford38.WeylEulerRemainder
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport
open Stafford38.OrePairStage
open Stafford38.OreIteratedPairStage

noncomputable section

section Generic

variable {A : Type*} [Ring A] (I : RightIdeal A) (R : Subring A)

/-- `q A_{≥0}`: the classes `q r = [r]` with `r ∈ R`. -/
def classSet : Set (RightQuotient I) := {z | ∃ r ∈ R, z = qmk I r}

variable {I R}

/-- **`q ∈ (qA_{≥0})x₁`.**  From `1 + u₀x₁ ∈ 𝓘`, `q = −q u₀ x₁`. -/
theorem step_4_3_q_mem (x u₀ : A) (hres : 1 + u₀ * x ∈ I) :
    qmk I 1 = rightMul I x (qmk I (-u₀)) := by
  rw [← qmk_right_mul]
  refine ((Submodule.Quotient.eq I).2 ?_).symm
  convert I.neg_mem hres using 1
  noncomm_ring

/-- **Equation (normal-surj): `qA_{≥0} = (qA_{≥0})x₁`.**  `⊇` because `x₁ ∈ A_{≥0}`;
`⊆` because `qr = −(qu₀)x₁r = −(qu₀r')x₁` for `x₁r = r'x₁`. -/
theorem step_4_3_normal_surj (x u₀ : A) (hx : x ∈ R) (hu₀ : u₀ ∈ R)
    (hres : 1 + u₀ * x ∈ I)
    (hnormal : ∀ r ∈ R, ∃ r' ∈ R, x * r = r' * x) :
    classSet I R = rightMul I x '' classSet I R := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨r', hr', hxr⟩ := hnormal r hr
    refine ⟨qmk I (-(u₀ * r')), ⟨_, R.neg_mem (R.mul_mem hu₀ hr'), rfl⟩, ?_⟩
    calc rightMul I x (qmk I (-(u₀ * r'))) = qmk I (-u₀ * (r' * x)) := by
          rw [← qmk_right_mul]; congr 1; noncomm_ring
      _ = qmk I (-u₀ * x * r) := by rw [← hxr, mul_assoc]
      _ = rightMul I r (rightMul I x (qmk I (-u₀))) := by
          rw [← qmk_right_mul, ← qmk_right_mul]
      _ = qmk I r := by rw [← step_4_3_q_mem x u₀ hres, ← qmk_right_mul, one_mul]
  · rintro ⟨w, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r * x, R.mul_mem hr hx, (qmk_right_mul I r x).symm⟩

/-- **Stability under `p`.**  If `m = m'x₁` with `m' ∈ qA_{≥0}`, then
`mp = m'(x₁p) = m'E ∈ qA_{≥0}`. -/
theorem step_4_3_stable_momentum (x p : A) (hE : x * p ∈ R)
    (hsurj : classSet I R = rightMul I x '' classSet I R) :
    ∀ z ∈ classSet I R, rightMul I p z ∈ classSet I R := by
  intro z hz
  rw [hsurj] at hz
  obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hz
  refine ⟨r * (x * p), R.mul_mem hr hE, ?_⟩
  rw [← qmk_right_mul, ← qmk_right_mul, mul_assoc]

/-- **Stability under `C`.**  `C = A_{n-1}[x₁] ⊆ A_{≥0}`. -/
theorem step_4_3_stable_coefficients (C : Subring A) (hC : C ≤ R) :
    ∀ c ∈ C, ∀ z ∈ classSet I R, rightMul I c z ∈ classSet I R := by
  rintro c hc _ ⟨r, hr, rfl⟩
  exact ⟨r * c, R.mul_mem hr (hC hc), (qmk_right_mul I r c).symm⟩

variable (I R) in
/-- The right multipliers preserving `qA_{≥0}` form a subring. -/
def classSetStabilizer : Subring A where
  carrier := {a | ∀ z ∈ classSet I R, rightMul I a z ∈ classSet I R}
  zero_mem' := by
    intro z _
    refine ⟨0, R.zero_mem, ?_⟩
    change MulOpposite.op (0 : A) • z = _
    rw [MulOpposite.op_zero, zero_smul]
    rfl
  one_mem' := by
    intro z hz
    change MulOpposite.op (1 : A) • z ∈ _
    rwa [MulOpposite.op_one, one_smul]
  add_mem' := by
    intro a b ha hb z hz
    obtain ⟨r, hr, hra⟩ := ha z hz
    obtain ⟨s, hs, hsb⟩ := hb z hz
    refine ⟨r + s, R.add_mem hr hs, ?_⟩
    change MulOpposite.op (a + b) • z = _
    rw [MulOpposite.op_add, add_smul]
    change rightMul I a z + rightMul I b z = _
    rw [hra, hsb]
    rfl
  neg_mem' := by
    intro a ha z hz
    obtain ⟨r, hr, hra⟩ := ha z hz
    refine ⟨-r, R.neg_mem hr, ?_⟩
    change MulOpposite.op (-a) • z = _
    rw [MulOpposite.op_neg, neg_smul]
    change -rightMul I a z = _
    rw [hra]
    rfl
  mul_mem' := by
    intro a b ha hb z hz
    have h := hb _ (ha z hz)
    change MulOpposite.op (a * b) • z ∈ _
    rw [MulOpposite.op_mul, mul_smul]
    exact h

/-- **`qA_{≥0} = Q`.**  `qA_{≥0}` is stable under `C` and `p`, which generate `A`. -/
theorem step_4_3_classSet_eq_univ (C : Subring A) (p : A)
    (hC : ∀ c ∈ C, ∀ z ∈ classSet I R, rightMul I c z ∈ classSet I R)
    (hp : ∀ z ∈ classSet I R, rightMul I p z ∈ classSet I R)
    (hgenerate : Subring.closure ((C : Set A) ∪ {p}) = ⊤) :
    classSet I R = Set.univ := by
  have htop : classSetStabilizer I R = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    apply Subring.closure_le.2
    rintro a (ha | ha)
    · exact hC a ha
    · rw [Set.mem_singleton_iff.mp ha]
      exact hp
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I z
  have ha : a ∈ classSetStabilizer I R := htop ▸ Subring.mem_top a
  have h := ha (qmk I 1) ⟨1, R.one_mem, rfl⟩
  rwa [← qmk_right_mul, one_mul] at h

/-- Proposition 4.3 for a ring with a right ideal, assembled from the
paragraphs: equation (normal-surj) with `qA_{≥0} = Q` reads `Q = Qx₁`. -/
theorem proposition_4_3_of (C : Subring A) (x p u₀ : A)
    (hx : x ∈ R) (hE : x * p ∈ R) (hC : C ≤ R)
    (hnormal : ∀ r ∈ R, ∃ r' ∈ R, x * r = r' * x)
    (hu₀ : u₀ ∈ R) (hres : 1 + u₀ * x ∈ I)
    (hgenerate : Subring.closure ((C : Set A) ∪ {p}) = ⊤) :
    Function.Surjective (rightMul I x) := by
  have hsurj := step_4_3_normal_surj x u₀ hx hu₀ hres hnormal
  have huniv := step_4_3_classSet_eq_univ C p
    (step_4_3_stable_coefficients C hC) (step_4_3_stable_momentum x p hE hsurj) hgenerate
  intro z
  have hz : z ∈ rightMul I x '' classSet I R := by
    rw [← hsurj, huniv]
    trivial
  obtain ⟨w, -, hw⟩ := hz
  exact ⟨w, hw⟩

end Generic

section Presented

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- `C = A_{n-1}(k)[x₁]`. -/
abbrev transverseCoordinateAlgebra : Subring (PresentedWeyl k (n + 1)) :=
  Subring.closure ((transverse k n : Set (PresentedWeyl k (n + 1))) ∪ {presentedCoordinate k n})

/-- `C ⊆ A_{≥0}`: no element of `C` contains `p`. -/
theorem transverseCoordinateAlgebra_le :
    transverseCoordinateAlgebra k n ≤ presentedNonnegativePart k n := by
  have hweyl := (Stafford38.Paper.Section2.convention_2_2_relations k n).1
  apply Subring.closure_le.2
  rintro a (ha | ha)
  · exact eulerSubring_le_nonnegativePart _ _ _ hweyl
      (fun c hc => (Stafford38.Paper.Section2.convention_2_2_relations k n).2.2 c hc)
      (coefficient_mem_eulerSubring _ _ _ ⟨a, ha⟩)
  · rw [Set.mem_singleton_iff.mp ha]
    exact coordinate_mem_nonnegativePart hweyl

/-- `C` and `p` together generate `A_n`. -/
theorem closure_transverseCoordinateAlgebra_momentum [Algebra ℚ k] :
    Subring.closure ((transverseCoordinateAlgebra k n : Set (PresentedWeyl k (n + 1))) ∪
      {presentedMomentum k n}) = ⊤ := by
  apply top_unique
  intro z _
  have hz : presentedToIterated k (n + 1) z ∈
      (⊤ : Subring (PairStage (B := IteratedPairStage k n))) := trivial
  let := Stafford38.WeylEulerRemainder.iteratedRatAlgebra k n
  rw [← closure_pairOldSubring_union_coordinate_momentum_eq_top] at hz
  have hle : Subring.closure (((pairOldSubring (IteratedPairStage k n) :
        Subring (PairStage (B := IteratedPairStage k n))) : Set _) ∪
        {pairCoordinate, pairMomentum}) ≤
      (Subring.closure ((transverseCoordinateAlgebra k n : Set (PresentedWeyl k (n + 1))) ∪
        {presentedMomentum k n})).comap (fromIterated k n) := by
    apply Subring.closure_le.2
    rintro a (⟨b, rfl⟩ | ha)
    · exact Subring.subset_closure (Or.inl (Subring.subset_closure
        (Or.inl (fromIterated_coefficient_mem_transverse k n b))))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · rw [SetLike.mem_coe, Subring.mem_comap, fromIterated_coordinate]
        exact Subring.subset_closure (Or.inl (Subring.subset_closure (Or.inr rfl)))
      · rw [SetLike.mem_coe, Subring.mem_comap, fromIterated_momentum]
        exact Subring.subset_closure (Or.inr rfl)
  have h : fromIterated k n (presentedToIterated k (n + 1) z) ∈
      Subring.closure ((transverseCoordinateAlgebra k n : Set (PresentedWeyl k (n + 1))) ∪
        {presentedMomentum k n}) := Subring.mem_comap.mp (hle hz)
  rwa [fromIterated_toIterated] at h

variable {k n}

/-- **Proposition 4.3.** For `d̃` in the form (3.1), right multiplication by `x₁`
on `Q = A_n/𝓘` (Equation (3.2)) is surjective, i.e. `Q = Qx₁`. -/
theorem proposition_4_3 [Algebra ℚ k] {N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hform : Stafford38.Paper.Section3.IsMonicNormalForm k N d) :
    Function.Surjective
      (rightMul (Stafford38.Paper.Section3.idealI k N d) (presentedCoordinate k n)) := by
  obtain ⟨u₀, hu₀, hres⟩ := lemma_4_2 hform
  exact proposition_4_3_of (transverseCoordinateAlgebra k n)
    (presentedCoordinate k n) (presentedMomentum k n) u₀
    (coordinate_mem_nonnegativePart (Stafford38.Paper.Section2.convention_2_2_relations k n).1)
    (euler_mem_nonnegativePart _ _)
    (transverseCoordinateAlgebra_le k n)
    (presented_coordinate_normal k n)
    hu₀ hres (closure_transverseCoordinateAlgebra_momentum k n)

end Presented

#print axioms step_4_3_q_mem
#print axioms step_4_3_normal_surj
#print axioms step_4_3_stable_momentum
#print axioms step_4_3_stable_coefficients
#print axioms step_4_3_classSet_eq_univ
#print axioms proposition_4_3_of
#print axioms proposition_4_3

end

end Stafford38.Paper.Section4
