module

public import Stafford38.Paper.Section6.Avoidance
public import Stafford38.Weyl.PaperQuotientDescent
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

@[expose] public section

/-!
# Lemma 6.2: base change of `Q` to a field extension `K/k`

`A_n(k) → A_n(K)` is `presentedWeylScalarExtension` (written `ι`) and
`k[x, ξ] → K[x, ξ]` is `symbolScalarExtension` (written `σ`, the coefficient
map `MvPolynomial.map (algebraMap k K)`).  For `d̃ ∈ A_n(k)`,
`𝓘_K = ι(d̃)A_n(K) + x₁^N ι(d̃)A_n(K)` is `Section3.idealI K N (ι d̃)` and
`Q_K = A_n(K)/𝓘_K` is `Section3.Q K N (ι d̃)`.

The proof follows the printed order: `𝓘_K = 𝓘 ⊗_k K` (`step_6_2_ideal`) gives
`θ : K ⊗_k Q ≅ Q_K` (`theta62`) and `Q_{K,i} = Q_i ⊗_k K` (`step_6_2_pieces`);
flatness gives `Q_{K,i}/Q_{K,i-1} = (Q_i/Q_{i-1}) ⊗_k K`
(`step_6_2_graded_pieces`), and summing over `i`, `gr Q_K = gr Q ⊗_k K`
(`step_6_2_sum`, `step_6_2_graded`), compatibly with `k[x,ξ] → K[x,ξ]`
(`step_6_2_graded_one_tmul_smul`); then the annihilator commutes with the base
change (`step_6_2_annihilator`), and `Q = 0 ⇔ Q_K = 0` (`step_6_2_vanishing`).
-/

namespace Stafford38.Paper.Section6

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicInitialIdeal
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.Weyl.PresentedScalarExtension
open Stafford38.Weyl.FilteredScalarLifting
open Stafford38.Paper.Section2
open Stafford38.Paper.Section3
open scoped TensorProduct
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol

noncomputable section

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- `ι(d̃) ∈ A_n(K)`, the image of `d̃` under the coefficient extension. -/
abbrev dtK (K : Type v) [Field K] [Algebra k K] {n : ℕ} (dt : PresentedWeyl k (n + 1)) :
    PresentedWeyl K (n + 1) :=
  presentedWeylScalarExtension (k := k) (K := K) (n + 1) dt

/-- `σ : k[x, ξ] → K[x, ξ]`. -/
abbrev σ (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] (n : ℕ) :
    SymbolRing k (n + 1) →+* SymbolRing K (n + 1) :=
  (symbolScalarExtension (k := k) (K := K) (n + 1)).toRingHom

/-- Proof, first sentence: by the PBW basis, `𝓘_K = 𝓘 ⊗_k K` inside
`A_n(K) = A_n(k) ⊗_k K`. -/
theorem step_6_2_ideal {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    Submodule.map (pbwTensorEquiv (k := k) (K := K) (n + 1)).toLinearMap
        ((rightIdealKSubmodule k (idealI k N dt)).baseChange K) =
      rightIdealKSubmodule K (idealI K N (dtK K dt)) :=
  pbwTensorEquiv_map_canonicalRightIdeal n N dt

/-- Consequently `Q ⊗_k K ≅ Q_K`: tensoring `0 → 𝓘 → A_n(k) → Q → 0` with
`K` and identifying the image of `𝓘 ⊗_k K` with `𝓘_K` by `step_6_2_ideal`. -/
def step_6_2_quotient {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    Q k N dt ⊗[k] K ≃ₗ[k] Q K N (dtK K dt) := by
  let J := rightIdealKSubmodule k (idealI k N dt)
  let eK := pbwTensorEquiv (k := k) (K := K) (n + 1)
  let JK := rightIdealKSubmodule K (idealI K N (dtK K dt))
  let f := (TensorProduct.comm k (PresentedWeyl k (n + 1)) K).trans
    (LinearEquiv.restrictScalars k eK)
  let D := LinearMap.range (TensorProduct.map J.subtype (LinearMap.id : K →ₗ[k] K))
  have hden : Submodule.map f.toLinearMap D = JK.restrictScalars k := by
    have hf : f.toLinearMap =
        (LinearEquiv.restrictScalars k eK).toLinearMap.comp
          (TensorProduct.comm k (PresentedWeyl k (n + 1)) K).toLinearMap := by
      ext z
      rfl
    rw [hf, Submodule.map_comp,
      Stafford38.PaperQuotientDescent.comm_map_tensorSubmodule_range]
    calc
      Submodule.map (LinearEquiv.restrictScalars k eK).toLinearMap
        (Submodule.restrictScalars k (J.baseChange K)) =
        Submodule.restrictScalars k (Submodule.map eK.toLinearMap (J.baseChange K)) :=
          (Submodule.restrictScalars_map eK.toLinearMap (J.baseChange K)).symm
      _ = Submodule.restrictScalars k JK := by rw [step_6_2_ideal]
  exact (TensorProduct.congr (filteredRightQuotientEquivRightQuotient k (idealI k N dt)).symm
      (LinearEquiv.refl k K)).trans
    (((TensorProduct.quotientTensorEquiv K J).trans
      (Submodule.Quotient.equiv D (JK.restrictScalars k) f hden)).trans
    ((Submodule.Quotient.restrictScalarsEquiv k JK).trans
      (LinearEquiv.restrictScalars k
        (filteredRightQuotientEquivRightQuotient K (idealI K N (dtK K dt))))))

variable {n N : ℕ}

set_option maxRecDepth 20000 in
theorem step_6_2_quotient_mk (dt : PresentedWeyl k (n + 1)) (a : PresentedWeyl k (n + 1)) (c : K) :
    step_6_2_quotient (K := K) (N := N) dt
      ((Submodule.Quotient.mk a : Q k N dt) ⊗ₜ[k] c) =
      Submodule.Quotient.mk (c • presentedWeylScalarExtension (k := k) (K := K) (n + 1) a) := by
  have h1 : pbwTensorEquiv (k := k) (K := K) (n + 1) (c ⊗ₜ[k] a) =
      c • presentedWeylScalarExtension (k := k) (K := K) (n + 1) a := by
    rw [← pbwTensorEquiv_tmul_one, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [← h1]
  rfl

/-- `θ : K ⊗_k Q ≅ Q_K`, `c ⊗ [a] ↦ c [a]`, `K`-linear. -/
def theta62 (dt : PresentedWeyl k (n + 1)) : K ⊗[k] Q k N dt ≃ₗ[K] Q K N (dtK K dt) :=
  { (TensorProduct.comm k K (Q k N dt)).trans (step_6_2_quotient (K := K) (N := N) dt) with
    map_smul' := fun c t => by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c' q =>
          obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
            LinearEquiv.trans_apply, TensorProduct.smul_tmul', TensorProduct.comm_tmul,
            smul_eq_mul, RingHom.id_apply]
          rw [step_6_2_quotient_mk, step_6_2_quotient_mk, mul_smul]
          rfl
      | add x y hx hy =>
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
            smul_add, map_add, RingHom.id_apply] at hx hy ⊢
          rw [hx, hy] }

set_option maxRecDepth 20000 in
theorem theta62_tmul (dt : PresentedWeyl k (n + 1)) (c : K) (a : PresentedWeyl k (n + 1)) :
    theta62 (N := N) dt (c ⊗ₜ[k] (Submodule.Quotient.mk a : Q k N dt)) =
      c • Submodule.Quotient.mk (presentedWeylScalarExtension (k := k) (K := K) (n + 1) a) :=
  (step_6_2_quotient_mk dt a c).trans rfl

/-- `Q_i = qF_i ⊆ Q`. -/
abbrev Qpiece (k : Type u) [Field k] {n : ℕ} (N : ℕ) (dt : PresentedWeyl k (n + 1)) (i : ℕ) :
    Submodule k (Q k N dt) :=
  cyclicFiltration (orderFiltration k (n + 1)) (qClass k (idealI k N dt)) i

/-- **Lemma 6.2, proof, first sentence.** By the PBW basis
`F_iA_n(K) = F_iA_n(k) ⊗_k K` and `𝓘_K = 𝓘 ⊗_k K`, so `Q_{K,i} = Q_i ⊗_k K`:
`θ` maps `K ⊗_k Q_i` onto `Q_{K,i} = qF_iA_n(K)`. -/
theorem step_6_2_pieces (dt : PresentedWeyl k (n + 1)) (i : ℕ) :
    ((Qpiece k N dt i).baseChange K).map (theta62 (N := N) dt).toLinearMap =
      Qpiece K N (dtK K dt) i := by
  set ι := presentedWeylScalarExtension (k := k) (K := K) (n + 1)
  set F := orderPiece k (n + 1) i
  have hF : orderPiece K (n + 1) i = Submodule.span K (ι '' F) := by
    rw [← pbwTensorEquiv_map_orderPiece (k := k) (K := K), Submodule.baseChange_eq_span,
      Submodule.map_span, Submodule.map_coe, ← Set.image_comp]
    congr 1
    ext z
    simp only [Set.mem_image, Function.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
      pbwTensorEquiv_tmul_one, SetLike.mem_coe]
    rfl
  have hR : Qpiece K N (dtK K dt) i = Submodule.span K
      ((fun a => (Submodule.Quotient.mk (ι a) : Q K N (dtK K dt))) '' F) := by
    change (orderPiece K (n + 1) i).map (orbitMap (qClass K (idealI K N (dtK K dt)))) = _
    rw [hF, Submodule.map_span, ← Set.image_comp]
    congr 1
    ext x
    simp only [Set.mem_image, Function.comp_apply, orbitMap_qClass]
  have hL : Qpiece k N dt i = Submodule.span k
      ((fun a => (Submodule.Quotient.mk a : Q k N dt)) '' F) := by
    calc Qpiece k N dt i = F.map (orbitMap (qClass k (idealI k N dt))) := rfl
      _ = (Submodule.span k (F : Set (PresentedWeyl k (n + 1)))).map
            (orbitMap (qClass k (idealI k N dt))) := by rw [Submodule.span_eq]
      _ = _ := by
        rw [Submodule.map_span]
        congr 1
        ext x
        simp only [Set.mem_image, orbitMap_qClass]
  rw [hR, hL, Submodule.baseChange_span, Submodule.map_span, ← Set.image_comp, ← Set.image_comp]
  congr 1
  ext x
  simp [theta62_tmul, ι]

section Flat

variable {X : Type*} [AddCommGroup X] [Module k X]

/-- `K ⊗_k M ≅ M ⊗ K ⊆ K ⊗_k X`: `K` is flat over `k`. -/
def baseChangeSubmoduleEquiv (M : Submodule k X) :
    K ⊗[k] M ≃ₗ[K] M.baseChange K :=
  LinearEquiv.ofInjective (M.subtype.baseChange K) (by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ M.injective_subtype)

/-- **Flatness of `K/k` on a pair `M' ⊆ M`.**  If `θ : K ⊗_k X ≅ Y` carries
`K ⊗_k M` onto `P` and `K ⊗_k M'` onto `P'`, then
`K ⊗_k (M/M') ≅ P/P'`. -/
def tensorPieceEquiv {Y : Type*} [AddCommGroup Y] [Module K Y] (θ : K ⊗[k] X ≃ₗ[K] Y)
    (M M' : Submodule k X) (h : M' ≤ M) (P P' : Submodule K Y)
    (hP : (M.baseChange K).map θ.toLinearMap = P)
    (hP' : (M'.baseChange K).map θ.toLinearMap = P') :
    K ⊗[k] (M ⧸ M'.comap M.subtype) ≃ₗ[K] (P ⧸ P'.comap P.subtype) :=
  let e : K ⊗[k] M ≃ₗ[K] P := (baseChangeSubmoduleEquiv M).trans
    ((θ.submoduleMap _).trans (LinearEquiv.ofEq _ _ hP))
  have he : ∀ t, (e t : Y) = θ (M.subtype.baseChange K t) := fun _ => rfl
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv K k K (M'.comap M.subtype)).trans
    (Submodule.Quotient.equiv _ _ e (by
      apply le_antisymm
      · rintro _ ⟨t, ⟨s, rfl⟩, rfl⟩
        rw [Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe, he, ← hP']
        refine ⟨_, ?_, rfl⟩
        induction s using TensorProduct.induction_on with
        | zero => simp
        | tmul c x => exact Submodule.tmul_mem_baseChange_of_mem c x.2
        | add a b ha hb =>
            rw [map_add, map_add]
            exact Submodule.add_mem _ ha hb
      · have hR : ∀ w ∈ M'.baseChange K, ∃ t ∈ LinearMap.range
            (TensorProduct.AlgebraTensorModule.lTensor K K
              ((M'.comap M.subtype).subtype.restrictScalars k)),
            M.subtype.baseChange K t = w := by
          intro w hw
          rw [Submodule.baseChange_eq_span] at hw
          induction hw using Submodule.span_induction with
          | mem x hx =>
              obtain ⟨m', hm', rfl⟩ := hx
              exact ⟨(1 : K) ⊗ₜ[k] (⟨m', h hm'⟩ : M),
                ⟨(1 : K) ⊗ₜ[k] ⟨⟨m', h hm'⟩, hm'⟩, rfl⟩, rfl⟩
          | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
          | add x y _ _ hx hy =>
              obtain ⟨tx, htx, rfl⟩ := hx
              obtain ⟨ty, hty, rfl⟩ := hy
              exact ⟨tx + ty, Submodule.add_mem _ htx hty, map_add _ _ _⟩
          | smul c x _ hx =>
              obtain ⟨tx, htx, rfl⟩ := hx
              exact ⟨c • tx, Submodule.smul_mem _ c htx, map_smul _ _ _⟩
        rintro z hz
        rw [Submodule.mem_comap, Submodule.coe_subtype, ← hP'] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        obtain ⟨t, ht, htw⟩ := hR w hw
        refine ⟨t, ht, Subtype.ext ?_⟩
        rw [LinearEquiv.coe_coe, he, htw]
        exact hwz))

end Flat

theorem lowerPiece_Qpiece_baseChange (dt : PresentedWeyl k (n + 1)) (i : ℕ) :
    ((lowerPiece (Qpiece k N dt) i).baseChange K).map (theta62 (N := N) dt).toLinearMap =
      lowerPiece (Qpiece K N (dtK K dt)) i := by
  cases i with
  | zero => simp [lowerPiece]
  | succ i => exact step_6_2_pieces dt i

/-- **Lemma 6.2, proof, second sentence.** As `K` is flat over `k`,
`Q_{K,i}/Q_{K,i-1} = (Q_i/Q_{i-1}) ⊗_k K`. -/
def step_6_2_graded_pieces (dt : PresentedWeyl k (n + 1)) (i : ℕ) :
    K ⊗[k] grPiece (Qpiece k N dt) i ≃ₗ[K] grPiece (Qpiece K N (dtK K dt)) i :=
  tensorPieceEquiv (theta62 (N := N) dt) (Qpiece k N dt i) (lowerPiece (Qpiece k N dt) i)
    (by
      cases i with
      | zero => exact bot_le
      | succ i => exact (cyclicFiltration_order_isCompatible k _).mono (Nat.le_succ i))
    _ _ (step_6_2_pieces dt i) (lowerPiece_Qpiece_baseChange dt i)

/-- Same sentence: summing over `i`, `gr Q_K = gr Q ⊗_k K` (Definition 2.3, `gr`). -/
def step_6_2_sum (dt : PresentedWeyl k (n + 1)) :
    K ⊗[k] gr (Qpiece k N dt) ≃ₗ[K] gr (Qpiece K N (dtK K dt)) :=
  (TensorProduct.directSumRight k K K (fun i => grPiece (Qpiece k N dt) i)).trans
    (DFinsupp.mapRange.linearEquiv fun i => step_6_2_graded_pieces dt i)

open Stafford38.CharacteristicAssociatedGradedModule in
/-- `gr Q_K ≅ K ⊗_k gr Q` (as `K`-modules), assembled from the pieces through
`grCyclicEquiv`. -/
def step_6_2_graded (dt : PresentedWeyl k (n + 1)) :
    K ⊗[k] grQ k N dt ≃ₗ[K] grQ K N (dtK K dt) :=
  (LinearEquiv.baseChange k K _ _ (grCyclicEquiv k (idealI k N dt))).trans
    ((step_6_2_sum dt).trans (grCyclicEquiv K (idealI K N (dtK K dt))).symm)

open Stafford38.CharacteristicAssociatedGradedModule in
theorem grCyclicEquiv_of {F : Type*} [Field F] {m : ℕ}
    (I : Stafford38.EulerSurjectivity.RightIdeal (PresentedWeyl F m))
    (j : ℕ) (y : orderPiece F m j) :
    grCyclicEquiv F I (orderAssociatedGradedOf F I j (orderPieceToQuotientGraded F I j y)) =
      DirectSum.lof F ℕ (grPiece (cyclicFiltration (orderFiltration F m) (qClass F I))) j
        (Submodule.Quotient.mk ⟨Submodule.Quotient.mk y.1, y.1, y.2, orbitMap_qClass F I y.1⟩) := by
  simp only [grCyclicEquiv, orderAssociatedGradedOf]
  erw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single]
  rfl

open Stafford38.CharacteristicAssociatedGradedModule in
set_option maxRecDepth 20000 in
theorem step_6_2_graded_pieces_mk (dt : PresentedWeyl k (n + 1)) (j : ℕ) (c : K)
    (y : orderPiece k (n + 1) j) :
    step_6_2_graded_pieces (N := N) dt j (c ⊗ₜ[k] Submodule.Quotient.mk
        ⟨Submodule.Quotient.mk y.1, y.1, y.2, orbitMap_qClass k _ y.1⟩) =
      c • Submodule.Quotient.mk ⟨Submodule.Quotient.mk
        (presentedWeylScalarExtension (k := k) (K := K) (n + 1) y.1),
          presentedWeylScalarExtension (k := k) (K := K) (n + 1) y.1,
          presentedWeylScalarExtension_mem_orderPiece (n + 1) j y.2,
          orbitMap_qClass K _ _⟩ := by
  rw [← Submodule.Quotient.mk_smul]
  change Submodule.Quotient.mk _ = _
  congr 1
  apply Subtype.ext
  change theta62 (N := N) dt (c ⊗ₜ[k] Submodule.Quotient.mk y.1) = _
  rw [theta62_tmul]
  rfl

open Stafford38.CharacteristicAssociatedGradedModule in
theorem step_6_2_graded_tmul_of (dt : PresentedWeyl k (n + 1)) (j : ℕ) (c : K)
    (y : orderPiece k (n + 1) j) :
    step_6_2_graded (N := N) dt (c ⊗ₜ[k] orderAssociatedGradedOf k (idealI k N dt) j
        (orderPieceToQuotientGraded k (idealI k N dt) j y)) =
      c • orderAssociatedGradedOf K (idealI K N (dtK K dt)) j
        (orderPieceToQuotientGraded K (idealI K N (dtK K dt)) j
          ⟨presentedWeylScalarExtension (k := k) (K := K) (n + 1) y,
            presentedWeylScalarExtension_mem_orderPiece (n + 1) j y.2⟩) := by
  simp only [step_6_2_graded, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, step_6_2_sum]
  rw [LinearEquiv.symm_apply_eq, map_smul, grCyclicEquiv_of, grCyclicEquiv_of,
    TensorProduct.directSumRight_tmul_lof]
  erw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single]
  rw [step_6_2_graded_pieces_mk, ← map_smul]
  rfl

open Stafford38.CharacteristicAssociatedGradedModule Stafford38.WeylAssociatedGraded in
/-- `gr Q ⊗_k K ≅ gr Q_K` is compatible with `k[x, ξ] → K[x, ξ]`:
`1 ⊗ f q̄ ↦ σ(f) q̄_K`. -/
theorem step_6_2_graded_one_tmul_smul (dt : PresentedWeyl k (n + 1)) (h : SymbolRing k (n + 1)) :
    step_6_2_graded (N := N) dt ((1 : K) ⊗ₜ[k] (h • qBar k (idealI k N dt))) =
      σ k K n h • qBar K (idealI K N (dtK K dt)) := by
  classical
  let _ := MvPolynomial.weightedGradedAlgebra k (@orderWeight (n + 1))
  let 𝒜 := MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight (n + 1))
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 h]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 h]
  rw [Finset.sum_smul, TensorProduct.tmul_sum, map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  obtain ⟨y, hy⟩ := principalComponentOnPiece_surjective k (@orderWeight (n + 1))
    (DirectSum.decompose 𝒜 h d)
  have hy' : ((DirectSum.decompose 𝒜 h d : SymbolRing k (n + 1))) =
      (principalComponentOnPiece k (@orderWeight (n + 1)) d y : SymbolRing k (n + 1)) :=
    (congrArg Subtype.val hy).symm
  rw [hy']
  have hσ := presentedWeylScalarExtension_principalComponent (k := k) (K := K) (n + 1)
    (@orderWeight (n + 1)) d (y : PresentedWeyl k (n + 1))
  change _ = (symbolScalarExtension (k := k) (K := K) (n + 1)
      (presentedPrincipalComponent k (@orderWeight (n + 1)) d y)) •
        qBar K (idealI K N (dtK K dt))
  rw [hσ]
  change step_6_2_graded dt (1 ⊗ₜ[k] (_ • orderAssociatedGradedOf k _ 0
      (orderPieceToQuotientGraded k _ 0 (orderPieceOne (n := n + 1) k)))) =
    _ • orderAssociatedGradedOf K _ 0
      (orderPieceToQuotientGraded K _ 0 (orderPieceOne (n := n + 1) K))
  rw [smul_orderAssociatedGradedOf_mk_eq_of_mul]
  erw [smul_orderAssociatedGradedOf_mk_eq_of_mul K (idealI K N (dtK K dt)) (orderPieceOne K)
    ⟨presentedWeylScalarExtension (k := k) (K := K) (n + 1) y,
      presentedWeylScalarExtension_mem_orderPiece (n + 1) d y.2⟩]
  rw [step_6_2_graded_tmul_of, one_smul]
  congr 3
  change presentedWeylScalarExtension (k := k) (K := K) (n + 1) (1 * y) = 1 * _
  rw [map_mul, map_one]

theorem smul_qBar_K_eq (dt : PresentedWeyl k (n + 1)) (c : K) (h : SymbolRing k (n + 1)) :
    step_6_2_graded (N := N) dt (c ⊗ₜ[k] (h • qBar k (idealI k N dt))) =
      (c • σ k K n h) • qBar K (idealI K N (dtK K dt)) := by
  rw [show c ⊗ₜ[k] (h • qBar k (idealI k N dt)) = c • ((1 : K) ⊗ₜ[k] (h • qBar k _)) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, step_6_2_graded_one_tmul_smul,
    smul_assoc]

/-- **Lemma 6.2, proof, third sentence.** `gr Q` is finitely generated (cyclic,
generated by `q̄`) over `k[x, ξ]`, and `k[x, ξ] → K[x, ξ] = K ⊗_k k[x, ξ]` is flat,
so the annihilator commutes with the base change (Stacks 07T8): through
`gr Q_K ≅ K ⊗_k gr Q`, `Ann_{K[x,ξ]} gr Q_K = (Ann_{k[x,ξ]} gr Q) K[x,ξ]`.  (For the
cyclic module the 07T8 argument is spelled out: write `g ∈ K[x, ξ]` as
`∑ b_λ σ(f_λ)` for a `k`-basis `b` of `K`.) -/
theorem step_6_2_annihilator (dt : PresentedWeyl k (n + 1)) :
    Module.annihilator (SymbolRing K (n + 1)) (grQ K N (dtK K dt)) =
      (Module.annihilator (SymbolRing k (n + 1)) (grQ k N dt)).map (σ k K n) := by
  classical
  let I := idealI k N dt
  let IK := idealI K N (dtK K dt)
  apply le_antisymm
  · intro g hg
    let b := Module.Basis.ofVectorSpace k K
    let t := (MvPolynomial.algebraTensorAlgEquiv k K).symm g
    let c := TensorProduct.equivFinsuppOfBasisLeft b t
    have ht : t = c.sum fun l f => b l ⊗ₜ[k] f := by
      rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply t]
      change (TensorProduct.equivFinsuppOfBasisLeft b).symm.toLinearMap c = _
      rw [TensorProduct.equivFinsuppOfBasisLeft_symm]
      simp [Finsupp.lsum_apply]
      rfl
    have hg' : g = c.sum fun l f => b l • σ k K n f := by
      rw [← (MvPolynomial.algebraTensorAlgEquiv k K).apply_symm_apply g]
      change MvPolynomial.algebraTensorAlgEquiv k K t = _
      rw [ht, Finsupp.sum, map_sum]
      simp [Finsupp.sum, MvPolynomial.algebraTensorAlgEquiv_tmul]
    have hzero : step_6_2_graded (K := K) (N := N) dt (c.sum fun l f => b l ⊗ₜ[k] (f • qBar k I)) = 0 := by
      rw [Finsupp.sum, map_sum,
        Finset.sum_congr rfl fun l _ => smul_qBar_K_eq (N := N) dt (b l) (c l),
        ← Finset.sum_smul]
      have := Module.mem_annihilator.mp hg (qBar K IK)
      rw [hg', Finsupp.sum] at this
      exact this
    rw [← map_zero (step_6_2_graded (K := K) (N := N) dt)] at hzero
    have hc := (step_6_2_graded (K := K) (N := N) dt).injective hzero
    have hmap : (c.mapRange (fun f => f • qBar k I) (zero_smul _ _)) = 0 := by
      apply TensorProduct.sum_tmul_basis_left_eq_zero b
      rw [Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
      exact hc
    have hann : ∀ l, c l ∈ Module.annihilator (SymbolRing k (n + 1)) (grQ k N dt) := by
      intro l
      have hl := congrArg (· l) hmap
      simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at hl
      rw [Module.mem_annihilator]
      intro m
      obtain ⟨f, rfl⟩ := grCyclic_generated k I m
      rw [smul_comm, hl, smul_zero]
    rw [hg', Finsupp.sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hann l))
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro y
    obtain ⟨t, rfl⟩ := (step_6_2_graded (K := K) (N := N) dt).surjective y
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]
    | tmul c m =>
        obtain ⟨h, rfl⟩ := grCyclic_generated k I m
        rw [smul_qBar_K_eq, smul_smul, mul_comm, ← smul_smul,
          ← step_6_2_graded_one_tmul_smul, Module.mem_annihilator.mp hf, TensorProduct.tmul_zero,
          map_zero, smul_zero]
    | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

/-- `Q = 0 ⇔ Q_K = 0`: `Q ⊗_k K = 0` implies `Q = 0` because `K` is a nonzero
free (so faithfully flat) `k`-module. -/
theorem step_6_2_vanishing {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    Subsingleton (Q k N dt) ↔ Subsingleton (Q K N (dtK K dt)) := by
  constructor
  · intro h
    have : Subsingleton (Q k N dt ⊗[k] K) := inferInstance
    exact (step_6_2_quotient (K := K) dt).toEquiv.symm.subsingleton
  · intro h
    have : Subsingleton (Q k N dt ⊗[k] K) := (step_6_2_quotient (K := K) dt).toEquiv.subsingleton
    exact Module.FaithfullyFlat.rTensor_reflects_triviality k K (Q k N dt)

/-- `Char(Q_K)` is the preimage of `Char(Q)` under
`Spec K[x,ξ] → Spec k[x,ξ]`. -/
theorem step_6_2_char {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    Section2.Char K (idealI K N (dtK K dt)) =
      PrimeSpectrum.comap (σ k K n) ⁻¹' Section2.Char k (idealI k N dt) := by
  rw [Section2.Char_eq, Section2.Char_eq, V, V, PrimeSpectrum.preimage_comap_zeroLocus,
    step_6_2_annihilator, Ideal.map, PrimeSpectrum.zeroLocus_span]

/-- **Lemma 6.2.** Let `K/k` be a field extension, `𝓘_K = d̃A_n(K) + x₁^N d̃A_n(K)`
and `Q_K = Q ⊗_k K = A_n(K)/𝓘_K` with the order filtration
`Q_{K,i} = qF_iA_n(K)`.  Then `gr Q_K ≅ gr Q ⊗_k K` (as `K`-modules; Lean writes the factor `K` on
the left, `K ⊗_k gr Q`),
`Ann_{K[x,ξ]} gr Q_K = (Ann_{k[x,ξ]} gr Q) K[x,ξ]`, and `Q = 0 ⇔ Q_K = 0`.
In particular, `Char(Q_K)` is the preimage of `Char(Q)` under
`Spec K[x,ξ] → Spec k[x,ξ]`. -/
theorem lemma_6_2 {n N : ℕ} (dt : PresentedWeyl k (n + 1)) :
    Nonempty (grQ K N (dtK K dt) ≃ₗ[K] K ⊗[k] grQ k N dt) ∧
      Module.annihilator (SymbolRing K (n + 1)) (grQ K N (dtK K dt)) =
        (Module.annihilator (SymbolRing k (n + 1)) (grQ k N dt)).map (σ k K n) ∧
      (Subsingleton (Q k N dt) ↔ Subsingleton (Q K N (dtK K dt))) ∧
      Section2.Char K (idealI K N (dtK K dt)) =
        PrimeSpectrum.comap (σ k K n) ⁻¹' Section2.Char k (idealI k N dt) :=
  ⟨⟨(step_6_2_graded (K := K) dt).symm⟩,
    step_6_2_annihilator dt, step_6_2_vanishing dt, step_6_2_char dt⟩

#print axioms step_6_2_ideal
#print axioms step_6_2_quotient
#print axioms step_6_2_annihilator
#print axioms step_6_2_quotient_mk
#print axioms step_6_2_pieces
#print axioms tensorPieceEquiv
#print axioms step_6_2_graded_pieces
#print axioms step_6_2_sum
#print axioms step_6_2_graded
#print axioms step_6_2_graded_tmul_of
#print axioms step_6_2_graded_one_tmul_smul
#print axioms step_6_2_vanishing
#print axioms step_6_2_char
#print axioms lemma_6_2

end

end Stafford38.Paper.Section6
