module

public import Stafford38.Paper.Section5
public import Stafford38.Paper.Section5.Definitions
public import Stafford38.Paper.Section5.JacobianConverse
public import Stafford38.Geometry.GenericPointKaehlerConormal
public import Stafford38.Geometry.ExactDivisorialVisibleFrameExistence

@[expose] public section

/-!
# Definitions 5.1–5.5 of the paper and the printed Theorem 5.7

The paper defines the smooth locus `Y_sm` of an irreducible closed `Y = V(𝔭)` by
the Jacobian (Definition 5.4(b)): `y ∈ Y_sm` iff the Jacobian matrix of
generators of `𝔭` has rank `n - dim Y` at `y`, with `dim Y` the Krull dimension
of `R = K[x]/𝔭`.  Theorems 5.7 and 5.8 are stated in Lean with
`SmoothAffinePoint`, Mathlib's smooth locus of `R`.  `definition_5_4_b_iff`
proves that the two loci coincide (the Jacobian criterion).

* `y` smooth ⇒ Jacobian rank `n - dim Y` (`definition_5_4_b`): the stalk
  `(Ω_{R/K})_𝔪` is free; its dual basis gives derivations `R → L` for every field
  `L` over `R_𝔪`, whose coordinate vectors are a basis of the Zariski tangent space
  over `L`.  Taking `L = K` (the point `y`) and `L = F = Frac R` (the generic point,
  Lemma 5.12(a)) gives `dim T_y Y = trdeg_K F = dim Y`.
* Jacobian rank `n - dim Y` ⇒ `y` smooth (`smoothAffinePoint_of_jacobian` in
  `Stafford38.Paper.Section5.JacobianConverse`): equations `f_1, …, f_c ∈ 𝔭` with
  independent differentials generate `𝔭` near `y`, and Mathlib's local Jacobian
  criterion applies.
* `dim Y = trdeg_K F` is `Stafford38.Paper.Support.ringKrullDim_eq_trdeg`.

Hence the printed conormal cone `N(Y)` is the Lean one (`conormalCone_paper_eq`),
the printed `Dir(Y)` is the Lean direction closure (`definition_5_5`), and
`theorem_5_7_i_printed`, `theorem_5_7_ii_printed` are Theorem 5.7 for them.

The last section binds the printed Definitions 5.1–5.3 to the Mathlib notions
where the wording differs.
-/

namespace Stafford38.Paper.Section5

open MvPolynomial
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry
open Stafford38.Geometry.GenericPointKaehlerConormal (quotientDerivation quotientDerivation_mk
  mkDerivation_eq_sum_pderiv)

noncomputable section

universe u

section Tangent

variable {k : Type u} [Field k] {n : ℕ} {I : Ideal (MvPolynomial (Fin n) k)}
  {L : Type*} [Field L] [Algebra k L] [Algebra (MvPolynomial (Fin n) k ⧸ I) L]
  [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) L]

/-- Chain rule: a derivation `D : K[x]/I → L` satisfies
`D(f̄) = Σ_i ∂_i f(x̄) · D(x̄_i)`. -/
theorem derivation_quotient_mk_eq_sum
    (D : Derivation k (MvPolynomial (Fin n) k ⧸ I) L) (f : MvPolynomial (Fin n) k) :
    D (Ideal.Quotient.mk I f) = ∑ i, MvPolynomial.eval₂ (algebraMap k L) (GenericPointKaehlerConormal.genericPoint I L)
      (MvPolynomial.pderiv i f) * D (Ideal.Quotient.mk I (X i)) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    have : Ideal.Quotient.mk I (C a) = algebraMap k (MvPolynomial (Fin n) k ⧸ I) a := rfl
    rw [this, Derivation.map_algebraMap]
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, MvPolynomial.eval₂_add, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, Derivation.leibniz, hp, Algebra.smul_def, Algebra.smul_def,
      algebraMap_quotient_mk_eq_eval₂, algebraMap_quotient_mk_eq_eval₂]
    have h2 : ∀ i, MvPolynomial.eval₂ (algebraMap k L) (GenericPointKaehlerConormal.genericPoint I L)
        (MvPolynomial.pderiv i (p * X j)) * D (Ideal.Quotient.mk I (X i)) =
        (if j = i then MvPolynomial.eval₂ (algebraMap k L) (GenericPointKaehlerConormal.genericPoint I L) p *
          D (Ideal.Quotient.mk I (X i)) else 0) +
        MvPolynomial.eval₂ (algebraMap k L) (GenericPointKaehlerConormal.genericPoint I L) (X j) *
          (MvPolynomial.eval₂ (algebraMap k L) (GenericPointKaehlerConormal.genericPoint I L) (MvPolynomial.pderiv i p) *
            D (Ideal.Quotient.mk I (X i))) := by
      intro i
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, MvPolynomial.eval₂_add,
        MvPolynomial.eval₂_mul, Pi.single_apply]
      split_ifs with h
      · subst h; simp; ring
      · simp; ring
    simp only [h2, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]

/-- The coordinates `(D x̄_i)_i` of a derivation `D : K[x]/I → L` form a tangent
vector at the point `x̄ ∈ L^n`. -/
theorem derivation_coordinates_mem_zariskiTangentSpace
    (D : Derivation k (MvPolynomial (Fin n) k ⧸ I) L) :
    (fun i ↦ D (Ideal.Quotient.mk I (X i))) ∈
      zariskiTangentSpace (GenericPointKaehlerConormal.genericPoint I L) (I.map (MvPolynomial.map (algebraMap k L))) := by
  apply mem_zariskiTangentSpace_map_of_forall_mem
  · intro g hg
    exact eval₂_genericPoint_eq_zero hg
  · intro g hg
    have h := derivation_quotient_mk_eq_sum D g
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 hg, map_zero] at h
    exact h.symm

/-- Conversely every tangent vector at `x̄ ∈ L^n` is `(D x̄_i)_i` for a derivation
`D : K[x]/I → L`. -/
theorem exists_derivation_of_mem_zariskiTangentSpace (w : Fin n → L)
    (hw : w ∈ zariskiTangentSpace (GenericPointKaehlerConormal.genericPoint I L)
      (I.map (MvPolynomial.map (algebraMap k L)))) :
    ∃ D : Derivation k (MvPolynomial (Fin n) k ⧸ I) L,
      ∀ i, D (Ideal.Quotient.mk I (X i)) = w i := by
  classical
  set A := MvPolynomial (Fin n) k ⧸ I
  set y := GenericPointKaehlerConormal.genericPoint I L
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator] at hw
  have htan : ∀ f ∈ I.map (MvPolynomial.map (algebraMap k L)),
      ∑ i, differentialAt y f i * w i = 0 := by
    intro f hf
    simpa using hw (differentialCovector y f) (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)
  let _ : Algebra (MvPolynomial (Fin n) k) L :=
    ((algebraMap A L).comp (algebraMap (MvPolynomial (Fin n) k) A)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) k) A L := by
    refine ⟨fun p a x ↦ ?_⟩
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Ideal.Quotient.mk_eq_mk,
      smul_eq_mul, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      mul_assoc]
    rfl
  have : IsScalarTower k (MvPolynomial (Fin n) k) L :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap k L a =
        algebraMap A L (algebraMap (MvPolynomial (Fin n) k) A (algebraMap k _ a))
      rw [← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) A,
        ← IsScalarTower.algebraMap_apply k A L]
  have halg : ∀ p : MvPolynomial (Fin n) k,
      algebraMap (MvPolynomial (Fin n) k) L p = aeval y p := by
    intro p
    have : (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) L) = aeval y := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [IsScalarTower.coe_toAlgHom', aeval_X]
      rfl
    exact AlgHom.congr_fun this p
  let DP : Derivation k (MvPolynomial (Fin n) k) L := mkDerivation k w
  have hDP : ∀ f, DP f = ∑ i, aeval y (pderiv i f) * w i :=
    mkDerivation_eq_sum_pderiv y w halg
  have hDPI : ∀ f ∈ I, DP f = 0 := by
    intro f hf
    rw [hDP]
    have := htan _ (Ideal.mem_map_of_mem _ hf)
    convert this using 2 with i
    rw [differentialAt, pderiv_map, eval_map, aeval_def]
  refine ⟨quotientDerivation DP hDPI, fun i ↦ ?_⟩
  rw [quotientDerivation_mk]
  exact mkDerivation_X k w i

end Tangent

section Stalk

variable {k : Type u} [Field k] {n : ℕ} {I : Ideal (MvPolynomial (Fin n) k)}
  (𝔪 : Ideal (MvPolynomial (Fin n) k ⧸ I)) [𝔪.IsPrime]
  {L : Type*} [Field L] [Algebra k L] [Algebra (MvPolynomial (Fin n) k ⧸ I) L]
  [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) L]
  [Algebra (Localization.AtPrime 𝔪) L]
  [IsScalarTower (MvPolynomial (Fin n) k ⧸ I) (Localization.AtPrime 𝔪) L]

/-- If `(Ω_{R/K})_𝔪` is free over `R_𝔪`, then for every field `L` over `R_𝔪` the
Zariski tangent space at the `L`-point `x̄` has dimension `rank (Ω_{R/K})_𝔪`.
A basis of the dual of `(Ω_{R/K})_𝔪` gives derivations `D_j : R → L`; their
coordinate vectors `(D_j x̄_i)_i` are a basis of the tangent space. -/
theorem finrank_zariskiTangentSpace_eq_finrank_localizedKaehler
    [Module.Free (Localization.AtPrime 𝔪)
      (LocalizedModule 𝔪.primeCompl Ω[(MvPolynomial (Fin n) k ⧸ I)⁄k])]
    [Module.Finite (Localization.AtPrime 𝔪)
      (LocalizedModule 𝔪.primeCompl Ω[(MvPolynomial (Fin n) k ⧸ I)⁄k])] :
    Module.finrank L (zariskiTangentSpace (GenericPointKaehlerConormal.genericPoint I L)
        (I.map (MvPolynomial.map (algebraMap k L)))) =
      Module.finrank (Localization.AtPrime 𝔪)
        (LocalizedModule 𝔪.primeCompl Ω[(MvPolynomial (Fin n) k ⧸ I)⁄k]) := by
  classical
  set A := MvPolynomial (Fin n) k ⧸ I
  set R := Localization.AtPrime 𝔪
  set M := LocalizedModule 𝔪.primeCompl Ω[A⁄k]
  set T := zariskiTangentSpace (GenericPointKaehlerConormal.genericPoint I L) (I.map (MvPolynomial.map (algebraMap k L)))
  let b := Module.Free.chooseBasis R M
  let lam : Module.Free.ChooseBasisIndex R M → (M →ₗ[R] L) :=
    fun j ↦ (Algebra.linearMap R L).comp (b.coord j)
  let mkM : Ω[A⁄k] →ₗ[A] M := LocalizedModule.mkLinearMap 𝔪.primeCompl Ω[A⁄k]
  let Dj : Module.Free.ChooseBasisIndex R M → Derivation k A L :=
    fun j ↦ (((lam j).restrictScalars A).comp mkM).compDer (KaehlerDifferential.D k A)
  let v : Module.Free.ChooseBasisIndex R M → Fin n → L :=
    fun j i ↦ Dj j (Ideal.Quotient.mk I (X i))
  have hv : ∀ j i, v j i = algebraMap R L (b.coord j (mkM (KaehlerDifferential.D k A
      (Ideal.Quotient.mk I (X i))))) := fun _ _ ↦ rfl
  -- Elements of `𝔪ᶜ` act invertibly on `L`.
  have hunit : ∀ s : 𝔪.primeCompl, IsUnit (algebraMap A (Module.End A L) s) := by
    intro s
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap A L s) := by
      rw [IsScalarTower.algebraMap_apply A R L]
      exact (IsLocalization.map_units R s).map _
    have hfun : ⇑(algebraMap A (Module.End A L) s) = fun x ↦ algebraMap A L s * x :=
      funext fun x ↦ Algebra.smul_def (s : A) x
    rw [hfun]
    exact ⟨hu.mul_right_injective, fun x ↦ ⟨(algebraMap A L s)⁻¹ * x, by
      simp only; rw [← mul_assoc, mul_inv_cancel₀ hu.ne_zero, one_mul]⟩⟩
  have hvT : ∀ j, v j ∈ T := fun j ↦ derivation_coordinates_mem_zariskiTangentSpace (Dj j)
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro t ht j
    let lt : M →ₗ[R] L := ∑ j', (LinearMap.mulLeft R (t j')).comp (lam j')
    have hlt : ∀ x, lt x = ∑ j', t j' * algebraMap R L (b.coord j' x) := by
      intro x
      simp [lt, lam]
    let Dt : Derivation k A L :=
      ((lt.restrictScalars A).comp mkM).compDer (KaehlerDifferential.D k A)
    have hDtX : ∀ i, Dt (Ideal.Quotient.mk I (X i)) = 0 := by
      intro i
      have h := congrFun ht i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hv] at h
      change lt (mkM (KaehlerDifferential.D k A (Ideal.Quotient.mk I (X i)))) = 0
      rw [hlt]
      exact h
    have hDt0 : Dt = 0 := by
      ext a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [derivation_quotient_mk_eq_sum Dt f]
      simp [hDtX]
    have hcomp : (lt.restrictScalars A).comp mkM = 0 := by
      apply Derivation.liftKaehlerDifferential_unique
      ext a
      change Dt a = 0
      rw [hDt0, Derivation.zero_apply]
    have hlt0 : lt.restrictScalars A = 0 :=
      IsLocalizedModule.ext 𝔪.primeCompl mkM hunit (by rw [hcomp, LinearMap.zero_comp])
    have h := LinearMap.congr_fun hlt0 (b j)
    rw [LinearMap.restrictScalars_apply, LinearMap.zero_apply, hlt] at h
    simpa [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] using h
  have hspan : T ≤ Submodule.span L (Set.range v) := by
    intro w hw
    obtain ⟨Dw, hDw⟩ := exists_derivation_of_mem_zariskiTangentSpace w hw
    let ψ : Ω[A⁄k] →ₗ[A] L := Dw.liftKaehlerDifferential
    let φ : M →ₗ[A] L := IsLocalizedModule.lift 𝔪.primeCompl mkM ψ hunit
    let Φ : M →ₗ[R] L := LinearMap.extendScalarsOfIsLocalization 𝔪.primeCompl R φ
    have hΦ : ∀ x, Φ x = ∑ j, Φ (b j) * algebraMap R L (b.coord j x) := by
      intro x
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smul, Algebra.smul_def, mul_comm, Module.Basis.coord_apply]
    have hw' : w = ∑ j, Φ (b j) • v j := by
      funext i
      have h1 : Φ (mkM (KaehlerDifferential.D k A (Ideal.Quotient.mk I (X i)))) = w i := by
        change φ (mkM _) = w i
        rw [IsLocalizedModule.lift_apply]
        change Dw.liftKaehlerDifferential (KaehlerDifferential.D k A _) = _
        rw [Derivation.liftKaehlerDifferential_comp_D, hDw]
      rw [← h1, hΦ]
      simp [Finset.sum_apply, hv]
    rw [hw']
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have heq : T = Submodule.span L (Set.range v) :=
    le_antisymm hspan (Submodule.span_le.2 (Set.range_subset_iff.2 hvT))
  have : StrongRankCondition R := commRing_strongRankCondition R
  rw [heq, finrank_span_eq_card hli, Module.finrank_eq_card_chooseBasisIndex]

end Stalk

section JacobianRank

variable {k : Type u} [Field k] {n : ℕ}

/-- `rank (df_y)_{f ∈ I} + dim T_y = n`: the Jacobian rank and the dimension of the
Zariski tangent space at `y` add up to `n`. -/
theorem finrank_differentialSpan_add_finrank_zariskiTangentSpace
    (I : Ideal (MvPolynomial (Fin n) k)) (y : Fin n → k) :
    Module.finrank k (Submodule.span k (Set.range fun f : I ↦ differentialAt y f.1)) +
      Module.finrank k (zariskiTangentSpace y I) = n := by
  have hspan : equationCovectorSpan y I =
      (Submodule.span k (Set.range fun f : I ↦ differentialAt y f.1)).map
        (coordinateCovectorLinear (k := k) (n := n)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hinj : Function.Injective (coordinateCovectorLinear (k := k) (n := n)) :=
    coordinateCovector_injective
  have h1 : Module.finrank k (equationCovectorSpan y I) =
      Module.finrank k (Submodule.span k (Set.range fun f : I ↦ differentialAt y f.1)) := by
    rw [hspan]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (equationCovectorSpan y I)
  have hn : Module.finrank k (AffineTangentVector k n) = n := Module.finrank_fin_fun k
  rw [h1, hn] at h
  exact h

/-- The rank of the Jacobian matrix `(∂_i g_j(y))_{j,i}` of a family of generators
`g_1, …, g_s` of `I` at a point `y ∈ V(I)` is `dim span {df_y : f ∈ I}`; in particular it
does not depend on the generators. -/
theorem jacobian_rank_eq_finrank_differentialSpan
    (I : Ideal (MvPolynomial (Fin n) k)) {s : ℕ} (g : Fin s → MvPolynomial (Fin n) k)
    (hg : Ideal.span (Set.range g) = I) {y : Fin n → k}
    (hy : y ∈ MvPolynomial.zeroLocus k I) :
    (Matrix.of fun j i ↦ differentialAt y (g j) i).rank =
      Module.finrank k (Submodule.span k (Set.range fun f : I ↦ differentialAt y f.1)) := by
  rw [Matrix.rank_eq_finrank_span_row]
  have hrows : Set.range (Matrix.of fun j i ↦ differentialAt y (g j) i).row =
      Set.range fun j ↦ differentialAt y (g j) := rfl
  suffices hs : Submodule.span k (Set.range fun j ↦ differentialAt y (g j)) =
      Submodule.span k (Set.range fun f : I ↦ differentialAt y f.1) by
    rw [hrows, hs]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : g j ∈ I := hg ▸ Ideal.subset_span ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨g j, hj⟩, rfl⟩
  · have key : ∀ f ∈ Ideal.span (Set.range g),
        differentialAt y f ∈ Submodule.span k (Set.range fun j ↦ differentialAt y (g j)) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨j, rfl⟩ := hf
        exact Submodule.subset_span ⟨j, rfl⟩
      | zero =>
        have : differentialAt y (0 : MvPolynomial (Fin n) k) = 0 := by
          funext i; simp [differentialAt]
        rw [this]
        exact Submodule.zero_mem _
      | add f₁ f₂ _ _ ih₁ ih₂ =>
        have : differentialAt y (f₁ + f₂) = differentialAt y f₁ + differentialAt y f₂ := by
          funext i; simp [differentialAt]
        rw [this]
        exact Submodule.add_mem _ ih₁ ih₂
      | smul a f hfs ih =>
        have hfy : MvPolynomial.eval y f = 0 := by
          simpa using (MvPolynomial.mem_zeroLocus_iff.1 hy) f (hg ▸ hfs)
        have : differentialAt y (a • f) = MvPolynomial.eval y a • differentialAt y f := by
          funext i
          simp [differentialAt, smul_eq_mul, hfy]
        rw [this]
        exact Submodule.smul_mem _ _ ih
    rw [Submodule.span_le]
    rintro _ ⟨⟨f, hf⟩, rfl⟩
    exact key f (hg ▸ hf)

end JacobianRank

section SmoothPoint

variable {k : Type u} [Field k] {n : ℕ}

/-- `dim Y` for `Y = V(𝔭)`: the transcendence degree over `K` of the function field
`F = Frac(K[x]/𝔭)`. -/
def componentDimension (P : PrimeSpectrum (MvPolynomial (Fin n) k)) : ℕ :=
  (Algebra.trdeg k (FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal))).toNat

/-- **Definition 5.4(b), the Jacobian smooth locus.** `y ∈ Y_sm` iff `y ∈ Y = V(𝔭)` and
the Jacobian matrix `(∂_i g_j(y))` of generators `g_1, …, g_s` of `I(Y) = 𝔭` has rank
`n - dim Y`, written `rank + dim Y = n` with `dim Y` the Krull dimension of `K[x]/𝔭`.
The rank does not depend on the generators
(`jacobian_rank_eq_finrank_differentialSpan`, `jacobianSmoothPoint_iff_span`). -/
def JacobianSmoothPoint (P : PrimeSpectrum (MvPolynomial (Fin n) k)) (y : Fin n → k) : Prop :=
  y ∈ MvPolynomial.zeroLocus k P.asIdeal ∧
    ∃ (s : ℕ) (g : Fin s → MvPolynomial (Fin n) k), Ideal.span (Set.range g) = P.asIdeal ∧
      ((Matrix.of fun j i ↦ differentialAt y (g j) i).rank : WithBot ℕ∞) +
        ringKrullDim (MvPolynomial (Fin n) k ⧸ P.asIdeal) = n

/-- The Jacobian rank is `dim span {df_y : f ∈ 𝔭}`, for any finite generating family
(one exists, `K[x]` being Noetherian). -/
theorem jacobianSmoothPoint_iff_span (P : PrimeSpectrum (MvPolynomial (Fin n) k))
    (y : Fin n → k) :
    JacobianSmoothPoint P y ↔ y ∈ MvPolynomial.zeroLocus k P.asIdeal ∧
      (Module.finrank k (Submodule.span k (Set.range fun f : P.asIdeal ↦ differentialAt y f.1)) :
        WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin n) k ⧸ P.asIdeal) = n := by
  constructor
  · rintro ⟨hy, s, g, hg, h⟩
    exact ⟨hy, by rwa [jacobian_rank_eq_finrank_differentialSpan P.asIdeal g hg hy] at h⟩
  · rintro ⟨hy, h⟩
    obtain ⟨s, g, hg⟩ :=
      Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian P.asIdeal)
    exact ⟨hy, s, g, hg, by rwa [jacobian_rank_eq_finrank_differentialSpan P.asIdeal g hg hy]⟩

/-- `dim Y` is both the Krull dimension of `K[x]/𝔭` and `trdeg_K Frac(K[x]/𝔭)`. -/
theorem componentDimension_eq_ringKrullDim (P : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ P.asIdeal) = componentDimension P := by
  rw [Stafford38.Paper.Support.ringKrullDim_eq_trdeg (K := k), componentDimension,
    Stafford38.Paper.Support.trdeg_fractionRing]

theorem componentDimension_le (P : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    componentDimension P ≤ n := by
  rw [componentDimension, Stafford38.Paper.Support.trdeg_fractionRing]
  have h := Stafford38.Paper.Support.trdeg_quotient_le (K := k) P.asIdeal
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fin,
    Cardinal.lift_natCast] at h
  have := Cardinal.toNat_le_toNat h Cardinal.natCast_lt_aleph0
  simpa using this

/-- **Definition 5.4(b), transcendence-degree form.** -/
theorem jacobianSmoothPoint_iff_trdeg (P : PrimeSpectrum (MvPolynomial (Fin n) k))
    (y : Fin n → k) :
    JacobianSmoothPoint P y ↔ y ∈ MvPolynomial.zeroLocus k P.asIdeal ∧
      Module.finrank k (Submodule.span k (Set.range fun f : P.asIdeal ↦ differentialAt y f.1)) =
        n - componentDimension P := by
  have hle := componentDimension_le P
  rw [jacobianSmoothPoint_iff_span, componentDimension_eq_ringKrullDim]
  apply and_congr_right
  intro _
  constructor
  · intro h
    have h' : Module.finrank k (Submodule.span k (Set.range fun f : P.asIdeal ↦
        differentialAt y f.1)) + componentDimension P = n := by exact_mod_cast h
    omega
  · intro h
    have h' : Module.finrank k (Submodule.span k (Set.range fun f : P.asIdeal ↦
        differentialAt y f.1)) + componentDimension P = n := by omega
    exact_mod_cast h'

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
open Stafford38.Geometry.SmoothAffineConormal in
/-- At a Mathlib smooth point `y` the Zariski tangent space has dimension
`dim_F Ω_{F/K}`.  The stalk `(Ω_{R/K})_𝔪` is free; its rank is read off once at `y`
(`L = K`) and once at the generic point (`L = F`), where Lemma 5.12(a) gives
`dim_F Ω_{F/K}`. -/
theorem finrank_zariskiTangentSpace_of_smoothAffinePoint
    (P : PrimeSpectrum (MvPolynomial (Fin n) k)) {y : Fin n → k}
    (hy : SmoothAffinePoint P.asIdeal y) :
    Module.finrank k (zariskiTangentSpace y P.asIdeal) =
      Module.finrank (FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal))
        Ω[FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal)⁄k] := by
  classical
  set A := MvPolynomial (Fin n) k ⧸ P.asIdeal
  set F := FractionRing A
  obtain ⟨e, heval, hsm⟩ := hy
  set 𝔪 : Ideal A := RingHom.ker e.toRingHom
  have : 𝔪.IsPrime := RingHom.ker_isPrime e
  rw [Algebra.smoothLocus_eq_compl_support_inter] at hsm
  have : Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl Ω[A⁄k]) :=
    Module.mem_freeLocus.1 hsm.2
  -- The point `y`: `L = K` through `e : R → K`.
  have hK : Module.finrank k (zariskiTangentSpace y P.asIdeal) =
      Module.finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl Ω[A⁄k]) := by
    let : Algebra A k := e.toRingHom.toAlgebra
    have : IsScalarTower k A k := ⟨fun c a x ↦ by
      change e (c • a) * x = c * (e a * x)
      rw [map_smul, smul_eq_mul, mul_assoc]⟩
    have hunitK : ∀ s : 𝔪.primeCompl, IsUnit (e.toRingHom (s : A)) :=
      fun s ↦ isUnit_iff_ne_zero.2 fun h ↦ s.2 h
    let : Algebra (Localization.AtPrime 𝔪) k :=
      (IsLocalization.lift (M := 𝔪.primeCompl) (S := Localization.AtPrime 𝔪) hunitK).toAlgebra
    have : IsScalarTower A (Localization.AtPrime 𝔪) k :=
      IsScalarTower.of_algebraMap_eq fun a ↦ (IsLocalization.lift_eq hunitK a).symm
    have h := finrank_zariskiTangentSpace_eq_finrank_localizedKaehler (L := k) 𝔪
    have hpt : GenericPointKaehlerConormal.genericPoint P.asIdeal k = y := by
      funext i
      change e (Ideal.Quotient.mk _ (X i)) = y i
      rw [heval]
      simp
    have hmap : MvPolynomial.map (algebraMap k k) =
        RingHom.id (MvPolynomial (Fin n) k) := by
      rw [Algebra.algebraMap_self]
      exact RingHom.ext MvPolynomial.map_id
    rwa [hpt, hmap, Ideal.map_id] at h
  -- The generic point: `L = F`.
  have hF : Module.finrank F (zariskiTangentSpace (GenericPointKaehlerConormal.genericPoint P.asIdeal F)
        (P.asIdeal.map (MvPolynomial.map (algebraMap k F)))) =
      Module.finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl Ω[A⁄k]) := by
    let : Algebra (Localization.AtPrime 𝔪) F :=
      IsLocalization.localizationAlgebraOfSubmonoidLe _ _ 𝔪.primeCompl (nonZeroDivisors A)
        (Ideal.primeCompl_le_nonZeroDivisors 𝔪)
    have : IsScalarTower A (Localization.AtPrime 𝔪) F :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (R := A)
        (Localization.AtPrime 𝔪) F 𝔪.primeCompl (nonZeroDivisors A)
        (Ideal.primeCompl_le_nonZeroDivisors 𝔪)
    exact finrank_zariskiTangentSpace_eq_finrank_localizedKaehler (L := F) 𝔪
  have hgen : IntermediateField.adjoin k
      (Set.range (GenericPointKaehlerConormal.genericPoint P.asIdeal F)) = ⊤ := by
    have : GenericPointKaehlerConormal.genericPoint P.asIdeal F =
        AffineComponentCoordinateSplit.componentCoordinate P := funext fun _ ↦ rfl
    rw [this]
    exact ExactDivisorialVisibleFrameExistence.componentCoordinate_adjoin_eq_top P
  have h512 := generic_tangent_finrank_eq_component_kaehler_finrank (E := F)
    (I := P.asIdeal) hgen
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h512
  rw [hK, ← hF, ← h512]

open Stafford38.Geometry.SmoothAffineConormal in
/-- **Definition 5.4(b), Lean smooth points are Jacobian smooth.** A point of Mathlib's
smooth locus of `K[x]/𝔭` (`SmoothAffinePoint`) lies in the paper's `Y_sm`: the Jacobian
of `𝔭` has rank `n - dim Y` there.  The converse is `definition_5_4_b_iff`. -/
theorem definition_5_4_b [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin n) k)) {y : Fin n → k}
    (hy : SmoothAffinePoint P.asIdeal y) : JacobianSmoothPoint P y := by
  rw [jacobianSmoothPoint_iff_trdeg]
  refine ⟨smoothAffinePoint_mem_zeroLocus P.asIdeal hy, ?_⟩
  have h1 := finrank_differentialSpan_add_finrank_zariskiTangentSpace P.asIdeal y
  have h2 := finrank_zariskiTangentSpace_of_smoothAffinePoint P hy
  have h3 := (component_kaehler_finrank_eq_trdeg (k := k)
    (AffineComponentCoordinateSplit.componentCoordinate P)
    (ExactDivisorialVisibleFrameExistence.componentCoordinate_adjoin_eq_top P)).2
  rw [componentDimension]
  omega

open Stafford38.Geometry.SmoothAffineConormal in
/-- **Definition 5.4(b), the Jacobian criterion.** `y` lies in Mathlib's smooth locus of
`K[x]/𝔭` iff the Jacobian of `𝔭` has rank `n - dim Y` at `y ∈ Y`.  The converse direction
picks equations `f_1, …, f_c ∈ 𝔭` with independent differentials at `y` and applies
`smoothAffinePoint_of_jacobian`. -/
theorem definition_5_4_b_iff [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin n) k)) (y : Fin n → k) :
    SmoothAffinePoint P.asIdeal y ↔ JacobianSmoothPoint P y := by
  classical
  refine ⟨definition_5_4_b P, fun h ↦ ?_⟩
  have hle := componentDimension_le P
  rw [jacobianSmoothPoint_iff_trdeg] at h
  obtain ⟨hy, hr⟩ := h
  obtain ⟨s, hsub, hspan, hli⟩ :=
    exists_linearIndependent k (Set.range fun f : P.asIdeal ↦ differentialAt y f.1)
  have : Fintype s := (hli.setFinite).fintype
  have hcard : Fintype.card s = Module.finrank k
      (Submodule.span k (Set.range fun f : P.asIdeal ↦ differentialAt y f.1)) := by
    rw [← hspan, ← finrank_span_eq_card hli, Subtype.range_coe]
  have hg : ∀ v : s, ∃ g : MvPolynomial (Fin n) k, g ∈ P.asIdeal ∧ differentialAt y g = v :=
    fun v ↦ by
      obtain ⟨g, hg⟩ := hsub v.2
      exact ⟨g.1, g.2, hg⟩
  choose g hgP hgd using hg
  have hli' : LinearIndependent k fun v : s ↦ differentialAt y (g v) := by
    convert hli using 1
    funext v
    exact hgd v
  exact smoothAffinePoint_of_jacobian P hy g hgP hli' (by
    change Fintype.card s + componentDimension P = n
    omega)

end SmoothPoint

section ConormalCone

open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ConormalPrincipalOpenDensity

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- **Definition 5.4(d), as printed.** The conormal cone
`N(Y) = ⋃_{y ∈ Y_sm} N*_y Y` over the Jacobian smooth locus, with
`N*_y Y = span_K {df_y : f ∈ I(Y)}`. -/
def conormalCone (P : PrimeSpectrum (MvPolynomial (Fin n) k)) : Set (Fin n → k) :=
  {ξ | ∃ y, JacobianSmoothPoint P y ∧
    ξ ∈ Submodule.span k (Set.range fun f : P.asIdeal ↦ differentialAt y f.1)}

/-- **`N(Y)` as printed is the Lean conormal cone**: the Jacobian smooth locus is Mathlib's
smooth locus (`definition_5_4_b_iff`). -/
theorem conormalCone_paper_eq [CharZero k] (P : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    conormalCone P = smoothConormalFibreProjection P.asIdeal := by
  ext ξ
  rw [definition_5_4_d]
  simp only [conormalCone, Set.mem_ofPred_eq, definition_5_4_b_iff]

omit [IsAlgClosed k] in
theorem projectivizedDirectionSet_smoothConormalDirectionSet
    (I : Ideal (MvPolynomial (Fin n) k)) :
    projectivizedDirectionSet (smoothConormalDirectionSet I) =
      projectivizedDirectionSet (smoothConormalFibreProjection I) := by
  ext z
  constructor
  · rintro ⟨v, ⟨y, hy, _, hc⟩, hv, rfl⟩
    exact ⟨v, ⟨y, hy, hc⟩, hv, rfl⟩
  · rintro ⟨v, ⟨y, hy, hc⟩, hv, rfl⟩
    exact ⟨v, ⟨y, hy, hv, hc⟩, hv, rfl⟩

/-- **Definition 5.5, as printed.** `Dir(Y)` is the Zariski closure in `ℙ((K^n)^*)` of
`{[ξ] : 0 ≠ ξ ∈ N(Y)}`; projective Zariski closed sets are the common zero sets of
homogeneous polynomials. -/
def conormalDirections (P : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    Set (Projectivization k (Fin n → k)) :=
  projectiveHomogeneousClosure (projectivizedDirectionSet (conormalCone P))

/-- **Definition 5.5.** The printed `Dir(Y)` is the Lean direction closure used in
Theorem 5.7(ii). -/
theorem definition_5_5 [CharZero k] (P : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    conormalDirections P = projectiveHomogeneousClosure
      (projectivizedDirectionSet (smoothConormalDirectionSet P.asIdeal)) := by
  rw [projectivizedDirectionSet_smoothConormalDirectionSet, conormalDirections,
    conormalCone_paper_eq]

end ConormalCone

section Theorem57

open Stafford38.Geometry.ProjectiveConormalDirections

/-- **Theorem 5.7(i), as printed.** Let `Y = V(𝔭)` be irreducible with `Y ∩ H = ∅`, and
let `N(Y)` be the conormal cone over the Jacobian smooth locus.  Every polynomial
`P ∈ K[ξ_1, …, ξ_n]` vanishing on `N(Y)` satisfies `P(1, 0, …, 0) = 0`. -/
theorem theorem_5_7_i_printed
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0)
    (Q : MvPolynomial (Fin m) k) (hQ : ∀ ξ ∈ conormalCone I, MvPolynomial.eval ξ Q = 0) :
    MvPolynomial.eval (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) Q = 0 := by
  have hQ' : Q ∈ MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff, ← conormalCone_paper_eq I]
    simpa using hQ
  simpa using (MvPolynomial.mem_zeroLocus_iff.1 (theorem_5_7_i hm I havoid)) Q hQ'

/-- **Theorem 5.7(ii), as printed.** `[dx_1] ∈ Dir(Y)`. -/
theorem theorem_5_7_ii_printed
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    Projectivization.mk k
        (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0)
        (by intro h; have := congrFun h ⟨0, hm⟩; simp at this) ∈
      conormalDirections I := by
  rw [definition_5_5]
  exact theorem_5_7_ii hm I havoid

end Theorem57

end

#print axioms derivation_quotient_mk_eq_sum
#print axioms derivation_coordinates_mem_zariskiTangentSpace
#print axioms exists_derivation_of_mem_zariskiTangentSpace
#print axioms finrank_zariskiTangentSpace_eq_finrank_localizedKaehler
#print axioms finrank_differentialSpan_add_finrank_zariskiTangentSpace
#print axioms jacobian_rank_eq_finrank_differentialSpan
#print axioms componentDimension_eq_ringKrullDim
#print axioms componentDimension_le
#print axioms jacobianSmoothPoint_iff_trdeg
#print axioms finrank_zariskiTangentSpace_of_smoothAffinePoint
#print axioms definition_5_4_b
#print axioms definition_5_4_b_iff
#print axioms conormalCone_paper_eq
#print axioms projectivizedDirectionSet_smoothConormalDirectionSet
#print axioms definition_5_5
#print axioms theorem_5_7_i_printed
#print axioms theorem_5_7_ii_printed

end Stafford38.Paper.Section5
