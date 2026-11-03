module

public import Stafford38.Geometry.PaperGenericTangentRank
public import Stafford38.Geometry.KaehlerTranscendenceBasis
public import Stafford38.Geometry.PowerSeriesArcTangency
public import Stafford38.Paper.Section5.Definitions

@[expose] public section

/-!
# Lemma 5.12(a): the generic tangent space has dimension `dim Ω_{F/k}`

Let `F` be the function field of the component cut out by the prime `I`, with
generic point `y ∈ F^m`, and let `E ⊇ F` be a field extension (in the paper
`E = κ((t))`).  `Θ_y` is the tangent space at `y` of the equations of `I` with
coefficients extended to `E`.  The proof follows the paper: the second
fundamental exact sequence for `k[x] → R = k[x]/I` gives
`Ω_{R/k} = R^m / span_R {df(x̄) : f ∈ I}` (`quotientKaehlerMap_exact`), its
localization gives `Ω_{F/k} = F^m / span_F {df(x̄)}` (`fieldKaehlerMap_exact`),
so the Jacobian has rank `m - dim Ω_{F/k}` over `F`; rank does not change under
`F ⊆ E`, and `Θ_y` is the common kernel of the `df_y`.  In characteristic zero
`dim Ω_{F/k}` is the transcendence degree of `F/k`.
-/

namespace Stafford38.Paper.Section5

open Stafford38.Geometry
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open KaehlerDifferential

noncomputable section

universe u

/-- A vector is tangent to the scalar extension of `I` at `y` once `y` is a
zero of `I` and the vector is killed by the differentials of the equations of
`I` themselves: `E`-combinations of equations vanishing at `y` add nothing. -/
theorem mem_zariskiTangentSpace_map_of_forall_mem
    {k E : Type*} [Field k] [Field E] [Algebra k E]
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k)) (y w : Fin m → E)
    (hy : ∀ g ∈ I, MvPolynomial.eval₂ (algebraMap k E) y g = 0)
    (hw : ∀ g ∈ I, ∑ i, MvPolynomial.eval₂ (algebraMap k E) y
      (MvPolynomial.pderiv i g) * w i = 0) :
    w ∈ zariskiTangentSpace y (I.map (MvPolynomial.map (algebraMap k E))) := by
  have hmap : ∀ h ∈ I.map (MvPolynomial.map (algebraMap k E)),
      MvPolynomial.eval y h = 0 ∧ differentialCovector y h w = 0 := by
    intro h hh
    rw [Ideal.map] at hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
        rcases hh with ⟨g, hg, rfl⟩
        refine ⟨by rw [MvPolynomial.eval_map]; exact hy g hg, ?_⟩
        simpa [differentialCovector, differentialAt, MvPolynomial.pderiv_map,
          MvPolynomial.eval_map] using hw g hg
    | zero => simp [differentialCovector, differentialAt]
    | add h₁ h₂ _ _ ih₁ ih₂ =>
        refine ⟨by rw [MvPolynomial.eval_add, ih₁.1, ih₂.1, add_zero], ?_⟩
        have hadd : differentialCovector y (h₁ + h₂) w =
            differentialCovector y h₁ w + differentialCovector y h₂ w := by
          simp only [differentialCovector_apply, differentialAt, map_add,
            add_mul, Finset.sum_add_distrib]
        rw [hadd, ih₁.2, ih₂.2, add_zero]
    | smul a h _ ih =>
        rw [show (a • h : MvPolynomial (Fin m) E) = a * h by rfl]
        refine ⟨by rw [MvPolynomial.eval_mul, ih.1, mul_zero], ?_⟩
        rw [differentialCovector_mul]
        simp [ih.1, ih.2]
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator]
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨g, rfl⟩
      exact (hmap g.1 g.2).2
  | zero => simp
  | add φ ψ _ _ ihφ ihψ => simp [ihφ, ihψ]
  | smul a φ _ ihφ => simp [ihφ]

/-- The generic point of the component is a zero of every equation in `I`. -/
theorem eval₂_genericPoint_eq_zero
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    {m : ℕ} {I : Ideal (MvPolynomial (Fin m) k)}
    [Algebra (MvPolynomial (Fin m) k ⧸ I) F]
    [IsScalarTower k (MvPolynomial (Fin m) k ⧸ I) F]
    {g : MvPolynomial (Fin m) k} (hg : g ∈ I) :
    MvPolynomial.eval₂ (algebraMap k F)
      (GenericPointKaehlerConormal.genericPoint I F) g = 0 := by
  have hhom : MvPolynomial.aeval (GenericPointKaehlerConormal.genericPoint I F) =
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k ⧸ I) F).comp
        (Ideal.Quotient.mkₐ k I) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [GenericPointKaehlerConormal.genericPoint]
  have h := congrArg (fun φ ↦ φ g) hhom
  simp only [MvPolynomial.aeval_def, AlgHom.comp_apply,
    Ideal.Quotient.mkₐ_eq_mk, (Ideal.Quotient.eq_zero_iff_mem).2 hg,
    map_zero] at h
  exact h

section ExactSequence

variable {k : Type*} [Field k] {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k))

local notation "A" => MvPolynomial (Fin m) k
local notation "R" => MvPolynomial (Fin m) k ⧸ I

/-- The column `df(x̄) = (∂_i f(x̄))_i ∈ R^n` of an equation `f`. -/
noncomputable def quotientGradient (f : A) : Fin m → R :=
  fun i ↦ Ideal.Quotient.mk I (MvPolynomial.pderiv i f)

/-- `ξ ↦ Σ ξ_i dx̄_i`, from `R^n` to `Ω_{R/K}`. -/
noncomputable def quotientKaehlerMap : (Fin m → R) →ₗ[R] Ω[R⁄k] :=
  Fintype.linearCombination R fun i ↦ D k R (Ideal.Quotient.mk I (MvPolynomial.X i))

/-- **Second fundamental exact sequence for `K[x] → R = K[x]/𝔭`.**  In
`R ⊗ Ω_{K[x]/K} = R^n` (basis `1 ⊗ dx_i`) the image of `f ∈ 𝔭` is `df(x̄)`, and the
exact sequence `𝔭/𝔭² → R^n → Ω_{R/K} → 0` (Matsumura, Thm. 25.2) gives
`Ω_{R/K} = R^n / span_R {df(x̄) : f ∈ 𝔭}`: the map `ξ ↦ Σ ξ_i dx̄_i` is onto, with
kernel `span_R {df(x̄)}`. -/
theorem quotientKaehlerMap_exact :
    LinearMap.range (quotientKaehlerMap I) = ⊤ ∧
      LinearMap.ker (quotientKaehlerMap I) =
        Submodule.span R (Set.range fun f : I ↦ quotientGradient I f.1) := by
  classical
  have h1 : ∀ ω : Ω[R⁄k], (1 : R) • ω = ω := fun ω ↦ one_smul R ω
  have hδ : ∀ ξ : Fin m → R, quotientKaehlerMap I ξ =
      ∑ i, ξ i • D k R (Ideal.Quotient.mk I (MvPolynomial.X i)) := fun ξ ↦
    Fintype.linearCombination_apply _ _ _
  let tb := Algebra.TensorProduct.basis R (mvPolynomialBasis k (Fin m))
  have htb : ∀ i, mapBaseChange k A R (tb i) = D k R (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    intro i
    simp only [tb, Algebra.TensorProduct.basis_apply, mapBaseChange_tmul,
      mvPolynomialBasis_apply, map_D, h1]
    rfl
  -- The coordinates of `1 ⊗ df` in the basis `1 ⊗ dx_i` are `df(x̄)`.
  have hcoord : ∀ f : A, (1 : R) ⊗ₜ[A] D k A f = ∑ i, quotientGradient I f i • tb i := by
    intro f
    apply tb.repr.injective
    ext i
    rw [Algebra.TensorProduct.basis_repr_tmul, map_sum]
    simp [tb, quotientGradient, Finsupp.single_apply]
  -- Hence the image of `t ∈ R ⊗ Ω_{K[x]/K}` in `Ω_{R/K}` is `δ` of its coordinates.
  have hmap : ∀ ξ : Fin m → R, mapBaseChange k A R (∑ i, ξ i • tb i) = quotientKaehlerMap I ξ := by
    intro ξ
    rw [hδ, map_sum]
    simp_rw [map_smul, htb]
  have hsurj : Function.Surjective (algebraMap A R) := Ideal.Quotient.mk_surjective
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · -- `Ω_{R/K}` is spanned by the `dx̄_i`.
    rw [eq_top_iff]
    intro ω _
    obtain ⟨t, rfl⟩ := mapBaseChange_surjective k A R hsurj ω
    refine ⟨tb.equivFun t, ?_⟩
    rw [← hmap, tb.sum_equivFun]
  · -- `ξ ∈ ker δ`: `t = Σ ξ_i ⊗ dx_i` lies in the kernel of `R ⊗ Ω_{K[x]/K} → Ω_{R/K}`,
    -- hence in the image of `𝔭/𝔭²`, so `t = 1 ⊗ df` for some `f ∈ 𝔭` and `ξ = df(x̄)`.
    intro ξ h
    have hker : (∑ i, ξ i • tb i) ∈ LinearMap.ker (mapBaseChange k A R) := by
      rw [LinearMap.mem_ker, hmap]
      exact h
    obtain ⟨c, hc⟩ := (exact_kerCotangentToTensor_mapBaseChange k A R hsurj _).mp hker
    obtain ⟨⟨f, hf⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
    rw [kerCotangentToTensor_toCotangent] at hc
    have hfI : f ∈ I := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hf
    have hξ : ξ = quotientGradient I f := by
      have := congrArg tb.equivFun ((hcoord f).symm.trans hc)
      simp only [map_sum, map_smul] at this
      funext i
      have hi := congrFun this i
      simpa [Finsupp.single_apply] using hi.symm
    rw [hξ]
    exact Submodule.subset_span ⟨⟨f, hfI⟩, rfl⟩
  · -- `δ(df(x̄)) = d(f(x̄)) = 0` for `f ∈ 𝔭`.
    rw [Submodule.span_le]
    rintro _ ⟨⟨f, hf⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hmap, ← hcoord, mapBaseChange_tmul, h1, map_D]
    change D k R (Ideal.Quotient.mk I f) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 hf, map_zero]

end ExactSequence

/-- A span is carried into the span of the image under a scalar extension `A → B`. -/
theorem algebraMap_comp_mem_span {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (S : ι → Fin n → A) {v : Fin n → A} (hv : v ∈ Submodule.span A (Set.range S)) :
    (fun i ↦ algebraMap A B (v i)) ∈
      Submodule.span B (Set.range fun j i ↦ algebraMap A B (S j i)) := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      exact Submodule.subset_span ⟨j, rfl⟩
  | zero =>
      convert Submodule.zero_mem (Submodule.span B (Set.range fun j i ↦ algebraMap A B (S j i)))
      simp
  | add w w' _ _ hw hw' =>
      convert Submodule.add_mem _ hw hw' using 1
      funext i
      simp
  | smul a w _ hw =>
      convert Submodule.smul_mem _ (algebraMap A B a) hw using 1
      funext i
      simp

section Localization

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {m : ℕ}
  (I : Ideal (MvPolynomial (Fin m) k)) [I.IsPrime]
  [Algebra (MvPolynomial (Fin m) k ⧸ I) F] [IsScalarTower k (MvPolynomial (Fin m) k ⧸ I) F]
  [IsFractionRing (MvPolynomial (Fin m) k ⧸ I) F]

local notation "R" => MvPolynomial (Fin m) k ⧸ I

/-- `df(x̄) ∈ F^n` for an equation `f`. -/
noncomputable def genericGradient (f : MvPolynomial (Fin m) k) : Fin m → F :=
  fun i ↦ algebraMap R F (quotientGradient I f i)

/-- `ξ ↦ Σ ξ_i dx̄_i`, from `F^n` to `Ω_{F/K}`. -/
noncomputable def fieldKaehlerMap : (Fin m → F) →ₗ[F] Ω[F⁄k] :=
  Fintype.linearCombination F fun i ↦
    D k F (GenericPointKaehlerConormal.genericPoint I F i)

/-- **Localization of the exact sequence.**  `Ω_{S⁻¹R/K} = S⁻¹ Ω_{R/K}` for
`S = R ∖ {0}` (Hartshorne, Prop. II.8.2A), and localization is exact, so
`Ω_{F/K} = F^n / span_F {df(x̄) : f ∈ 𝔭}`. -/
theorem fieldKaehlerMap_exact :
    LinearMap.range (fieldKaehlerMap (F := F) I) = ⊤ ∧
      LinearMap.ker (fieldKaehlerMap (F := F) I) =
        Submodule.span F (Set.range fun f : I ↦ genericGradient (F := F) I f.1) := by
  classical
  obtain ⟨hrangeR, hkerR⟩ := quotientKaehlerMap_exact I
  let φ := KaehlerDifferential.map k k R F
  have hδF : ∀ ξ : Fin m → F, fieldKaehlerMap I ξ =
      ∑ i, ξ i • D k F (GenericPointKaehlerConormal.genericPoint I F i) := fun ξ ↦
    Fintype.linearCombination_apply _ _ _
  have hδR : ∀ ξ : Fin m → R, quotientKaehlerMap I ξ =
      ∑ i, ξ i • D k R (Ideal.Quotient.mk I (MvPolynomial.X i)) := fun ξ ↦
    Fintype.linearCombination_apply _ _ _
  -- `Ω_{R/K} → Ω_{F/K}` sends `Σ ξ_i dx̄_i` to `Σ ξ_i dx̄_i`.
  have hφ : ∀ ξ : Fin m → R, φ (quotientKaehlerMap I ξ) =
      fieldKaehlerMap I (fun i ↦ algebraMap R F (ξ i)) := by
    intro ξ
    rw [hδR, hδF, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_D]
    exact (algebraMap_smul F (ξ i) (D k F (GenericPointKaehlerConormal.genericPoint I F i))).symm
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · -- `Ω_{F/K}` is spanned by the images of `Ω_{R/K} = δ_R(R^n)`.
    rw [eq_top_iff, ← span_range_map_derivation_of_isLocalization k R F (nonZeroDivisors R),
      Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    obtain ⟨ξ, hξ⟩ : D k R r ∈ LinearMap.range (quotientKaehlerMap I) := by
      rw [hrangeR]; exact Submodule.mem_top
    refine ⟨fun i ↦ algebraMap R F (ξ i), ?_⟩
    rw [← hφ, hξ]
    rfl
  · -- Clear denominators, `ξ = b⁻¹ ξ'`; then `Σ ξ'_i dx̄_i` dies in `F ⊗ Ω_{R/K}`, so
    -- `c Σ ξ'_i dx̄_i = 0` in `Ω_{R/K}` for some `c ≠ 0`, and `c ξ' ∈ span_R {df(x̄)}`.
    intro ξ hξ
    rw [LinearMap.mem_ker] at hξ
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) ξ
    choose ξ' hξ' using hb
    have hzero : φ (quotientKaehlerMap I ξ') = 0 := by
      rw [hφ]
      have : (fun i ↦ algebraMap R F (ξ' i)) = (algebraMap R F b) • ξ := by
        funext i
        rw [hξ' i, Pi.smul_apply, Algebra.smul_def, smul_eq_mul]
      rw [this, map_smul, hξ, smul_zero]
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) φ).mp hzero
    have hmem : (c : R) • ξ' ∈ Submodule.span R (Set.range fun f : I ↦ quotientGradient I f.1) := by
      rw [← hkerR, LinearMap.mem_ker, map_smul]
      exact hc
    have hF := algebraMap_comp_mem_span (B := F) _ hmem
    have hb0 : algebraMap R F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    have hc0 : algebraMap R F c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
    have hξeq : ξ = (algebraMap R F c * algebraMap R F b)⁻¹ •
        (fun i ↦ algebraMap R F (((c : R) • ξ') i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, hξ' i]
      rw [Algebra.smul_def]
      field_simp
    rw [hξeq]
    exact Submodule.smul_mem _ _ hF
  · -- `δ_F(df(x̄))` is the image of `δ_R(df(x̄)) = 0`.
    rw [Submodule.span_le]
    rintro _ ⟨⟨f, hf⟩, rfl⟩
    have hR : quotientKaehlerMap I (quotientGradient I f) = 0 := by
      rw [← LinearMap.mem_ker, hkerR]
      exact Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have := hφ (quotientGradient I f)
    rw [hR, map_zero] at this
    exact this.symm

end Localization

/-- **Lemma 5.12(a), `dim Θ_y = dim Ω_{F/k}`.**  By the exact sequence and its
localization (`fieldKaehlerMap_exact`), `span_F {df(x̄) : f ∈ 𝔭}` has dimension
`n − dim_F Ω_{F/K}`.  Rank does not change under the field extension `F ⊆ E`
(in the paper `E = κ((t))`), so `span_E {df_y : f ∈ 𝔭}` has the same dimension,
and `Θ_y = ⋂_f ker df_y` has dimension `n − (n − dim_F Ω_{F/K})`. -/
theorem generic_tangent_finrank_eq_component_kaehler_finrank
    {k F E : Type u} [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    {m : ℕ} {I : Ideal (MvPolynomial (Fin m) k)} [I.IsPrime]
    [Algebra (MvPolynomial (Fin m) k ⧸ I) F]
    [IsScalarTower k (MvPolynomial (Fin m) k ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin m) k ⧸ I) F] :
    Module.finrank E
        (zariskiTangentSpace
          (fun i ↦ algebraMap F E
            (GenericPointKaehlerConormal.genericPoint I F i))
          (I.map (MvPolynomial.map (algebraMap k E)))) =
      Module.finrank F (Ω[F⁄k]) := by
  classical
  let yF := GenericPointKaehlerConormal.genericPoint I F
  let yE : Fin m → E := fun i ↦ algebraMap F E (yF i)
  let IE : Ideal (MvPolynomial (Fin m) E) := I.map (MvPolynomial.map (algebraMap k E))
  obtain ⟨hrange, hker⟩ := fieldKaehlerMap_exact (F := F) I
  -- `dim_F span_F {df(x̄)} = n − dim_F Ω_{F/K}`.
  let T : Submodule F (Fin m → F) :=
    Submodule.span F (Set.range fun f : I ↦ genericGradient (F := F) I f.1)
  have hTdim : Module.finrank F T + Module.finrank F (Ω[F⁄k]) = m := by
    have h := LinearMap.finrank_range_add_finrank_ker (fieldKaehlerMap (F := F) I)
    rw [hrange, hker, finrank_top, Module.finrank_fin_fun] at h
    rw [add_comm]
    exact h
  -- Rank does not change under `F ⊆ E`.
  let gE : I → Fin m → E := fun f i ↦ algebraMap F E (genericGradient (F := F) I f.1 i)
  let TE : Submodule E (Fin m → E) := Submodule.span E (Set.range gE)
  have hTE : Module.finrank E TE = Module.finrank F T := by
    let b := Module.finBasis F T
    let z : Fin (Module.finrank F T) → Fin m → F := fun j ↦ (b j : Fin m → F)
    have hliF : LinearIndependent F z :=
      b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
    have hli : LinearIndependent E (fun j i ↦ algebraMap F E (z j i)) :=
      (linearIndependent_algebraMap_comp_iff (R := F) (S := E) (ι' := Fin m)).2 hliF
    have hspanz : Submodule.span F (Set.range z) = T := by
      have h := congrArg (Submodule.map T.subtype) b.span_eq
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at h
      exact h
    have hTEeq : TE = Submodule.span E (Set.range fun j i ↦ algebraMap F E (z j i)) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨f, rfl⟩
        have hf : genericGradient (F := F) I f.1 ∈ Submodule.span F (Set.range z) := by
          rw [hspanz]
          exact Submodule.subset_span ⟨f, rfl⟩
        exact algebraMap_comp_mem_span (B := E) z hf
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact algebraMap_comp_mem_span (B := E) (fun f : I ↦ genericGradient (F := F) I f.1)
          (b j).2
    rw [hTEeq, finrank_span_eq_card hli, Fintype.card_fin]
  -- `df_y` for `f ∈ 𝔭` is the image of `df(x̄)`, and `f(y) = 0`.
  have hevalF : ∀ p : MvPolynomial (Fin m) k, MvPolynomial.eval₂ (algebraMap k F) yF p =
      algebraMap (MvPolynomial (Fin m) k ⧸ I) F (Ideal.Quotient.mk I p) := by
    have hhom : MvPolynomial.aeval yF =
        (IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k ⧸ I) F).comp
          (Ideal.Quotient.mkₐ k I) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [yF, GenericPointKaehlerConormal.genericPoint]
    intro p
    exact congrArg (fun φ ↦ φ p) hhom
  have hevalE : ∀ p : MvPolynomial (Fin m) k, MvPolynomial.eval₂ (algebraMap k E) yE p =
      algebraMap F E (MvPolynomial.eval₂ (algebraMap k F) yF p) := by
    intro p
    rw [MvPolynomial.eval₂_comp_left, ← IsScalarTower.algebraMap_eq k F E]
    rfl
  have hdf : ∀ f : MvPolynomial (Fin m) k, ∀ i,
      Stafford38.Geometry.CoisotropicTranslation.differentialAt yE
        (MvPolynomial.map (algebraMap k E) f) i =
          algebraMap F E (genericGradient (F := F) I f i) := by
    intro f i
    simp only [Stafford38.Geometry.CoisotropicTranslation.differentialAt,
      MvPolynomial.pderiv_map, MvPolynomial.eval_map]
    rw [hevalE, hevalF]
    rfl
  have hzero : ∀ g ∈ I, MvPolynomial.eval₂ (algebraMap k E) yE g = 0 := by
    intro g hg
    rw [hevalE, hevalF, (Ideal.Quotient.eq_zero_iff_mem).2 hg, map_zero, map_zero]
  -- `Θ_y = ⋂_{f ∈ 𝔭} ker df_y`.
  let C := TE.map (coordinateCovectorLinear (k := E) (n := m))
  have hC : Module.finrank E C = Module.finrank E TE :=
    (Submodule.equivMapOfInjective _ coordinateCovector_injective TE).finrank_eq.symm
  have hΘ : zariskiTangentSpace yE IE = C.dualCoannihilator := by
    apply le_antisymm
    · intro v hv
      rw [Submodule.mem_dualCoannihilator]
      rintro _ ⟨t, ht, rfl⟩
      induction ht using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨f, rfl⟩ := ht
          have hfE : MvPolynomial.map (algebraMap k E) f.1 ∈ IE :=
            Ideal.mem_map_of_mem _ f.2
          have h := (Submodule.mem_dualCoannihilator _).1 hv _
            (Submodule.subset_span ⟨⟨_, hfE⟩, rfl⟩)
          rw [differentialCovector_apply] at h
          change ∑ i, gE f i * v i = 0
          simpa [gE, hdf] using h
      | zero => simp
      | add t t' _ _ ht ht' => simp [ht, ht']
      | smul a t _ ht => simp [ht]
    · intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      apply mem_zariskiTangentSpace_map_of_forall_mem I yE v hzero
      intro g hg
      have h := hv _ ⟨gE ⟨g, hg⟩, Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩, rfl⟩
      change ∑ i, gE ⟨g, hg⟩ i * v i = 0 at h
      have h' : ∀ i, MvPolynomial.eval₂ (algebraMap k E) yE (MvPolynomial.pderiv i g) =
          gE ⟨g, hg⟩ i := by
        intro i
        have := hdf g i
        simp only [Stafford38.Geometry.CoisotropicTranslation.differentialAt,
          MvPolynomial.pderiv_map, MvPolynomial.eval_map] at this
        exact this
      simp_rw [h']
      exact h
  have hdual := Subspace.finrank_add_finrank_dualCoannihilator_eq C
  rw [← hΘ, hC, hTE, Module.finrank_fin_fun] at hdual
  change Module.finrank E (zariskiTangentSpace yE IE) = _
  omega

/-- **`dim Ω_{F/k} = trdeg_k F`.**  For a field `F` generated over `k` by
finitely many elements, in characteristic zero, the Kähler rank is the
transcendence degree (Matsumura, Thm. 26.5), which is finite. -/
theorem component_kaehler_finrank_eq_trdeg
    {k F : Type u} [Field k] [CharZero k] [Field F] [Algebra k F]
    {m : ℕ} (y : Fin m → F)
    (hgen : IntermediateField.adjoin k (Set.range y) = ⊤) :
    (Module.finrank F (Ω[F⁄k]) : Cardinal) = Algebra.trdeg k F ∧
      Module.finrank F (Ω[F⁄k]) = (Algebra.trdeg k F).toNat := by
  classical
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range y)) F := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, hgen,
      Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) (Set.range y)
  have htfin : t.Finite := (Set.finite_range y).subset hts
  let : Fintype t := htfin.fintype
  have hrank : Module.finrank F (Ω[F⁄k]) = Fintype.card t :=
    kaehlerFinrankOfTranscendenceBasis k F t (↑) ht
  have hcard : (Fintype.card t : Cardinal) = Algebra.trdeg k F := by
    rw [← Cardinal.mk_fintype]
    exact (definition_5_1_g_h ht).2
  refine ⟨by rw [hrank, hcard], ?_⟩
  rw [← hcard, Cardinal.toNat_natCast, hrank]

end

#print axioms mem_zariskiTangentSpace_map_of_forall_mem
#print axioms eval₂_genericPoint_eq_zero
#print axioms quotientKaehlerMap_exact
#print axioms fieldKaehlerMap_exact
#print axioms generic_tangent_finrank_eq_component_kaehler_finrank
#print axioms component_kaehler_finrank_eq_trdeg

end Stafford38.Paper.Section5
