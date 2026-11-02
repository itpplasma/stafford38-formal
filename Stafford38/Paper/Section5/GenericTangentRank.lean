module

public import Stafford38.Geometry.PaperGenericTangentRank
public import Stafford38.Geometry.KaehlerTranscendenceBasis
public import Stafford38.Geometry.PowerSeriesArcTangency

@[expose] public section

/-!
# Lemma 5.12(a): the generic tangent space has dimension `dim Ω_{F/k}`

Let `F` be the function field of the component cut out by the prime `I`, with
generic point `y ∈ F^m`, and let `E ⊇ F` be a field extension (in the paper
`E = κ((t))`).  `Θ_y` is the tangent space at `y` of the equations of `I` with
coefficients extended to `E`.  The paper's argument is that the Jacobian has
rank `m - dim Ω_{F/k}` over `F` and that rank does not change under `F ⊆ E`.

The upper bound `dim Θ_y ≤ dim Ω_{F/k}` is
`generic_tangent_finrank_le_component_kaehler_finrank`.  The lower bound below
uses the derivations of `F/k`: every `F`-linear form on `Ω_{F/k}` gives a
derivation `D`, and `(D y_i)_i` is tangent at `y`.  Such vectors for a dual
basis are linearly independent over `F`, hence over `E`.  In characteristic
zero `dim Ω_{F/k}` is the transcendence degree of `F/k`.
-/

namespace Stafford38.Paper.Section5

open Stafford38.Geometry
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation

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

/-- **Lemma 5.12(a), lower bound.**  The tangent space `Θ_y` at the generic
point, with coefficients extended to `E`, has dimension at least
`dim_F Ω_{F/k}`. -/
theorem component_kaehler_finrank_le_generic_tangent_finrank
    {k F E : Type u} [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    {m : ℕ} {I : Ideal (MvPolynomial (Fin m) k)} [I.IsPrime]
    [Algebra (MvPolynomial (Fin m) k ⧸ I) F]
    [IsScalarTower k (MvPolynomial (Fin m) k ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin m) k ⧸ I) F]
    (hgen : IntermediateField.adjoin k
      (Set.range (GenericPointKaehlerConormal.genericPoint I F)) = ⊤) :
    Module.finrank F (Ω[F⁄k]) ≤
      Module.finrank E
        (zariskiTangentSpace
          (fun i ↦ algebraMap F E
            (GenericPointKaehlerConormal.genericPoint I F i))
          (I.map (MvPolynomial.map (algebraMap k E)))) := by
  classical
  let yF := GenericPointKaehlerConormal.genericPoint I F
  let yE : Fin m → E := fun i ↦ algebraMap F E (yF i)
  let IE : Ideal (MvPolynomial (Fin m) E) :=
    I.map (MvPolynomial.map (algebraMap k E))
  have hspan : Submodule.span F
      (Set.range fun i ↦ KaehlerDifferential.D k F (yF i)) = ⊤ :=
    Stafford38.Geometry.KaehlerSpanSeparableAdjoin.kaehler_span_of_intermediateField_adjoin_eq_top
      (k := k) (E := F) yF hgen
  have : FiniteDimensional F (Ω[F⁄k]) := by
    have : FiniteDimensional F
        (Submodule.span F
          (Set.range fun i ↦ KaehlerDifferential.D k F (yF i))) :=
      FiniteDimensional.span_of_finite F (Set.finite_range _)
    have : FiniteDimensional F (⊤ : Submodule F (Ω[F⁄k])) :=
      (LinearEquiv.ofEq _ _ hspan).finiteDimensional
    exact Submodule.topEquiv.finiteDimensional
  -- `Φ ψ = (ψ (d y_i))_i`: the Jacobian-dual coordinates of a form on `Ω`.
  let Φ : Module.Dual F (Ω[F⁄k]) →ₗ[F] (Fin m → F) :=
    { toFun := fun ψ i ↦ ψ (KaehlerDifferential.D k F (yF i))
      map_add' := by intro ψ χ; rfl
      map_smul' := by intro a ψ; rfl }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ψ hψ
    apply LinearMap.ext_on_range hspan
    intro i
    simpa [Φ] using congrFun hψ i
  let b := (Module.finBasis F (Ω[F⁄k])).dualBasis
  let z : Fin (Module.finrank F (Ω[F⁄k])) → Fin m → F := fun j ↦ Φ (b j)
  have hliF : LinearIndependent F z := b.linearIndependent.map' Φ hΦ
  have hliE : LinearIndependent E (fun j i ↦ algebraMap F E (z j i)) :=
    (linearIndependent_algebraMap_comp_iff (R := F) (S := E)
      (ι' := Fin m)).2 hliF
  have htan (j : Fin (Module.finrank F (Ω[F⁄k]))) :
      (fun i ↦ algebraMap F E (z j i)) ∈ zariskiTangentSpace yE IE := by
    let D : Derivation k F F := (b j).compDer (KaehlerDifferential.D k F)
    have hzD : ∀ i, z j i = D (yF i) := fun i ↦ rfl
    have hcomp : algebraMap k E = (algebraMap F E).comp (algebraMap k F) :=
      IsScalarTower.algebraMap_eq k F E
    have hevalE : ∀ p : MvPolynomial (Fin m) k,
        MvPolynomial.eval₂ (algebraMap k E) yE p =
          algebraMap F E (MvPolynomial.eval₂ (algebraMap k F) yF p) := by
      intro p
      rw [MvPolynomial.eval₂_comp_left, ← hcomp]
      rfl
    apply mem_zariskiTangentSpace_map_of_forall_mem
    · intro g hg
      rw [hevalE, eval₂_genericPoint_eq_zero hg, map_zero]
    · intro g hg
      have hchain :=
        Stafford38.Geometry.PowerSeriesArcTangency.derivation_eval₂ D g yF
      rw [show yF = GenericPointKaehlerConormal.genericPoint I F from rfl,
        eval₂_genericPoint_eq_zero hg, map_zero] at hchain
      simp_rw [hevalE, hzD, ← map_mul, ← map_sum]
      rw [← hchain, map_zero]
  have hle : Submodule.span E
      (Set.range fun j i ↦ algebraMap F E (z j i)) ≤ zariskiTangentSpace yE IE := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact htan j
  have hrank := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hliE, Fintype.card_fin] at hrank
  simpa [yE, IE] using hrank

/-- **Lemma 5.12(a), `dim Θ_y = dim Ω_{F/k}`.**  The tangent space at the
generic point, with coefficients extended to `E ⊇ F`, has the Kähler rank of
the component function field as its dimension. -/
theorem generic_tangent_finrank_eq_component_kaehler_finrank
    {k F E : Type u} [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    {m : ℕ} {I : Ideal (MvPolynomial (Fin m) k)} [I.IsPrime]
    [Algebra (MvPolynomial (Fin m) k ⧸ I) F]
    [IsScalarTower k (MvPolynomial (Fin m) k ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin m) k ⧸ I) F]
    (hgen : IntermediateField.adjoin k
      (Set.range (GenericPointKaehlerConormal.genericPoint I F)) = ⊤) :
    Module.finrank E
        (zariskiTangentSpace
          (fun i ↦ algebraMap F E
            (GenericPointKaehlerConormal.genericPoint I F i))
          (I.map (MvPolynomial.map (algebraMap k E)))) =
      Module.finrank F (Ω[F⁄k]) :=
  le_antisymm
    (PaperGenericTangentRank.generic_tangent_finrank_le_component_kaehler_finrank
      (E := E) hgen)
    (component_kaehler_finrank_le_generic_tangent_finrank (E := E) hgen)

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
    exact ht.cardinalMk_eq_trdeg
  refine ⟨by rw [hrank, hcard], ?_⟩
  rw [← hcard, Cardinal.toNat_natCast, hrank]

end

#print axioms mem_zariskiTangentSpace_map_of_forall_mem
#print axioms eval₂_genericPoint_eq_zero
#print axioms component_kaehler_finrank_le_generic_tangent_finrank
#print axioms generic_tangent_finrank_eq_component_kaehler_finrank
#print axioms component_kaehler_finrank_eq_trdeg

end Stafford38.Paper.Section5
