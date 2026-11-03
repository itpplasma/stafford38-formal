module

public import Stafford38.Geometry.ProjectiveConormalDirections
public import Stafford38.Geometry.FibreConicalVanishingIdeal
public import Stafford38.Paper.Section2.Geometry
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

@[expose] public section

/-!
# Definitions 5.4 and 5.6 of the paper, in the paper's form

The repository's canonical notions are
`AffineConormalSpan.affineConormalSpace` (the conormal space `N*_y Y`, defined
as the annihilator of the embedded Zariski tangent space),
`ProjectiveConormalDirections.smoothConormalFibreProjection` (the conormal cone
`N(Y)`) and `FibreConicalVanishingIdeal.IsFibreConical`.  The paper defines
`N*_y Y` as the span of the differentials `df_y`, `f ∈ I(Y)`, and fibre-conical
sets by the scaling `(y, ξ) ↦ (y, tξ)`.  The lemmas below show that the
canonical notions are the paper's, with covectors written in the coordinates
`ξ = (ξ_1, …, ξ_n)` and `df_y = (∂_1 f(y), …, ∂_n f(y))`.

Definition 5.4(a) is `IsIrreducibleClosed` (not a union of two proper closed
subsets), and `definition_5_4_a` proves the printed equivalence with primality of
`I(Y)` for nonempty closed `Y`.  Definition 5.4(b), the Jacobian smooth locus, is
`JacobianSmoothPoint` in `Stafford38.Paper.Section5.SmoothLocus`, where
`definition_5_4_b_iff` proves the Jacobian criterion identifying it with
`SmoothAffinePoint`, the smooth locus of `K[x]/I` in Mathlib's sense.
-/

namespace Stafford38.Paper.Section5

open Stafford38.Characteristic
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.SmoothAffineConormal

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- A Zariski-closed subset of `X = K^n`: `Y = V_K(J)` for an ideal `J ⊆ K[x]`. -/
def IsZariskiClosed (Y : Set (Fin n → k)) : Prop :=
  ∃ J : Ideal (MvPolynomial (Fin n) k), Y = MvPolynomial.zeroLocus k J

/-- **Definition 5.4(a).** A closed set `Y` is irreducible if it is not a union of two
proper closed subsets. -/
def IsIrreducibleClosed (Y : Set (Fin n → k)) : Prop :=
  IsZariskiClosed Y ∧ ¬ ∃ Y₁ Y₂ : Set (Fin n → k), IsZariskiClosed Y₁ ∧ IsZariskiClosed Y₂ ∧
    Y₁ ⊂ Y ∧ Y₂ ⊂ Y ∧ Y = Y₁ ∪ Y₂

/-- A closed set is the zero set of its vanishing ideal: `V_K(I(Y)) = Y`. -/
theorem zeroLocus_vanishingIdeal_of_isZariskiClosed {Y : Set (Fin n → k)}
    (hY : IsZariskiClosed Y) :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Y) = Y := by
  obtain ⟨J, rfl⟩ := hY
  exact le_antisymm (MvPolynomial.zeroLocus_anti_mono (MvPolynomial.le_vanishingIdeal_zeroLocus J))
    (MvPolynomial.zeroLocus_vanishingIdeal_le _)

/-- `V_K(J + (f)) = V_K(J) ∩ {f = 0}`. -/
theorem mem_zeroLocus_sup_span_singleton (J : Ideal (MvPolynomial (Fin n) k))
    (f : MvPolynomial (Fin n) k) (y : Fin n → k) :
    y ∈ MvPolynomial.zeroLocus k (J ⊔ Ideal.span {f}) ↔
      y ∈ MvPolynomial.zeroLocus k J ∧ MvPolynomial.aeval y f = 0 := by
  simp only [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Ideal.mem_sup_left hp),
      h f (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))⟩
  · rintro ⟨hJ, hf⟩ p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    rw [map_add, map_mul, hJ a ha, hf, mul_zero, add_zero]

/-- **Definition 5.4(a), "equivalently if `I(Y)` is prime"** ([Hartshorne, Cor. I.1.4]).
As there, `Y` is nonempty (the empty set has `I(∅) = K[x]`, which is not prime). -/
theorem definition_5_4_a {Y : Set (Fin n → k)} (hne : Y.Nonempty) (hY : IsZariskiClosed Y) :
    IsIrreducibleClosed Y ↔ (MvPolynomial.vanishingIdeal k Y).IsPrime := by
  constructor
  · rintro ⟨-, hirr⟩
    refine ⟨fun htop => ?_, fun {f g} hfg => ?_⟩
    · obtain ⟨y, hy⟩ := hne
      have h1 : (1 : MvPolynomial (Fin n) k) ∈ MvPolynomial.vanishingIdeal k Y :=
        htop ▸ Submodule.mem_top
      have := MvPolynomial.mem_vanishingIdeal_iff.mp h1 y hy
      simp at this
    · by_contra h
      push Not at h
      obtain ⟨hf, hg⟩ := h
      obtain ⟨J, rfl⟩ := hY
      apply hirr
      have hproper : ∀ e : MvPolynomial (Fin n) k, e ∉ MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k J) →
          MvPolynomial.zeroLocus k (J ⊔ Ideal.span {e}) ⊂ MvPolynomial.zeroLocus k J := by
        intro e he
        refine ⟨MvPolynomial.zeroLocus_anti_mono le_sup_left, fun hsub => he ?_⟩
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro y hy
        exact ((mem_zeroLocus_sup_span_singleton J e y).mp (hsub hy)).2
      refine ⟨_, _, ⟨_, rfl⟩, ⟨_, rfl⟩, hproper f hf, hproper g hg, ?_⟩
      ext y
      simp only [Set.mem_union, mem_zeroLocus_sup_span_singleton]
      constructor
      · intro hy
        have h0 := MvPolynomial.mem_vanishingIdeal_iff.mp hfg y hy
        rw [map_mul] at h0
        rcases mul_eq_zero.mp h0 with h0 | h0
        · exact Or.inl ⟨hy, h0⟩
        · exact Or.inr ⟨hy, h0⟩
      · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
  · intro hP
    refine ⟨hY, ?_⟩
    rintro ⟨Y₁, Y₂, hY₁, hY₂, h₁, h₂, hU⟩
    -- a proper closed `Y_i` is cut out inside `Y` by some `f_i ∈ I(Y_i) ∖ I(Y)`
    have hsep : ∀ Z : Set (Fin n → k), IsZariskiClosed Z → Z ⊂ Y →
        ∃ f ∈ MvPolynomial.vanishingIdeal k Z, f ∉ MvPolynomial.vanishingIdeal k Y := by
      intro Z hZ hZY
      obtain ⟨y, hyY, hyZ⟩ := Set.exists_of_ssubset hZY
      rw [← zeroLocus_vanishingIdeal_of_isZariskiClosed hZ, MvPolynomial.mem_zeroLocus_iff] at hyZ
      push Not at hyZ
      obtain ⟨f, hf, hfy⟩ := hyZ
      exact ⟨f, hf, fun hfY => hfy (MvPolynomial.mem_vanishingIdeal_iff.mp hfY y hyY)⟩
    obtain ⟨f₁, hf₁, hf₁Y⟩ := hsep Y₁ hY₁ h₁
    obtain ⟨f₂, hf₂, hf₂Y⟩ := hsep Y₂ hY₂ h₂
    have hprod : f₁ * f₂ ∈ MvPolynomial.vanishingIdeal k Y := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      rw [hU] at hy
      rw [map_mul]
      rcases hy with hy | hy
      · rw [MvPolynomial.mem_vanishingIdeal_iff.mp hf₁ y hy, zero_mul]
      · rw [MvPolynomial.mem_vanishingIdeal_iff.mp hf₂ y hy, mul_zero]
    rcases hP.mem_or_mem hprod with h | h
    · exact hf₁Y h
    · exact hf₂Y h

/-- For nonempty irreducible closed `Y`, the prime `I(Y)` as a point of `Spec K[x]`;
Definitions 5.4(b)–(d) and 5.5 are stated in terms of it. -/
def idealPoint (Y : Set (Fin n → k)) (hne : Y.Nonempty) (hY : IsIrreducibleClosed Y) :
    PrimeSpectrum (MvPolynomial (Fin n) k) :=
  ⟨MvPolynomial.vanishingIdeal k Y, (definition_5_4_a hne hY.1).1 hY⟩

/-- `ξ ↦ Σ ξ_i dx_i`, the identification of coordinate vectors with covectors. -/
def coordinateCovectorLinear :
    (Fin n → k) →ₗ[k] Module.Dual k (AffineTangentVector k n) where
  toFun := coordinateCovector
  map_add' ξ η := by
    ext v
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c ξ := by
    ext v
    simp [Finset.mul_sum, mul_assoc]

/-- **Definition 5.4(c).** `N*_y Y = span_K {df_y : f ∈ I}`, with covectors in
coordinates. -/
theorem definition_5_4_c
    (I : Ideal (MvPolynomial (Fin n) k)) (y ξ : Fin n → k) :
    coordinateCovector ξ ∈ affineConormalSpace y I ↔
      ξ ∈ Submodule.span k (Set.range fun f : I => differentialAt y f.1) := by
  have hspan : equationCovectorSpan y I =
      (Submodule.span k (Set.range fun f : I => differentialAt y f.1)).map
        (coordinateCovectorLinear (k := k) (n := n)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [affineConormalSpace_eq_equationCovectorSpan, hspan]
  constructor
  · rintro ⟨η, hη, hηξ⟩
    have : η = ξ := coordinateCovector_injective hηξ
    exact this ▸ hη
  · intro hξ
    exact ⟨ξ, hξ, rfl⟩

/-- **Definition 5.4(d).** `N(Y) = ⋃_{y ∈ Y_sm} N*_y Y`, in the paper's form of
`N*_y Y`. -/
theorem definition_5_4_d
    [IsAlgClosed k] (I : Ideal (MvPolynomial (Fin n) k)) (ξ : Fin n → k) :
    ξ ∈ smoothConormalFibreProjection I ↔
      ∃ y, SmoothAffinePoint I y ∧
        ξ ∈ Submodule.span k (Set.range fun f : I => differentialAt y f.1) := by
  constructor
  · rintro ⟨y, hy, hξ⟩
    exact ⟨y, hy, (definition_5_4_c I y ξ).1 hξ⟩
  · rintro ⟨y, hy, hξ⟩
    exact ⟨y, hy, (definition_5_4_c I y ξ).2 hξ⟩

/-- **Definition 5.6.** `W` is fibre-conical iff it is stable under the
fibrewise scaling `(y, ξ) ↦ (y, tξ)`, `t ∈ K^×`: the scaling maps
`W ∩ T*_y X` into `W ∩ T*_y X` for every fibre `T*_y X = π⁻¹(y)`
(`Section2.fibre`, Definition 2.5). -/
theorem definition_5_6
    [IsAlgClosed k] [CharZero k] (W : Set (PhaseVar n → k)) :
    Stafford38.Geometry.FibreConicalVanishingIdeal.IsFibreConical W ↔
      ∀ y ξ : Fin n → k, Sum.elim y ξ ∈ W ∩ Stafford38.Paper.Section2.fibre y →
        ∀ t : k, t ≠ 0 → Sum.elim y (t • ξ) ∈ W ∩ Stafford38.Paper.Section2.fibre y := by
  constructor
  · intro hW y ξ hq t ht
    exact ⟨by simpa [Pi.smul_def] using hW _ hq.1 t ht, rfl⟩
  · intro hW q hq t ht
    have hsplit : q = Sum.elim (fun i => q (.inl i)) (fun i => q (.inr i)) := by
      funext i; cases i <;> rfl
    rw [hsplit] at hq
    simpa [Pi.smul_def] using (hW _ _ ⟨hq, rfl⟩ t ht).1

section Definitions51to53

/-! ### Definitions 5.1–5.3

The proof of Theorem 5.7 works with Mathlib's notions for the printed
definitions: 5.1(a)–(b) `IsAlgebraic`, `Transcendental` (`transcendental_iff`
is the printed `g(z) = 0 ⇒ g = 0`), 5.1(c) `minpoly`, 5.1(d) `Algebra.IsAlgebraic`,
5.1(e) separability (automatic in characteristic zero), 5.1(f)
`AlgebraicIndependent` (`algebraicIndependent_iff`), 5.2(a) `Derivation`,
5.3(a) `ValuationSubring` and 5.3(b) `IsDiscreteValuationRing`, and 5.3(c)
`PowerSeries`, `LaurentSeries`; no step needs the printed wording of these, so
it is not restated.  Restated below are the items the proof uses in the
printed form: 5.1(g)–(h) (Lemma 5.11 and Lemma 5.12), and 5.2(b)–(c), the
presentation of `Ω_{κ/K}` and the dual derivations of the paragraph after
Lemma 5.11. -/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Definition 5.1(g)–(h).** For a transcendence basis `B` of `L/K`, `L` is algebraic
over `K(B)`, and `|B| = trdeg_K L`. -/
theorem definition_5_1_g_h {B : Set L} (hB : IsTranscendenceBasis K ((↑) : B → L)) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range ((↑) : B → L))) L ∧
      Cardinal.mk B = Algebra.trdeg K L :=
  ⟨hB.isAlgebraic_field, hB.cardinalMk_eq_trdeg⟩

/-- **Definition 5.1, closing sentence.** The elements of `L` that are algebraic over
`K` form a subfield, and every finite set generating `L` over `K` contains a
transcendence basis ([Lang, Thm. VIII.1.1]). -/
theorem definition_5_1_closing :
    (∃ E : IntermediateField K L, ∀ z : L, z ∈ E ↔ IsAlgebraic K z) ∧
      ∀ S : Set L, S.Finite → IntermediateField.adjoin K S = ⊤ →
        ∃ B ⊆ S, IsTranscendenceBasis K ((↑) : B → L) := by
  refine ⟨⟨algebraicClosure K L, fun z => mem_algebraicClosure_iff⟩, fun S _ hS => ?_⟩
  have : Algebra.IsAlgebraic (Algebra.adjoin K S) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, hS]
    exact ⟨fun z => ⟨Polynomial.X - Polynomial.C ⟨z, trivial⟩, Polynomial.X_sub_C_ne_zero _,
      by simp [Polynomial.aeval_def]⟩⟩
  exact exists_isTranscendenceBasis_subset S

/-- The relations of Definition 5.2(b) in the free `κ`-vector space `𝒢` on symbols
`⟨a⟩ = Finsupp.single a 1`: `⟨a+b⟩ - ⟨a⟩ - ⟨b⟩`, `⟨ab⟩ - a⟨b⟩ - b⟨a⟩`, `⟨c⟩` (`c ∈ K`). -/
def differentialRelations (K κ : Type*) [Field K] [Field κ] [Algebra K κ] :
    Submodule κ (κ →₀ κ) :=
  Submodule.span κ
    (((Set.range fun x : κ × κ ↦
        Finsupp.single (x.1 + x.2) 1 - Finsupp.single x.1 1 - Finsupp.single x.2 1) ∪
      Set.range fun x : κ × κ ↦
        Finsupp.single (x.1 * x.2) 1 - x.1 • Finsupp.single x.2 1 -
          x.2 • Finsupp.single x.1 1) ∪
      Set.range fun c : K ↦ Finsupp.single (algebraMap K κ c) 1)

/-- The printed relations span Mathlib's `KaehlerDifferential.kerTotal`. -/
theorem differentialRelations_eq_kerTotal :
    differentialRelations K L = KaehlerDifferential.kerTotal K L := by
  apply le_antisymm
  · rw [differentialRelations, Submodule.span_le]
    rintro _ ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨a, b⟩, rfl⟩) | ⟨c, rfl⟩)
    · have e : Finsupp.single (a + b) (1 : L) - Finsupp.single a 1 - Finsupp.single b 1 =
          -(Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single (a + b) 1) := by abel
      rw [SetLike.mem_coe]
      beta_reduce
      rw [e]
      exact Submodule.neg_mem _ (Submodule.subset_span (Or.inl (Or.inl ⟨(a, b), rfl⟩)))
    · have e : Finsupp.single (a * b) (1 : L) - a • Finsupp.single b 1 - b • Finsupp.single a 1 =
          -(Finsupp.single b a + Finsupp.single a b - Finsupp.single (a * b) 1) := by
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
        abel
      rw [SetLike.mem_coe]
      beta_reduce
      rw [e]
      exact Submodule.neg_mem _ (Submodule.subset_span (Or.inl (Or.inr ⟨(a, b), rfl⟩)))
    · exact Submodule.subset_span (Or.inr ⟨c, rfl⟩)
  · rw [KaehlerDifferential.kerTotal, Submodule.span_le]
    rintro _ ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨a, b⟩, rfl⟩) | ⟨c, rfl⟩)
    · have e : Finsupp.single a (1 : L) + Finsupp.single b 1 - Finsupp.single (a + b) 1 =
          -(Finsupp.single (a + b) 1 - Finsupp.single a 1 - Finsupp.single b 1) := by abel
      rw [SetLike.mem_coe]
      beta_reduce
      rw [e]
      exact Submodule.neg_mem _ (Submodule.subset_span (Or.inl (Or.inl ⟨(a, b), rfl⟩)))
    · have e : Finsupp.single b a + Finsupp.single a b - Finsupp.single (a * b) (1 : L) =
          -(Finsupp.single (a * b) 1 - a • Finsupp.single b 1 - b • Finsupp.single a 1) := by
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
        abel
      rw [SetLike.mem_coe]
      beta_reduce
      rw [e]
      exact Submodule.neg_mem _ (Submodule.subset_span (Or.inl (Or.inr ⟨(a, b), rfl⟩)))
    · exact Submodule.subset_span (Or.inr ⟨c, rfl⟩)

/-- **Definition 5.2(b).** `Ω_{κ/K}`, the quotient of the free module `𝒢` by the printed
relations, is Mathlib's `Ω[κ⁄K]`, with the class of `⟨a⟩` going to `da`. -/
theorem definition_5_2_b :
    ∃ e : ((L →₀ L) ⧸ differentialRelations K L) ≃ₗ[L] Ω[L⁄K],
      ∀ a : L, e (Submodule.Quotient.mk (Finsupp.single a 1)) = KaehlerDifferential.D K L a := by
  refine ⟨(Submodule.quotEquivOfEq _ _ differentialRelations_eq_kerTotal).trans
    (KaehlerDifferential.quotKerTotalEquiv K L), fun a ↦ ?_⟩
  simp [KaehlerDifferential.quotKerTotalEquiv]

/-- **Definition 5.2(c), first sentences.** A `K`-derivation `D` of `κ` induces the
`κ`-linear map `Ω_{κ/K} → κ`, `da ↦ D(a)`, and conversely a `κ`-linear map
`φ : Ω_{κ/K} → κ` gives the `K`-derivation `a ↦ φ(da)`; the two constructions are
inverse (`KaehlerDifferential.linearMapEquivDerivation`). -/
theorem definition_5_2_c_correspondence :
    ∃ e : (Ω[L⁄K] →ₗ[L] L) ≃ₗ[L] Derivation K L L,
      (∀ (φ : Ω[L⁄K] →ₗ[L] L) (a : L), e φ a = φ (KaehlerDifferential.D K L a)) ∧
        ∀ (D : Derivation K L L) (a : L), e.symm D (KaehlerDifferential.D K L a) = D a :=
  ⟨KaehlerDifferential.linearMapEquivDerivation K L, fun _ _ => rfl,
    fun D a => D.liftKaehlerDifferential_comp_D a⟩

/-- **Definition 5.2(c).** A basis `dβ_1, …, dβ_d` of `Ω_{κ/K}` has dual derivations
`D_k` with `D_k(β_l) = δ_{kl}`, namely `D_k = (dβ_k)^* ∘ d`. -/
theorem definition_5_2_c {ι : Type*} [DecidableEq ι] (β : ι → L)
    (b : Module.Basis ι L Ω[L⁄K]) (hb : ∀ l, b l = KaehlerDifferential.D K L (β l)) :
    ∃ D : ι → Derivation K L L, ∀ k' l, D k' (β l) = if k' = l then 1 else 0 := by
  -- `dβ_l` is the class of `⟨β_l⟩` (Definition 5.2(b)); `D_k` is the derivation
  -- of the coordinate functional `(dβ_k)^*` on `Ω_{κ/K}`.
  obtain ⟨e, he⟩ := definition_5_2_b (K := K) (L := L)
  obtain ⟨c, hc, -⟩ := definition_5_2_c_correspondence (K := K) (L := L)
  refine ⟨fun k' ↦ c (b.coord k'), fun k' l ↦ ?_⟩
  have hb' : ∀ l, b l = e (Submodule.Quotient.mk (Finsupp.single (β l) 1)) :=
    fun l ↦ (hb l).trans (he _).symm
  rw [hc, ← he, ← hb', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : k' = l
  · subst h; simp
  · simp [h, Ne.symm h]

end Definitions51to53

#print axioms zeroLocus_vanishingIdeal_of_isZariskiClosed
#print axioms mem_zeroLocus_sup_span_singleton
#print axioms definition_5_4_a
#print axioms definition_5_4_c
#print axioms definition_5_4_d
#print axioms definition_5_6
#print axioms definition_5_1_g_h
#print axioms definition_5_1_closing
#print axioms definition_5_2_c_correspondence
#print axioms differentialRelations_eq_kerTotal
#print axioms definition_5_2_b
#print axioms definition_5_2_c

end

end Stafford38.Paper.Section5
