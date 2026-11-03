module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.Algebra.Module.SpanRankOperations

@[expose] public section

/-!
# Dimension theory of finitely generated algebras over a field

* `trdeg_quotient_lt`: in a finitely generated domain `D` over a field `K`, a nonzero
  prime `𝔭` lowers the transcendence degree, `trdeg_K (D/𝔭) < trdeg_K D`.
* `ringKrullDim_eq_trdeg`: a finitely generated domain `A` over `K` has Krull
  dimension `trdeg_K A` (Noether normalization and going up for the lower bound,
  `trdeg_quotient_lt` along a chain of primes for the upper bound).
* `partialEvalChain`, `le_height_ker_aeval`: the maximal ideal of a point of `K^n`
  has height at least `n` in `K[x_1, …, x_n]`.
* `isDomain_of_spanFinrank_maximalIdeal_le`: a regular local ring is a domain.
-/

namespace Stafford38.Paper.Support

open MvPolynomial

noncomputable section

universe u

section Trdeg

variable {K : Type u} [Field K]

/-- **A nonzero prime lowers the transcendence degree.** Lift a transcendence basis of
`D/𝔭` to `D`; if `trdeg D ≤ trdeg D/𝔭`, the lift is a transcendence basis of `D`, so a
nonzero `a ∈ 𝔭` is algebraic over `K[z]` and `𝔭 ∩ K[z] ≠ 0`; but `K[z] → D/𝔭` is
injective. -/
theorem trdeg_quotient_lt {D : Type u} [CommRing D] [IsDomain D] [Algebra K D]
    [Algebra.FiniteType K D] (p : Ideal D) [p.IsPrime] (hp : p ≠ ⊥) :
    Algebra.trdeg K (D ⧸ p) < Algebra.trdeg K D := by
  classical
  have hfin : Algebra.trdeg K D < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  have : FaithfulSMul K (D ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective K (D ⧸ p)).2 (algebraMap K (D ⧸ p)).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K (D ⧸ p)
  by_contra hlt
  have hle : Algebra.trdeg K D ≤ Cardinal.mk s := by
    rw [hs.cardinalMk_eq_trdeg]
    exact not_lt.1 hlt
  let z : s → D := fun i ↦ (Ideal.Quotient.mk_surjective (i : D ⧸ p)).choose
  have hz : ∀ i, Ideal.Quotient.mk p (z i) = i := fun i ↦
    (Ideal.Quotient.mk_surjective (i : D ⧸ p)).choose_spec
  have hcomp : (Ideal.Quotient.mkₐ K p : D →ₐ[K] D ⧸ p) ∘ z = ((↑) : s → D ⧸ p) := by
    funext i
    exact hz i
  have hzi : AlgebraicIndependent K z :=
    AlgebraicIndependent.of_comp (Ideal.Quotient.mkₐ K p) (hcomp ▸ hs.1)
  have hzb : IsTranscendenceBasis K z := AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le hzi hfin hle
  have := hzb.isAlgebraic
  obtain ⟨a, hap, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hunder := Ideal.under_ne_bot_of_algebraic_mem
    (R := Algebra.adjoin K (Set.range z)) ha0 hap (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hunder
  obtain ⟨g, hg⟩ : (r : D) ∈ (MvPolynomial.aeval (R := K) z).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact r.2
  have hg0 : MvPolynomial.aeval ((↑) : s → D ⧸ p) g = 0 := by
    rw [← hcomp, show (⇑(Ideal.Quotient.mkₐ K p) ∘ z) = fun i ↦ Ideal.Quotient.mkₐ K p (z i)
      from rfl, ← MvPolynomial.comp_aeval_apply]
    change Ideal.Quotient.mk p ((MvPolynomial.aeval (R := K) z).toRingHom g) = 0
    rw [hg]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hr
  have hg' : g = 0 := (algebraicIndependent_iff.1 hs.1) g hg0
  apply hr0
  apply Subtype.ext
  rw [← hg, hg', map_zero]
  rfl

/-- The transcendence degree of a quotient is at most that of the ring. -/
theorem trdeg_quotient_le {A : Type u} [CommRing A] [Algebra K A] (p : Ideal A) :
    Algebra.trdeg K (A ⧸ p) ≤ Algebra.trdeg K A :=
  trdeg_le_of_surjective (Ideal.Quotient.mkₐ K p) Ideal.Quotient.mk_surjective

/-- A domain and its fraction field have the same transcendence degree. -/
theorem trdeg_fractionRing (D : Type u) [CommRing D] [IsDomain D] [Algebra K D] :
    Algebra.trdeg K (FractionRing D) = Algebra.trdeg K D := by
  have : FaithfulSMul K D :=
    (faithfulSMul_iff_algebraMap_injective K D).2 (algebraMap K D).injective
  have : FaithfulSMul D (FractionRing D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective D (FractionRing D))
  have : Algebra.IsAlgebraic D (FractionRing D) :=
    IsLocalization.isAlgebraic (R := D) (S := FractionRing D) (nonZeroDivisors D)
  rw [← trdeg_add_eq (R := K) (S := D) (A := FractionRing D),
    trdeg_eq_zero (R := D) (A := FractionRing D), add_zero]

/-- For primes `𝔭 < 𝔮` of a finitely generated `K`-algebra,
`trdeg_K (A/𝔮) < trdeg_K (A/𝔭)`, as natural numbers. -/
theorem trdeg_quotient_toNat_lt {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] {p q : Ideal A} [p.IsPrime] [q.IsPrime] (hpq : p < q) :
    (Algebra.trdeg K (A ⧸ q)).toNat < (Algebra.trdeg K (A ⧸ p)).toNat := by
  classical
  let q' : Ideal (A ⧸ p) := q.map (Ideal.Quotient.mk p)
  have hker : RingHom.ker (Ideal.Quotient.mk p) ≤ q := by
    rw [Ideal.mk_ker]
    exact hpq.le
  have : q'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hq' : q' ≠ ⊥ := by
    obtain ⟨a, haq, hap⟩ := IsConcreteLE.exists_of_lt hpq
    intro h
    apply hap
    have : Ideal.Quotient.mk p a ∈ q' := Ideal.mem_map_of_mem _ haq
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have hlt := trdeg_quotient_lt (K := K) q' hq'
  have he : Algebra.trdeg K ((A ⧸ p) ⧸ q') = Algebra.trdeg K (A ⧸ q) :=
    (DoubleQuot.quotQuotEquivQuotOfLEₐ K hpq.le).trdeg_eq
  rw [he] at hlt
  have hfin : Algebra.trdeg K (A ⧸ p) < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  exact Cardinal.toNat_strictMonoOn (hlt.trans hfin) hfin hlt

end Trdeg

section Chain

variable {K : Type u} [Field K] {n : ℕ}

/-- Substitute `x_i = y_i` for `i < j`. -/
def partialEval (y : Fin n → K) (j : ℕ) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval fun i ↦ if (i : ℕ) < j then C (y i) else X i

theorem partialEval_comp (y : Fin n → K) {j k : ℕ} (hjk : j ≤ k) :
    (partialEval y k).comp (partialEval y j) = partialEval y k := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [partialEval, AlgHom.comp_apply, aeval_X]
  by_cases hij : (i : ℕ) < j
  · have hik : (i : ℕ) < k := lt_of_lt_of_le hij hjk
    simp [hij, hik]
  · simp [hij]

theorem ker_partialEval_mono (y : Fin n → K) {j k : ℕ} (hjk : j ≤ k) :
    RingHom.ker (partialEval y j) ≤ RingHom.ker (partialEval y k) := by
  intro g hg
  rw [RingHom.mem_ker] at hg ⊢
  rw [← partialEval_comp y hjk, AlgHom.comp_apply, hg, map_zero]

theorem ker_partialEval_lt (y : Fin n → K) {j : ℕ} (hj : j < n) :
    RingHom.ker (partialEval y j) < RingHom.ker (partialEval y (j + 1)) := by
  refine lt_of_le_of_ne (ker_partialEval_mono y (Nat.le_succ j)) fun h ↦ ?_
  have hmem : X (⟨j, hj⟩ : Fin n) - C (y ⟨j, hj⟩) ∈ RingHom.ker (partialEval y (j + 1)) := by
    rw [RingHom.mem_ker]
    simp [partialEval]
  rw [← h, RingHom.mem_ker] at hmem
  simp only [partialEval, map_sub, aeval_X, lt_irrefl, ite_false, aeval_C,
    MvPolynomial.algebraMap_eq] at hmem
  have := congrArg (MvPolynomial.eval fun _ ↦ y ⟨j, hj⟩ + 1) hmem
  simp at this

theorem ker_partialEval_zero (y : Fin n → K) : RingHom.ker (partialEval y 0) = ⊥ := by
  have : partialEval y 0 = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [partialEval]
  rw [this]
  exact (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id

theorem ker_partialEval_self (y : Fin n → K) :
    RingHom.ker (partialEval y n) = RingHom.ker (MvPolynomial.aeval (R := K) y) := by
  have : partialEval y n = (Algebra.ofId K (MvPolynomial (Fin n) K)).comp (aeval y) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [partialEval, MvPolynomial.algebraMap_eq]
  ext g
  rw [RingHom.mem_ker, RingHom.mem_ker, this, AlgHom.comp_apply]
  simp only [Algebra.ofId_apply, MvPolynomial.algebraMap_eq]
  exact MvPolynomial.C_eq_zero

theorem isPrime_ker_partialEval (y : Fin n → K) (j : ℕ) :
    (RingHom.ker (partialEval y j)).IsPrime :=
  RingHom.ker_isPrime _

/-- The chain `0 = 𝔭_0 < 𝔭_1 < ⋯ < 𝔭_n = 𝔪_y`, `𝔭_j = (x_1 - y_1, …, x_j - y_j)`. -/
def partialEvalChain (y : Fin n → K) : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) K)) where
  length := n
  toFun j := ⟨RingHom.ker (partialEval y j), isPrime_ker_partialEval y j⟩
  step j := ker_partialEval_lt y j.2

theorem partialEvalChain_head (y : Fin n → K) :
    ((partialEvalChain y).head).asIdeal = ⊥ :=
  ker_partialEval_zero y

theorem partialEvalChain_last (y : Fin n → K) :
    ((partialEvalChain y).last).asIdeal = RingHom.ker (MvPolynomial.aeval (R := K) y) :=
  ker_partialEval_self y

/-- The maximal ideal of a point of `K^n` has height at least `n`. -/
theorem le_height_ker_aeval (y : Fin n → K) :
    (n : ℕ∞) ≤ (RingHom.ker (MvPolynomial.aeval (R := K) y)).height := by
  have : (RingHom.ker (MvPolynomial.aeval (R := K) y)).IsPrime := RingHom.ker_isPrime _
  rw [show RingHom.ker (MvPolynomial.aeval (R := K) y) =
    ((partialEvalChain y).last).asIdeal from (partialEvalChain_last y).symm,
    PrimeSpectrum.height_eq_orderHeight]
  exact Order.length_le_height_last (p := partialEvalChain y)

end Chain

section KrullTrdeg

variable {K : Type u} [Field K]

/-- `dim A ≤ trdeg_K A` for a finitely generated `K`-algebra: along a chain of primes
the transcendence degree of the quotients drops strictly. -/
theorem ringKrullDim_le_trdeg (A : Type u) [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ringKrullDim A ≤ ((Algebra.trdeg K A).toNat : WithBot ℕ∞) := by
  have hfinA : Algebra.trdeg K A < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  let tr : PrimeSpectrum A → ℕ := fun p ↦ (Algebra.trdeg K (A ⧸ p.asIdeal)).toNat
  have hstep : ∀ k (hk : k ≤ l.length),
      tr (l ⟨k, Nat.lt_succ_of_le hk⟩) + k ≤ tr (l 0) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have hlt : l ⟨k, by omega⟩ < l ⟨k + 1, by omega⟩ := l.strictMono (by simp)
      have h2 := trdeg_quotient_toNat_lt (K := K) (A := A) (p := (l ⟨k, by omega⟩).asIdeal)
        (q := (l ⟨k + 1, by omega⟩).asIdeal) hlt
      simp only [tr] at h1 ⊢
      omega
  have hlen := hstep l.length le_rfl
  have h0 : tr (l 0) ≤ (Algebra.trdeg K A).toNat :=
    Cardinal.toNat_le_toNat (trdeg_quotient_le _) hfinA
  have : l.length ≤ (Algebra.trdeg K A).toNat := by omega
  exact_mod_cast this

/-- `trdeg_K A ≤ dim A` for a finitely generated domain: Noether normalization
`K[z_1, …, z_s] ⊆ A` with `s = trdeg_K A`, and the chain of `partialEvalChain` lifts to `A`
by going up. -/
theorem trdeg_le_ringKrullDim (A : Type u) [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ((Algebra.trdeg K A).toNat : WithBot ℕ∞) ≤ ringKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin s) K) A :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : FaithfulSMul K (MvPolynomial (Fin s) K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K _).injective
  have htr : Algebra.trdeg K A = s := by
    rw [← trdeg_add_eq (R := K) (S := MvPolynomial (Fin s) K) (A := A), MvPolynomial.trdeg_of_isDomain,
      trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := A)]
    simp
  rw [htr, Cardinal.toNat_natCast]
  let l := partialEvalChain (K := K) (fun _ : Fin s ↦ (0 : K))
  have : (⊥ : Ideal A).LiesOver (RelSeries.head l).asIdeal := by
    refine ⟨?_⟩
    rw [partialEvalChain_head, Ideal.under]
    exact (Ideal.comap_bot_of_injective (algebraMap (MvPolynomial (Fin s) K) A) hinj).symm
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l (⊥ : Ideal A)
  have := Order.LTSeries.length_le_krullDim L
  rw [hL] at this
  exact this

/-- **Krull dimension equals transcendence degree** for a finitely generated domain over a
field. -/
theorem ringKrullDim_eq_trdeg (A : Type u) [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ringKrullDim A = ((Algebra.trdeg K A).toNat : WithBot ℕ∞) :=
  le_antisymm (ringKrullDim_le_trdeg A) (trdeg_le_ringKrullDim A)

end KrullTrdeg

section Regular

open IsLocalRing

theorem withBot_natCast_le_of_add_one_le {a : ℕ} {D : WithBot ℕ∞}
    (h : (a : WithBot ℕ∞) + 1 ≤ D + 1) : (a : WithBot ℕ∞) ≤ D := by
  induction D using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe d =>
      have : a + 1 ≤ d + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : a ≤ d)

/-- If `x ∈ 𝔪 ∖ 𝔪²`, then `𝔪_{R/(x)}` needs one generator fewer than `𝔪`: extend the class
of `x` to a basis of `𝔪/𝔪²` and lift it to generators of `𝔪` containing `x`. -/
theorem spanFinrank_maximalIdeal_quotient_add_one_le {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  set 𝔪 := maximalIdeal R
  let v : CotangentSpace R := 𝔪.toCotangent ⟨x, hx⟩
  have hv : v ≠ 0 := fun h ↦ hx2 ((Ideal.toCotangent_eq_zero 𝔪 ⟨x, hx⟩).1 h)
  have hli : LinearIndepOn (ResidueField R) id ({v} : Set (CotangentSpace R)) :=
    (linearIndepOn_singleton_iff (ResidueField R)).2 hv
  let S : Set (CotangentSpace R) := hli.extend (Set.subset_univ _)
  let b := Module.Basis.extend hli
  have hvS : v ∈ S := hli.subset_extend _ rfl
  have hSfin : S.Finite := Set.toFinite S
  have hrank : 𝔪.spanFinrank = S.ncard := by
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, Module.finrank_eq_nat_card_basis b,
      Nat.card_coe_set_eq]
  let σ : CotangentSpace R → 𝔪 := fun w ↦
    if w = v then ⟨x, hx⟩ else (Ideal.toCotangent_surjective 𝔪 w).choose
  have hσ : ∀ w, 𝔪.toCotangent (σ w) = w := by
    intro w
    by_cases h : w = v
    · simp only [σ, h, ite_true]; rfl
    · simp only [σ, h, ite_false]; exact (Ideal.toCotangent_surjective 𝔪 w).choose_spec
  let T : Set 𝔪 := σ '' S
  have hTspan : Submodule.span R T = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff]
    have : 𝔪.toCotangent '' T = S := by
      rw [Set.image_image]
      simp [hσ]
    rw [this]
    have := b.span_eq
    rwa [Module.Basis.range_extend] at this
  have h𝔪 : 𝔪 = Ideal.span (Subtype.val '' T) := by
    have h := congrArg (Submodule.map 𝔪.subtype) hTspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h
    exact h.symm
  have hmax : maximalIdeal (R ⧸ Ideal.span {x}) =
      Ideal.span ((Ideal.Quotient.mk _) '' (Subtype.val '' (T \ {σ v}))) := by
    rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    change 𝔪.map _ = _
    conv_lhs => rw [h𝔪]
    rw [Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      by_cases htv : t = σ v
      · have : Ideal.Quotient.mk (Ideal.span {x}) (t : R) = 0 := by
          rw [htv, Ideal.Quotient.eq_zero_iff_mem]
          simp only [σ, ite_true]
          exact Ideal.mem_span_singleton_self x
        rw [this]
        exact Ideal.zero_mem _
      · exact Ideal.subset_span ⟨t, ⟨t, ⟨ht, htv⟩, rfl⟩, rfl⟩
    · apply Ideal.span_mono
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ⟨t, ht.1, rfl⟩, rfl⟩
  have hTfin : T.Finite := hSfin.image σ
  have hσvT : σ v ∈ T := ⟨v, hvS, rfl⟩
  have h1 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤
      ((Ideal.Quotient.mk (Ideal.span {x})) '' (Subtype.val '' (T \ {σ v}))).ncard := by
    rw [hmax]
    exact Submodule.spanFinrank_span_le_ncard_of_finite
      (((hTfin.sdiff).image _).image _)
  have h2 : ((Ideal.Quotient.mk (Ideal.span {x})) '' (Subtype.val '' (T \ {σ v}))).ncard ≤
      (T \ {σ v}).ncard :=
    (Set.ncard_image_le ((hTfin.sdiff).image _)).trans (Set.ncard_image_le hTfin.sdiff)
  have h3 : (T \ {σ v}).ncard + 1 = T.ncard := Set.ncard_sdiff_singleton_add_one hσvT hTfin
  have h4 : T.ncard ≤ S.ncard := Set.ncard_image_le hSfin
  omega

/-- **A regular local ring is a domain.** If `𝔪` is generated by at most `dim R` elements,
then `R` is a domain.  Induction on the number of generators: choose `x ∈ 𝔪` outside `𝔪²`
and outside the minimal primes; `R/(x)` is again regular, hence a domain, so `(x)` is prime;
a minimal prime `𝔮 ⊆ (x)` satisfies `𝔮 = x𝔮`, so `𝔮 = 0` by Nakayama. -/
theorem isDomain_of_spanFinrank_maximalIdeal_le :
    ∀ (μ : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (maximalIdeal R).spanFinrank = μ → (μ : WithBot ℕ∞) ≤ ringKrullDim R → IsDomain R := by
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
  intro R _ _ _ hμ hdim
  set 𝔪 := maximalIdeal R
  have hfg : 𝔪.FG := IsNoetherian.noetherian 𝔪
  have hjac : 𝔪 ≤ (⊥ : Ideal R).jacobson := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  rcases Nat.eq_zero_or_pos μ with h0 | hpos
  · have hbot : 𝔪 = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 (hμ.trans h0)
    exact (IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot).isDomain
  -- `𝔪 ⊄ 𝔪²`
  have hm2 : ¬ 𝔪 ≤ 𝔪 ^ 2 := by
    intro h
    have : 𝔪 = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔪 𝔪 hfg
      (by rw [smul_eq_mul, ← pow_two]; exact h) hjac
    rw [this, Submodule.spanFinrank_bot] at hμ
    omega
  -- `𝔪` is not a minimal prime
  have hdimpos : (0 : WithBot ℕ∞) < ringKrullDim R :=
    lt_of_lt_of_le (by exact_mod_cast hpos) hdim
  have hmin : ∀ q ∈ minimalPrimes R, ¬ 𝔪 ≤ q := by
    intro q hq hle
    have hqp : q.IsPrime := hq.1.1
    have heq : q = 𝔪 := (IsLocalRing.le_maximalIdeal hqp.ne_top).antisymm hle
    have h0 : 𝔪.height = 0 := Ideal.height_eq_zero_iff.2 (heq ▸ hq)
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h0] at hdimpos
    exact lt_irrefl _ hdimpos
  -- prime avoidance
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  let s : Finset (Ideal R) := insert (𝔪 ^ 2) hfin.toFinset
  have hp : ∀ i ∈ s, i ≠ 𝔪 ^ 2 → i ≠ 𝔪 ^ 2 → (id i).IsPrime := by
    intro i hi hia _
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact absurd rfl hia
    · exact (hfin.mem_toFinset.1 hi).1.1
  have hnot := (Ideal.subset_union_prime (s := s) (f := id) (𝔪 ^ 2) (𝔪 ^ 2) hp (I := 𝔪)).not.2
    (by
      rintro ⟨i, hi, hle⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hm2 hle
      · exact hmin i (hfin.mem_toFinset.1 hi) hle)
  obtain ⟨x, hx𝔪, hxU⟩ := Set.not_subset.1 hnot
  have hx2 : x ∉ 𝔪 ^ 2 := fun h ↦ hxU (Set.mem_biUnion (Finset.mem_coe.2
    (Finset.mem_insert_self _ _)) h)
  have hxq : ∀ q ∈ minimalPrimes R, x ∉ q := fun q hq h ↦ hxU (Set.mem_biUnion
    (Finset.mem_coe.2 (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hq))) h)
  -- `R/(x)` is regular of smaller embedding dimension
  have hne : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal x).1 hx𝔪
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.2 hne
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hμ' := spanFinrank_maximalIdeal_quotient_add_one_le hx𝔪 hx2
  have hdim' : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact Ideal.height_le_ringKrullDim_quotient_add_one hx𝔪
  set μ' := (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank
  have hle : (μ' : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {x}) := by
    have h1 : ((μ' + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 :=
      le_trans (by exact_mod_cast hμ ▸ hμ') (hdim.trans hdim')
    push_cast at h1
    exact withBot_natCast_le_of_add_one_le h1
  have hμlt : μ' < μ := by
    have h := hμ'
    rw [show maximalIdeal R = 𝔪 from rfl, hμ] at h
    omega
  have hdom := ih μ' hμlt (R ⧸ Ideal.span {x}) rfl hle
  have hprime : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 hdom
  -- a minimal prime inside `(x)` is zero
  obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ Ideal.span {x})
  have hqp : q.IsPrime := hq.1.1
  have hxq' : x ∉ q := hxq q hq
  have hqle : q ≤ Ideal.span {x} • q := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (hqx ha)
    have hc : c ∈ q := (hqp.mem_or_mem ha).resolve_right hxq'
    rw [mul_comm]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hc
  have hq0 : q = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ q
    (IsNoetherian.noetherian q) hqle
    (le_trans (Ideal.span_le.2 (Set.singleton_subset_iff.2 hx𝔪)) hjac)
  have hbot : (⊥ : Ideal R).IsPrime := hq0 ▸ hqp
  have : IsDomain (R ⧸ (⊥ : Ideal R)) := (Ideal.Quotient.isDomain_iff_prime _).2 hbot
  exact (RingEquiv.quotientBot R).toMulEquiv.isDomain_iff.1 this

end Regular

end

#print axioms trdeg_quotient_lt
#print axioms trdeg_quotient_le
#print axioms trdeg_fractionRing
#print axioms trdeg_quotient_toNat_lt
#print axioms partialEval_comp
#print axioms ker_partialEval_mono
#print axioms ker_partialEval_lt
#print axioms ker_partialEval_zero
#print axioms ker_partialEval_self
#print axioms isPrime_ker_partialEval
#print axioms partialEvalChain_head
#print axioms partialEvalChain_last
#print axioms le_height_ker_aeval
#print axioms ringKrullDim_le_trdeg
#print axioms trdeg_le_ringKrullDim
#print axioms ringKrullDim_eq_trdeg
#print axioms withBot_natCast_le_of_add_one_le
#print axioms spanFinrank_maximalIdeal_quotient_add_one_le
#print axioms isDomain_of_spanFinrank_maximalIdeal_le

end Stafford38.Paper.Support
