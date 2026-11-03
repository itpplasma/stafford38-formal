module

public import Stafford38.Paper.Section5
public import Stafford38.Paper.Section5.Definitions
public import Stafford38.Paper.Section5.SmoothLocus
public import Stafford38.Paper.Section2.Symplectic
public import Stafford38.Geometry.GeneralCoisotropicSets
public import Stafford38.Characteristic.PostScalarExtensionPoisson

@[expose] public section

/-!
# Theorem 5.8 and its proof (Subsection 5.3), paragraph by paragraph

Notation as in the paper.  `X = K^n` with `n = m`, a point `(y, ξ)` of
`T*X = K^n × (K^n)*` is `Sum.elim y ξ : PhaseVar m → K`, closed subsets of
`T*X` are zero loci `V_K(L)` of ideals of `K[x, ξ] = SymbolRing K m`, and the
paper's coordinate `x_1` is index `⟨0, hm⟩`.  In the proof `J = I(W)`,
`B = J ∩ K[x]` is `exclusionBaseIdeal W` (the contraction along
`baseLift : K[x] → K[x, ξ]`), `Y = V_K(B)`, `df_y = differentialAt y f` and
`φ(t) = g(y, t df_y)` is `fibreLinePolynomial y (differentialAt y f) g`.
Involutivity of `W` is Definition 2.10 (`{I(W), I(W)} ⊆ I(W)`), the predicate
`PostScalarExtensionPoisson.IsInvolutive` of `I(W)`.

The steps `step_*` state the paragraphs of the printed proof in order;
`theorem_5_8` chains them and closes with `theorem_5_7_i_printed`.
-/

namespace Stafford38.Paper.Section5

open Stafford38.Characteristic
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ConormalPrincipalOpenDensity
open Stafford38.Geometry.FibreConicalVanishingIdeal
open Stafford38.Geometry.GeneralCoisotropicSets
open Stafford38.Geometry.GeneralConormalContainment
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.SmoothAffineConormal

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {m : ℕ}

/-- `B = I(W) ∩ K[x]`. -/
abbrev exclusionBaseIdeal (W : Set (PhaseVar m → k)) :
    Ideal (MvPolynomial (Fin m) k) :=
  (MvPolynomial.vanishingIdeal k W).comap (baseLift (k := k) (n := m))

omit [IsAlgClosed k] [CharZero k] in
/-- `d` is `K`-linear: every element of `span_K {df_y : f ∈ I}` is `dh_y` for
one `h ∈ I`. -/
theorem exists_mem_differentialAt_eq_of_mem_span
    (I : Ideal (MvPolynomial (Fin m) k)) (y ξ : Fin m → k)
    (hξ : ξ ∈ Submodule.span k (Set.range fun f : I => differentialAt y f.1)) :
    ∃ h ∈ I, differentialAt y h = ξ := by
  induction hξ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      exact ⟨f.1, f.2, rfl⟩
  | zero =>
      exact ⟨0, I.zero_mem, by funext i; simp [differentialAt]⟩
  | add x z _ _ hx hz =>
      obtain ⟨f, hf, rfl⟩ := hx
      obtain ⟨g, hg, rfl⟩ := hz
      exact ⟨f + g, I.add_mem hf hg, by funext i; simp [differentialAt]⟩
  | smul c x _ hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact ⟨MvPolynomial.C c * f, I.mul_mem_left _ hf,
        by funext i; simp [differentialAt]⟩

/-- Paragraph "Because `W` is fibre-conical": the `ξ`-homogeneous components
`g_d` of every `g ∈ J` lie in `J`.  The proof is the paper's: `g(y, aξ) =
Σ a^d g_d(y, ξ)` vanishes for all `a ∈ K^×`, so every coefficient does. -/
theorem step_homogeneous_components
    (W : Set (PhaseVar m → k)) (hcone : IsFibreConical W) :
    ∀ g ∈ MvPolynomial.vanishingIdeal k W, ∀ d : ℕ,
      (DirectSum.decompose (orderDecomposition (k := k) (n := m)) g d :
        SymbolRing k m) ∈ MvPolynomial.vanishingIdeal k W :=
  fun _ hg d => vanishingIdeal_isHomogeneous_of_isFibreConical W hcone d hg

/-- Same paragraph: `g_0 ∈ B`, hence `g(y, 0) = g_0(y) = 0` for `y ∈ Y = V_K(B)`,
and `Y × {0} ⊆ V_K(J) = W` because `W` is closed. -/
theorem step_zero_section
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W) :
    ∀ y ∈ MvPolynomial.zeroLocus k (exclusionBaseIdeal W),
      Sum.elim y (0 : Fin m → k) ∈ W := by
  intro y hy
  have hhom : (MvPolynomial.vanishingIdeal k W).IsHomogeneous
      (orderDecomposition (k := k) (n := m)) :=
    fun d _ hg => step_homogeneous_components W hcone _ hg d
  have hzero := zeroSection_commonZero_of_isHomogeneous
    (MvPolynomial.vanishingIdeal k W) hhom y hy
  have hpoint : Sum.elim y (0 : Fin m → k) = zeroSectionPoint y := by
    funext i; rcases i with i | i <;> rfl
  rw [← zeroLocus_vanishingIdeal_of_algebraic_closed W hclosed, hpoint]
  exact hzero

/-- Same paragraph: `Y = π(W)`. -/
theorem step_projection
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W) :
    {y : Fin m → k | ∃ ξ : Fin m → k, Sum.elim y ξ ∈ W} =
      MvPolynomial.zeroLocus k (exclusionBaseIdeal W) := by
  ext y
  constructor
  · rintro ⟨ξ, hξ⟩ f hf
    have h := hf (Sum.elim y ξ) hξ
    simpa [baseLift, MvPolynomial.eval_rename, Function.comp_def] using h
  · intro hy
    exact ⟨0, step_zero_section W hclosed hcone y hy⟩

/-- Paragraph "Lastly": `W ∩ π⁻¹(H) = ∅` gives `Y ∩ H = ∅`. -/
theorem step_Y_avoids_H
    (hm : 0 < m) (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hH : W ∩ {q | q (.inl ⟨0, hm⟩) = 0} = ∅) :
    ∀ y ∈ MvPolynomial.zeroLocus k (exclusionBaseIdeal W), y ⟨0, hm⟩ ≠ 0 := by
  intro y hy hy0
  have hmem : Sum.elim y (0 : Fin m → k) ∈ W ∩ {q | q (.inl ⟨0, hm⟩) = 0} :=
    ⟨step_zero_section W hclosed hcone y hy, hy0⟩
  rw [hH] at hmem
  exact hmem

omit [IsAlgClosed k] [CharZero k] in
/-- Paragraph "For the next argument": for `f ∈ B`,
`H_f g = Σ_i ∂f/∂x_i ∂g/∂ξ_i = {f, g}` (the bracket of Definition 2.9,
`Section2.poisson`), and involutivity gives `H_f^m g ∈ J`
for all `g ∈ J`, `m ≥ 0`. -/
theorem step_hamiltonian
    (W : Set (PhaseVar m → k))
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (f : MvPolynomial (Fin m) k) (hf : f ∈ exclusionBaseIdeal W)
    (g : SymbolRing k m) (hg : g ∈ MvPolynomial.vanishingIdeal k W) :
    Stafford38.Paper.Section2.poisson k (baseLift f) g =
        ∑ i : Fin m, baseLift (MvPolynomial.pderiv i f) *
          MvPolynomial.pderiv (Sum.inr i : PhaseVar m) g ∧
      ∀ j : ℕ, hamiltonIter f j g ∈ MvPolynomial.vanishingIdeal k W := by
  refine ⟨?_, fun j => ?_⟩
  · rw [Stafford38.Paper.Section2.poisson_eq]
    simp [poissonBracket, pderiv_baseLift_base, pderiv_baseLift_fibre]
  · induction j with
    | zero => exact hg
    | succ j hj => exact hinv _ hf _ hj

/-- Same paragraph: for `y ∈ Y`, `f ∈ B`, `g ∈ J`, the polynomial
`φ(t) = g(y, t df_y)` satisfies `φ^{(j)}(0) = H_f^j g(y, 0) = 0` for all `j`. -/
theorem step_phi_derivatives
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (y : Fin m → k) (hy : y ∈ MvPolynomial.zeroLocus k (exclusionBaseIdeal W))
    (f : MvPolynomial (Fin m) k) (hf : f ∈ exclusionBaseIdeal W)
    (g : SymbolRing k m) (hg : g ∈ MvPolynomial.vanishingIdeal k W) (j : ℕ) :
    Polynomial.eval 0 ((Polynomial.derivative^[j])
      (fibreLinePolynomial y (differentialAt y f) g)) = 0 := by
  rw [iterate_derivative_fibreLinePolynomial, eval_zero_fibreLinePolynomial]
  have hpoint : zeroSectionPoint y = Sum.elim y (0 : Fin m → k) := by
    funext i; rcases i with i | i <;> rfl
  rw [hpoint]
  exact (step_hamiltonian W hinv f hf g hg).2 j _
    (step_zero_section W hclosed hcone y hy)

/-- Same paragraph: since `char K = 0`, `φ^{(j)}(0) = j! c_j = 0` forces
`φ = 0`, so `(y, t df_y) ∈ V_K(J) = W` for every `t ∈ K`. -/
theorem step_line_mem
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (y : Fin m → k) (hy : y ∈ MvPolynomial.zeroLocus k (exclusionBaseIdeal W))
    (f : MvPolynomial (Fin m) k) (hf : f ∈ exclusionBaseIdeal W) (t : k) :
    Sum.elim y (t • differentialAt y f) ∈ W := by
  rw [← zeroLocus_vanishingIdeal_of_algebraic_closed W hclosed]
  intro g hg
  have hphi : fibreLinePolynomial y (differentialAt y f) g = 0 :=
    polynomial_eq_zero_of_eval_iterate_derivative_zero _
      (step_phi_derivatives W hclosed hcone hinv y hy f hf g hg)
  have h := eval_fibreLinePolynomial y (differentialAt y f) g t
  rw [hphi, Polynomial.eval_zero] at h
  have hpt : Sum.elim y (t • differentialAt y f) =
      Sum.elim y (fun i => t * differentialAt y f i) := rfl
  rw [hpt]
  exact h.symm

/-- Same paragraph, last sentence: `{y} × span{df_y : f ∈ B} ⊆ W` for `y ∈ Y`,
since `Σ c_a df_a = d(Σ c_a f_a)` with `Σ c_a f_a ∈ B`, at `t = 1`. -/
theorem step_span_mem
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (y : Fin m → k) (hy : y ∈ MvPolynomial.zeroLocus k (exclusionBaseIdeal W))
    (ξ : Fin m → k)
    (hξ : ξ ∈ Submodule.span k
      (Set.range fun f : exclusionBaseIdeal W => differentialAt y f.1)) :
    Sum.elim y ξ ∈ W := by
  obtain ⟨f, hf, rfl⟩ := exists_mem_differentialAt_eq_of_mem_span _ y ξ hξ
  simpa using step_line_mem W hclosed hcone hinv y hy f hf 1

/-- Paragraph "Since `V_K(B) = Y = π(W) ≠ ∅`": `B` is radical and proper (by
`step_projection`), has finitely many minimal primes `𝔮_1, …, 𝔮_r`, at least
one, and `B = ⋂ 𝔮_i`. -/
theorem step_minimal_primes
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W) (hne : W.Nonempty) :
    (exclusionBaseIdeal W).IsRadical ∧
      (exclusionBaseIdeal W).minimalPrimes.Finite ∧
      sInf (exclusionBaseIdeal W).minimalPrimes = exclusionBaseIdeal W ∧
      (exclusionBaseIdeal W).minimalPrimes.Nonempty := by
  have hrad : (exclusionBaseIdeal W).IsRadical :=
    (vanishingIdeal_isRadical W).comap _
  have hproper : exclusionBaseIdeal W ≠ ⊤ := by
    intro htop
    obtain ⟨q, hq⟩ := hne
    have hy : (fun i => q (.inl i)) ∈ MvPolynomial.zeroLocus k (exclusionBaseIdeal W) := by
      rw [← step_projection W hclosed hcone]
      refine ⟨fun i => q (.inr i), ?_⟩
      have hsplit : Sum.elim (fun i => q (.inl i)) (fun i => q (.inr i)) = q := by
        funext i; cases i <;> rfl
      rwa [hsplit]
    have := hy 1 (htop ▸ trivial)
    simp at this
  refine ⟨hrad, Ideal.finite_minimalPrimes_of_isNoetherianRing _ _, ?_,
    Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes hproper)⟩
  rw [Ideal.sInf_minimalPrimes, hrad.radical]

/-- Same paragraph: for a minimal prime `𝔮` of `B`, `Y_0 = V_K(𝔮)` is
nonempty, closed and irreducible (`𝔮` prime), `𝔮 = I(Y_0)`, `Y_0 ⊆ Y` and
`Y_0 ∩ H = ∅`. -/
theorem step_component
    (hm : 0 < m) (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hH : W ∩ {q | q (.inl ⟨0, hm⟩) = 0} = ∅)
    (𝔮 : Ideal (MvPolynomial (Fin m) k))
    (h𝔮 : 𝔮 ∈ (exclusionBaseIdeal W).minimalPrimes) :
    𝔮.IsPrime ∧ (MvPolynomial.zeroLocus k 𝔮).Nonempty ∧
      MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k 𝔮) = 𝔮 ∧
      MvPolynomial.zeroLocus k 𝔮 ⊆
        MvPolynomial.zeroLocus k (exclusionBaseIdeal W) ∧
      ∀ y ∈ MvPolynomial.zeroLocus k 𝔮, y ⟨0, hm⟩ ≠ 0 := by
  have hprime : 𝔮.IsPrime := h𝔮.1.1
  have hI : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k 𝔮) = 𝔮 :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus 𝔮
  have hsub : MvPolynomial.zeroLocus k 𝔮 ⊆
      MvPolynomial.zeroLocus k (exclusionBaseIdeal W) :=
    MvPolynomial.zeroLocus_anti_mono h𝔮.1.2
  refine ⟨hprime, ?_, hI, hsub, fun y hy =>
    step_Y_avoids_H hm W hclosed hcone hH y (hsub hy)⟩
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  rw [hempty, MvPolynomial.vanishingIdeal_empty] at hI
  exact hprime.ne_top hI.symm

omit [IsAlgClosed k] [CharZero k] in
/-- Paragraph "Furthermore": there is a separator `s ∉ 𝔮` with `s𝔮 ⊆ B`,
`s = s_2 ⋯ s_r` with `s_i ∈ 𝔮_i ∖ 𝔮`. -/
theorem step_separator
    (W : Set (PhaseVar m → k))
    (𝔮 : Ideal (MvPolynomial (Fin m) k))
    (hrad : (exclusionBaseIdeal W).IsRadical)
    (h𝔮 : 𝔮 ∈ (exclusionBaseIdeal W).minimalPrimes) :
    ∃ s ∉ 𝔮, ∀ h ∈ 𝔮, s * h ∈ exclusionBaseIdeal W := by
  classical
  set B := exclusionBaseIdeal W
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (Fin m) k) B
  set T := hfin.toFinset.erase 𝔮 with hT
  have hchoice : ∀ Q ∈ T, ∃ s ∈ Q, s ∉ 𝔮 := by
    intro Q hQ
    rw [hT, Finset.mem_erase, hfin.mem_toFinset] at hQ
    by_contra hcon
    push Not at hcon
    exact hQ.1 (le_antisymm hcon (h𝔮.2 hQ.2.1 hcon))
  choose s hsQ hsP using hchoice
  refine ⟨∏ Q ∈ T.attach, s Q.1 Q.2, ?_, ?_⟩
  · intro hs
    obtain ⟨Q, -, hQ⟩ := (h𝔮.1.1.prod_mem_iff).1 hs
    exact hsP Q.1 Q.2 hQ
  · intro h hh
    rw [← hrad.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro Q hQ
    by_cases hQP : Q = 𝔮
    · subst hQP
      exact Ideal.mul_mem_left _ _ hh
    · have hQT : Q ∈ T := by
        rw [hT, Finset.mem_erase, hfin.mem_toFinset]
        exact ⟨hQP, hQ⟩
      refine Ideal.mul_mem_right _ _ ?_
      exact Ideal.mem_of_dvd _
        (Finset.dvd_prod_of_mem (fun Q : T ↦ s Q.1 Q.2)
          (Finset.mem_attach _ ⟨Q, hQT⟩))
        (hsQ Q hQT)

/-- Same paragraph: for `h ∈ 𝔮` and `y ∈ Y_0 ∩ {s ≠ 0}`, `(y, dh_y) ∈ W`,
because `d(sh)_y = s(y) dh_y` with `sh ∈ B`, and `W` is fibre-conical. -/
theorem step_dh_on_open
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (𝔮 : Ideal (MvPolynomial (Fin m) k))
    (h𝔮 : 𝔮 ∈ (exclusionBaseIdeal W).minimalPrimes)
    (s : MvPolynomial (Fin m) k)
    (hs : ∀ h ∈ 𝔮, s * h ∈ exclusionBaseIdeal W)
    (h : MvPolynomial (Fin m) k) (hh : h ∈ 𝔮)
    (y : Fin m → k) (hy : y ∈ MvPolynomial.zeroLocus k 𝔮)
    (hsy : MvPolynomial.eval y s ≠ 0) :
    Sum.elim y (differentialAt y h) ∈ W := by
  have hyY : y ∈ MvPolynomial.zeroLocus k (exclusionBaseIdeal W) :=
    MvPolynomial.zeroLocus_anti_mono h𝔮.1.2 hy
  have hhy : MvPolynomial.eval y h = 0 := hy h hh
  have hd : differentialAt y (s * h) = MvPolynomial.eval y s • differentialAt y h := by
    funext i
    simp [differentialAt, hhy]
  have hsh : Sum.elim y (differentialAt y (s * h)) ∈ W :=
    step_span_mem W hclosed hcone hinv y hyY _
      (Submodule.subset_span ⟨⟨s * h, hs h hh⟩, rfl⟩)
  rw [hd] at hsh
  have := ((definition_5_6 W).1 hcone y _ ⟨hsh, rfl⟩ (MvPolynomial.eval y s)⁻¹
    (inv_ne_zero hsy)).1
  rwa [smul_smul, inv_mul_cancel₀ hsy, one_smul] at this

/-- Same paragraph: `(y, dh_y) ∈ W` for all `y ∈ Y_0`.  For `g ∈ J`,
`G(x) = g(x, dh_x)` vanishes on `Y_0 ∩ {s ≠ 0}`, so `sG ∈ I(Y_0) = 𝔮`, and
`G ∈ 𝔮` as `s ∉ 𝔮`. -/
theorem step_dh_on_component
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (𝔮 : Ideal (MvPolynomial (Fin m) k))
    (h𝔮 : 𝔮 ∈ (exclusionBaseIdeal W).minimalPrimes)
    (s : MvPolynomial (Fin m) k) (hs𝔮 : s ∉ 𝔮)
    (hs : ∀ h ∈ 𝔮, s * h ∈ exclusionBaseIdeal W)
    (h : MvPolynomial (Fin m) k) (hh : h ∈ 𝔮)
    (y : Fin m → k) (hy : y ∈ MvPolynomial.zeroLocus k 𝔮) :
    Sum.elim y (differentialAt y h) ∈ W := by
  rw [← zeroLocus_vanishingIdeal_of_algebraic_closed W hclosed]
  intro g hg
  have hG : gradientGraphSubstitution h g ∈ 𝔮 := by
    apply mem_of_vanishes_on_principal_open 𝔮 h𝔮.1.1 hs𝔮
    intro z hz hsz
    rw [eval_gradientGraphSubstitution]
    exact hg _ (step_dh_on_open W hclosed hcone hinv 𝔮 h𝔮 s hs h hh z hz hsz)
  have h0 : MvPolynomial.eval y (gradientGraphSubstitution h g) = 0 := hy _ hG
  rw [eval_gradientGraphSubstitution] at h0
  exact h0

/-- Same paragraph: `{y} × span{dh_y : h ∈ 𝔮} ⊆ W` for every `y ∈ Y_0`. -/
theorem step_span_component
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (𝔮 : Ideal (MvPolynomial (Fin m) k))
    (h𝔮 : 𝔮 ∈ (exclusionBaseIdeal W).minimalPrimes)
    (s : MvPolynomial (Fin m) k) (hs𝔮 : s ∉ 𝔮)
    (hs : ∀ h ∈ 𝔮, s * h ∈ exclusionBaseIdeal W)
    (y : Fin m → k) (hy : y ∈ MvPolynomial.zeroLocus k 𝔮)
    (ξ : Fin m → k)
    (hξ : ξ ∈ Submodule.span k (Set.range fun h : 𝔮 => differentialAt y h.1)) :
    Sum.elim y ξ ∈ W := by
  obtain ⟨h, hh, rfl⟩ := exists_mem_differentialAt_eq_of_mem_span 𝔮 y ξ hξ
  exact step_dh_on_component W hclosed hcone hinv 𝔮 h𝔮 s hs𝔮 hs h hh y hy

/-- Same paragraph: at smooth points `y` of `Y_0`, `{y} × N*_y Y_0 ⊆ W`, with
`N*_y Y_0 = span{df_y : f ∈ 𝔮}` (Definition 5.4(c), `𝔮 = I(Y_0)`). -/
theorem step_conormal_subset
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (𝔮 : Ideal (MvPolynomial (Fin m) k))
    (h𝔮 : 𝔮 ∈ (exclusionBaseIdeal W).minimalPrimes)
    (s : MvPolynomial (Fin m) k) (hs𝔮 : s ∉ 𝔮)
    (hs : ∀ h ∈ 𝔮, s * h ∈ exclusionBaseIdeal W)
    (y : Fin m → k) (hy : SmoothAffinePoint 𝔮 y)
    (ξ : Fin m → k) (hξ : coordinateCovector ξ ∈ affineConormalSpace y 𝔮) :
    Sum.elim y ξ ∈ W :=
  step_span_component W hclosed hcone hinv 𝔮 h𝔮 s hs𝔮 hs y
    (smoothAffinePoint_mem_zeroLocus 𝔮 hy) ξ ((definition_5_4_c 𝔮 y ξ).1 hξ)

/-- Same paragraph: `P`, which depends on `ξ` only, vanishes on `N(Y_0)`
(Definition 5.4(d)). -/
theorem step_P_vanishes_on_conormal_cone
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (𝔮 : Ideal (MvPolynomial (Fin m) k))
    (h𝔮 : 𝔮 ∈ (exclusionBaseIdeal W).minimalPrimes)
    (s : MvPolynomial (Fin m) k) (hs𝔮 : s ∉ 𝔮)
    (hs : ∀ h ∈ 𝔮, s * h ∈ exclusionBaseIdeal W)
    (P : MvPolynomial (Fin m) k)
    (hPW : ∀ q ∈ W, MvPolynomial.eval (fun i => q (.inr i)) P = 0) :
    P ∈ MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection 𝔮) := by
  intro ξ hξ
  obtain ⟨y, hy, hspan⟩ := (definition_5_4_d 𝔮 ξ).1 hξ
  have hyξ := step_conormal_subset W hclosed hcone hinv 𝔮 h𝔮 s hs𝔮 hs y hy ξ
    ((definition_5_4_c 𝔮 y ξ).2 hspan)
  simpa using hPW _ hyξ

/-- `P` vanishes on the printed cone `N(Y_0) = ⋃_{y ∈ Y_sm} N*_y Y_0` over the
Jacobian smooth locus (Definition 5.4).  `step_P_vanishes_on_conormal_cone`
argues over Mathlib's smooth points, which are exactly the Jacobian smooth
points (`definition_5_4_b_iff`), so the two cones are equal
(`conormalCone_paper_eq`). -/
theorem step_P_vanishes_on_N (𝔮 : Ideal (MvPolynomial (Fin m) k)) (hprime : 𝔮.IsPrime)
    (P : MvPolynomial (Fin m) k)
    (hP : P ∈ MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection 𝔮)) :
    ∀ ξ ∈ conormalCone ⟨𝔮, hprime⟩, MvPolynomial.eval ξ P = 0 := by
  rw [conormalCone_paper_eq ⟨𝔮, hprime⟩]
  intro ξ hξ
  simpa using (MvPolynomial.mem_vanishingIdeal_iff.1 hP) ξ hξ

/-- Final sentence: `Y_0` is nonempty, closed, irreducible and avoids `H`, and
`P` vanishes on `N(Y_0)`, so Theorem 5.7(i) gives `P(1, 0, …, 0) = 0`. -/
theorem step_theorem_5_7_applies
    (hm : 0 < m) (𝔮 : Ideal (MvPolynomial (Fin m) k)) (hprime : 𝔮.IsPrime)
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k 𝔮, y ⟨0, hm⟩ ≠ 0)
    (P : MvPolynomial (Fin m) k)
    (hP : ∀ ξ ∈ conormalCone ⟨𝔮, hprime⟩, MvPolynomial.eval ξ P = 0) :
    MvPolynomial.eval (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) P = 0 :=
  theorem_5_7_i_printed hm ⟨𝔮, hprime⟩ havoid P hP

/-- **Theorem 5.8.** Let `K` be algebraically closed of characteristic zero and
`W ⊆ T*X` Zariski closed, fibre-conical and involutive.  If
`P ∈ K[ξ_1, …, ξ_n]` with `P(1, 0, …, 0) ≠ 0` vanishes on `W` and
`W ∩ π⁻¹(H) = ∅`, then `W = ∅`.  Proved along Subsection 5.3. -/
theorem theorem_5_8
    (hm : 0 < m) (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m), W = MvPolynomial.zeroLocus k L)
    (hcone : IsFibreConical W)
    (hinv : IsInvolutive (MvPolynomial.vanishingIdeal k W))
    (P : MvPolynomial (Fin m) k)
    (haxis : MvPolynomial.eval
      (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) P ≠ 0)
    (hPW : ∀ q ∈ W, MvPolynomial.eval (fun i => q (.inr i)) P = 0)
    (hH : W ∩ {q | q (.inl ⟨0, hm⟩) = 0} = ∅) :
    W = ∅ := by
  -- Suppose `W ≠ ∅`.
  by_contra hne
  have hW : W.Nonempty := Set.nonempty_iff_ne_empty.2 hne
  -- `B` is radical with a minimal prime `𝔮`; `Y_0 = V_K(𝔮)`.
  obtain ⟨hrad, -, -, 𝔮, h𝔮⟩ := step_minimal_primes W hclosed hcone hW
  obtain ⟨hprime, -, -, -, havoid⟩ := step_component hm W hclosed hcone hH 𝔮 h𝔮
  -- The separator `s`, then `P` vanishes on `N(Y_0)`.
  obtain ⟨s, hs𝔮, hs⟩ := step_separator W 𝔮 hrad h𝔮
  have hPN := step_P_vanishes_on_conormal_cone W hclosed hcone hinv 𝔮 h𝔮 s hs𝔮 hs P hPW
  -- Theorem 5.7(i) contradicts `P(1, 0, …, 0) ≠ 0`.
  exact haxis (step_theorem_5_7_applies hm 𝔮 hprime havoid P
    (step_P_vanishes_on_N 𝔮 hprime P hPN))

#print axioms exists_mem_differentialAt_eq_of_mem_span
#print axioms step_homogeneous_components
#print axioms step_zero_section
#print axioms step_projection
#print axioms step_Y_avoids_H
#print axioms step_hamiltonian
#print axioms step_phi_derivatives
#print axioms step_line_mem
#print axioms step_span_mem
#print axioms step_minimal_primes
#print axioms step_component
#print axioms step_separator
#print axioms step_dh_on_open
#print axioms step_dh_on_component
#print axioms step_span_component
#print axioms step_conormal_subset
#print axioms step_P_vanishes_on_conormal_cone
#print axioms step_P_vanishes_on_N
#print axioms step_theorem_5_7_applies
#print axioms theorem_5_8

end

end Stafford38.Paper.Section5
