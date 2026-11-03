module

public import Stafford38.Paper.Section4.TangentialFiniteness
public import AlgebraicAnalysis.Module.BaseLocalizedKoszulPositivity

@[expose] public section

/-!
# Lemma 4.10: the strict inequality `ℓ(U_𝔮) > ℓ(V_𝔮)`

Paragraphs of the printed proof: Gabber's theorem keeps `x₁` out of the minimal
primes of `J = √Ann M`; this persists after localizing at `S = T∖𝔮`; the stable
power kernel `K_∞`; its two elementary facts; `ℓ(K_∞/x₁K_∞) = ℓ(V_𝔮)`; the split
`ℓ(U_𝔮) = ℓ(V_𝔮) + ℓ(Ẽ/x₁Ẽ)` with `Ẽ = M_𝔮/K_∞`; `Ẽ/x₁Ẽ ≠ 0` by Nakayama.

The middle paragraphs are stated for a base ring `R` (where lengths are
measured, `R = T_𝔮`), a Noetherian coefficient algebra `C` (`C = k[x,ξ]_𝔮`), a
finite `C`-module `E` (`E = M_𝔮`) and `x ∈ C`, with `f = x·` viewed `R`-linearly.
In Lean `Ẽ/x₁Ẽ` is `E ⧸ (K_∞ ⊔ x₁E)`, which is the same module by the third
isomorphism theorem (`Submodule.quotientQuotientEquivQuotientSup`).
-/

namespace Stafford38.Paper.Section4

open scoped Pointwise
open Stafford38.Characteristic
open Stafford38.Characteristic.NoncharacteristicMinimalPrime
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open AlgebraicAnalysis
open AlgebraicAnalysis.BaseLocalizationModuleComparison
open AlgebraicAnalysis.LocalizedKernelCokernelEquivalences
open AlgebraicAnalysis.LocalizedMinimalSupportAvoidance

open Stafford38.Paper.Section3 (IsMonicNormalForm isPBWMonicAt_of_isMonicNormalForm)

noncomputable section

section Generic

variable {R C E : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [AddCommGroup E] [Module C E] [Module R E] [IsScalarTower R C E]

/-- **`K_∞`.**  The chain `ker f ⊆ ker f² ⊆ ⋯` stabilizes (`E` is Noetherian), at
`K_∞ = ker f^m = ker f^{m+1}`; the layers `ker f^{i+1}/ker f^i` inject into `V`
via `v ↦ x₁^i v`, so `K_∞` has finite length with `V`. -/
theorem step_4_10_stable_kernel [IsNoetherianRing C] [Module.Finite C E] (x : C)
    (hV : IsFiniteLength R (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R))) :
    ∃ m : ℕ,
      LinearMap.ker (((LinearMap.lsmul C E x).restrictScalars R) ^ m) =
          LinearMap.ker (((LinearMap.lsmul C E x).restrictScalars R) ^ (m + 1)) ∧
        IsFiniteLength R (LinearMap.ker (((LinearMap.lsmul C E x).restrictScalars R) ^ m)) := by
  let fC : Module.End C E := LinearMap.lsmul C E x
  let fR : Module.End R E := fC.restrictScalars R
  obtain ⟨m, hm⟩ := PrincipalKoszulPositivity.exists_stable_kernel_power_smul (E := E) x
  have hpow : ∀ j, fR ^ j = (fC ^ j).restrictScalars R := by
    intro j
    induction j with
    | zero => ext z; simp
    | succ j ih =>
        rw [pow_succ, pow_succ, ih]
        ext z
        simp [fR, LinearMap.restrictScalars_apply, Module.End.mul_apply]
  refine ⟨m, ?_, PrincipalKoszulFiniteTorsion.isFiniteLength_kernel_power fR hV m⟩
  change LinearMap.ker (fR ^ m) = LinearMap.ker (fR ^ (m + 1))
  rw [hpow, hpow, LinearMap.ker_restrictScalars, LinearMap.ker_restrictScalars]
  exact congrArg (Submodule.restrictScalars R) hm

/-- **The two elementary facts.**  For `K_∞ = ker f^m = ker f^{m+1}`:
`f⁻¹K_∞ = K_∞` and `K_∞ ∩ fE = f(K_∞)`. -/
theorem step_4_10_two_facts (f : Module.End R E) (m : ℕ)
    (hstable : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (m + 1))) :
    (LinearMap.ker (f ^ m)).comap f = LinearMap.ker (f ^ m) ∧
      LinearMap.ker (f ^ m) ⊓ LinearMap.range f = (LinearMap.ker (f ^ m)).map f := by
  have hcomap : (LinearMap.ker (f ^ m)).comap f = LinearMap.ker (f ^ m) := by
    ext z
    rw [Submodule.mem_comap]
    change (f ^ m) (f z) = 0 ↔ (f ^ m) z = 0
    rw [← Module.End.mul_apply, (Commute.self_pow f m).eq.symm, Module.End.mul_apply]
    simpa [Module.End.pow_apply, Function.iterate_succ_apply'] using
      congrArg (fun K : Submodule R E ↦ z ∈ K) hstable.symm
  refine ⟨hcomap, le_antisymm ?_ ?_⟩
  · rintro w ⟨hwK, v, rfl⟩
    have hv : v ∈ (LinearMap.ker (f ^ m)).comap f := hwK
    rw [hcomap] at hv
    exact ⟨v, hv, rfl⟩
  · rintro w ⟨v, hv, rfl⟩
    refine ⟨?_, v, rfl⟩
    have : v ∈ (LinearMap.ker (f ^ m)).comap f := by rw [hcomap]; exact hv
    exact this

/-- **`ℓ(K_∞/x₁K_∞) = ℓ(V)`.**  For an endomorphism `φ` of a finite-length module,
additivity along `0 → ker φ → L → φL → 0` and `0 → φL → L → L/φL → 0` gives
`ℓ(ker φ) = ℓ(L/φL)`; for `φ = f|_{K_∞}`, `ker φ = ker f` as `ker f ⊆ K_∞`. -/
theorem step_4_10_kernel_length (f : Module.End R E) (K : Submodule R E)
    (hK : IsFiniteLength R K) (hcomap : K.comap f = K) :
    Module.length R (K ⧸ LinearMap.range (f.restrict (p := K) (q := K)
        (fun z hz => show z ∈ K.comap f from hcomap.symm ▸ hz))) =
      Module.length R (LinearMap.ker f) := by
  let fK : Module.End R K := f.restrict (fun z hz => show z ∈ K.comap f from hcomap.symm ▸ hz)
  have hparts := isFiniteLength_iff_isNoetherian_isArtinian.mp hK
  let : IsNoetherian R K := hparts.1
  let : IsArtinian R K := hparts.2
  have hkerle : LinearMap.ker f ≤ K := by
    intro z hz
    rw [← hcomap]
    change f z ∈ K
    rw [LinearMap.mem_ker.mp hz]
    exact K.zero_mem
  have hker : Module.length R (LinearMap.ker fK) = Module.length R (LinearMap.ker f) := by
    have hk : LinearMap.ker fK = (LinearMap.ker f).comap K.subtype := by
      simp [fK, LinearMap.ker_restrict]
    rw [hk]
    exact (Submodule.comapSubtypeEquivOfLe hkerle).length_eq
  have hsource := (definition_4_6 (T := R) (M := K)).2 (LinearMap.ker fK).subtype
    fK.rangeRestrict (Submodule.subtype_injective _)
    (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict fK))
    (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  have htarget := (definition_4_6 (T := R) (M := K)).2 (LinearMap.range fK).subtype
    (LinearMap.range fK).mkQ (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  rw [← hker]
  apply ENat.add_left_injective_of_ne_top (Module.length_ne_top (R := R) (M := LinearMap.range fK))
  change Module.length R (K ⧸ LinearMap.range fK) + Module.length R (LinearMap.range fK) =
    Module.length R (LinearMap.ker fK) + Module.length R (LinearMap.range fK)
  rw [add_comm (Module.length R (K ⧸ LinearMap.range fK)), ← htarget]
  exact hsource

/-- **The split `ℓ(U) = ℓ(V) + ℓ(Ẽ/x₁Ẽ)`.**  `E/fE → Ẽ/fẼ` is onto with kernel
`(K_∞ + fE)/fE ≅ K_∞/(K_∞ ∩ fE) = K_∞/fK_∞`; additivity and
`ℓ(K_∞/fK_∞) = ℓ(V)` give the split. -/
theorem step_4_10_length_split (f : Module.End R E) (K : Submodule R E)
    (hK : IsFiniteLength R K) (hcomap : K.comap f = K)
    (hinter : K ⊓ LinearMap.range f = K.map f) :
    Module.length R (E ⧸ LinearMap.range f) =
      Module.length R (LinearMap.ker f) + Module.length R (E ⧸ (K ⊔ LinearMap.range f)) := by
  have hstable : ∀ z ∈ K, f z ∈ K := fun z hz =>
    show z ∈ K.comap f from hcomap.symm ▸ hz
  let fK : Module.End R K := f.restrict hstable
  have hpre : (LinearMap.range f).comap K.subtype = LinearMap.range fK := by
    ext z
    constructor
    · intro hz
      have hz' : (z : E) ∈ K.map f := hinter ▸ ⟨z.2, hz⟩
      obtain ⟨w, hw, hwz⟩ := hz'
      exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w.val, rfl⟩
  let i : (K ⧸ LinearMap.range fK) →ₗ[R] (E ⧸ LinearMap.range f) :=
    (LinearMap.range fK).mapQ (LinearMap.range f) K.subtype hpre.ge
  let j : (E ⧸ LinearMap.range f) →ₗ[R] (E ⧸ (K ⊔ LinearMap.range f)) :=
    (LinearMap.range f).mapQ (K ⊔ LinearMap.range f) LinearMap.id le_sup_right
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot]
    dsimp [i]
    rw [Submodule.ker_mapQ, hpre, Submodule.mkQ_map_self]
  have hj : Function.Surjective j := by
    rw [← LinearMap.range_eq_top]
    simp [j, Submodule.range_mapQ]
  have hexact : Function.Exact i j := by
    rw [LinearMap.exact_iff]
    simp [i, j, Submodule.range_mapQ, Submodule.ker_mapQ, Submodule.map_sup,
      Submodule.mkQ_map_self]
  have hsum := (definition_4_6 (T := R) (M := E ⧸ LinearMap.range f)).2 i j hi hj hexact
  rw [hsum, step_4_10_kernel_length f K hK hcomap]

/-- **Nakayama paragraph: `Ẽ/x₁Ẽ ≠ 0`.**  Pick `𝔓` in the support of `E/x₁E ≠ 0`
and `𝔭' ⊆ 𝔓` minimal in `Supp E`; `x₁ ∉ 𝔭'`, so `K_∞` vanishes at `𝔭'` and
`Ẽ_{𝔭'} = E_{𝔭'} ≠ 0`; hence `Ẽ_𝔓 ≠ 0`, and as `x₁ ∈ 𝔓`, Nakayama gives
`(Ẽ/x₁Ẽ)_𝔓 ≠ 0`. -/
theorem step_4_10_residual_nonzero [IsNoetherianRing C] [Module.Finite C E] (x : C)
    (havoid : ∀ p ∈ (Module.annihilator C E).minimalPrimes, x ∉ p)
    (hU : Nontrivial (QuotSMulTop x E)) (m : ℕ) :
    Nontrivial (E ⧸ (LinearMap.ker (((LinearMap.lsmul C E x).restrictScalars R) ^ m) ⊔
      LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R))) := by
  let fC : Module.End C E := LinearMap.lsmul C E x
  let fR : Module.End R E := fC.restrictScalars R
  -- `𝔓 ∈ Supp(E/x₁E)` and a minimal `𝔭' ⊆ 𝔓` of `Supp E`
  obtain ⟨P, hPquot⟩ := Module.nonempty_support_of_nontrivial (R := C) (M := QuotSMulTop x E)
  have hPE : P ∈ Module.support C E := by
    have h := hPquot
    rw [Module.support_quotSMulTop] at h
    exact h.1
  obtain ⟨p, hpmin, hpP⟩ := Ideal.exists_minimalPrimes_le (I := Module.annihilator C E)
    (J := P.asIdeal) (Module.mem_support_iff_of_finite.mp hPE)
  let p' : PrimeSpectrum C := ⟨p, hpmin.1.1⟩
  have hp' : p' ∈ Module.support C E := Module.mem_support_iff_of_finite.mpr hpmin.1.2
  have hnonzeroC : Nontrivial (E ⧸ (LinearMap.ker (fC ^ m) ⊔ LinearMap.range fC)) :=
    StableTorsionResidualSupport.residual_nontrivial_of_support x m p' P hp' hpP
      (havoid p hpmin) hPquot
  have hpow : ∀ j, fR ^ j = (fC ^ j).restrictScalars R := by
    intro j
    induction j with
    | zero => ext z; simp
    | succ j ih =>
        rw [pow_succ, pow_succ, ih]
        ext z
        simp [fR, LinearMap.restrictScalars_apply, Module.End.mul_apply]
  have hPR : LinearMap.ker (fR ^ m) ⊔ LinearMap.range fR =
      (LinearMap.ker (fC ^ m) ⊔ LinearMap.range fC).restrictScalars R := by
    rw [hpow m]
    simp only [LinearMap.ker_restrictScalars, Submodule.restrictScalars_sup]
    rfl
  apply Submodule.Quotient.nontrivial_iff.mpr
  intro htop
  apply (Submodule.Quotient.nontrivial_iff.mp hnonzeroC)
  apply (Submodule.restrictScalars_eq_top_iff R C E).mp
  change LinearMap.ker (fR ^ m) ⊔ LinearMap.range fR = ⊤ at htop
  rw [← hPR, htop]

/-- The length comparison over a base ring, assembled from the paragraphs above:
`ℓ(U) = ℓ(V) + ℓ(Ẽ/x₁Ẽ) > ℓ(V)`. -/
theorem step_4_10_core [IsNoetherianRing C] [Module.Finite C E] (x : C)
    (havoid : ∀ p ∈ (Module.annihilator C E).minimalPrimes, x ∉ p)
    (hU : Nontrivial (QuotSMulTop x E))
    (hV : IsFiniteLength R (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R))) :
    Module.length R (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R)) >
      Module.length R (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R)) := by
  let f : Module.End R E := (LinearMap.lsmul C E x).restrictScalars R
  obtain ⟨m, hstable, hK⟩ := step_4_10_stable_kernel x hV
  obtain ⟨hcomap, hinter⟩ := step_4_10_two_facts f m hstable
  have hsplit := step_4_10_length_split f _ hK hcomap hinter
  have hres := step_4_10_residual_nonzero (R := R) x havoid hU m
  have hpos : 0 < Module.length R (E ⧸ (LinearMap.ker (f ^ m) ⊔ LinearMap.range f)) :=
    Module.length_pos
  change Module.length R (E ⧸ LinearMap.range f) > Module.length R (LinearMap.ker f)
  rw [hsplit]
  have hVtop : Module.length R (LinearMap.ker f) ≠ ⊤ := Module.length_ne_top_iff.mpr hV
  simpa [add_comm] using ENat.lt_add_left hVtop hpos

/-- **Localizing at `S = T∖𝔮`.**  `M_𝔮 = S⁻¹M` over `T_𝔮` is the coefficient
localization `k[x,ξ]_𝔮 = S⁻¹k[x,ξ]` acting on `S⁻¹M`; there `U_𝔮 = M_𝔮/x₁M_𝔮 ≠ 0`
(`𝔮 ∈ Supp_T U`) and `V_𝔮 = ker(x₁ on M_𝔮)`, so `step_4_10_core` applies. -/
theorem step_4_10_localized [IsNoetherianRing C] [Module.Finite C E] (x : C)
    (q : PrimeSpectrum R)
    (hqmem : q ∈ Module.support R
      (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R)))
    (hkerfinite : IsFiniteLength (Localization q.asIdeal.primeCompl)
      (LocalizedModule q.asIdeal.primeCompl
        (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R))))
    (havoid : ∀ Q ∈ (Module.annihilator
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))
        (LocalizedModule (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl) E)).minimalPrimes,
      algebraMap C (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)) x ∉ Q) :
    Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl
          (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R))) >
      Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl
          (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R))) := by
  let S : Submonoid R := q.asIdeal.primeCompl
  let SC : Submonoid C := Algebra.algebraMapSubmonoid C S
  let fC : Module.End C E := LinearMap.lsmul C E x
  let fR : Module.End R E := fC.restrictScalars R
  -- compare the base localization `M_𝔮 = S⁻¹M` with the coefficient localization
  let : Module (Localization S) (LocalizedModule SC E) :=
    Module.compHom _ (algebraMap (Localization S) (Localization SC))
  let : IsScalarTower (Localization S) (Localization SC) (LocalizedModule SC E) :=
    IsScalarTower.of_compHom (Localization S) (Localization SC) (LocalizedModule SC E)
  let e : LocalizedModule S E ≃ₗ[Localization S] LocalizedModule SC E :=
    localizedModuleComparison S
  let gR : Module.End (Localization S) (LocalizedModule S E) := localizedMap S fR
  let y : Localization SC := algebraMap C (Localization SC) x
  let gC : Module.End (Localization SC) (LocalizedModule SC E) :=
    LinearMap.lsmul (Localization SC) (LocalizedModule SC E) y
  have heq (z : LocalizedModule S E) : e (gR z) = gC (e z) := by
    rw [show e (gR z) = LocalizedModule.map SC fC (e z) by
      exact localizedModuleComparison_natural S fC z]
    induction e z using LocalizedModule.induction_on with
    | _ m s => simp [gC, y, fC, LocalizedModule.smul'_mk]
  let ek : LinearMap.ker gR ≃ₗ[Localization S]
      LinearMap.ker (gC.restrictScalars (Localization S)) :=
    LinearEquiv.ofBijective
      (e.toLinearMap.domRestrict (LinearMap.ker gR) |>.codRestrict
        (LinearMap.ker (gC.restrictScalars (Localization S))) (fun z => by
          exact LinearMap.mem_ker.mpr (by simpa using (heq z).symm)))
      (by
        constructor
        · intro a b hab
          exact Subtype.ext (e.injective (congrArg Subtype.val hab))
        · intro z
          refine ⟨⟨e.symm z, ?_⟩, Subtype.ext (e.apply_symm_apply z)⟩
          exact LinearMap.mem_ker.mpr (e.injective (by
            rw [heq]
            simpa using z.property)))
  have herange : Submodule.map e.toLinearMap (LinearMap.range gR) =
      LinearMap.range (gC.restrictScalars (Localization S)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨e a, by simpa using (heq a).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨gR (e.symm a), ⟨e.symm a, rfl⟩, ?_⟩
      simpa using heq (e.symm a)
  let ec : (LocalizedModule S E ⧸ LinearMap.range gR) ≃ₗ[Localization S]
      (LocalizedModule SC E ⧸ LinearMap.range (gC.restrictScalars (Localization S))) :=
    Submodule.Quotient.equiv _ _ e herange
  -- `𝔮 ∈ Supp_T U`, so `U_𝔮 = M_𝔮/x₁M_𝔮 ≠ 0`
  have hnontrivBase : Nontrivial (LocalizedModule S (E ⧸ LinearMap.range fR)) := by
    exact Module.mem_support_iff.mp hqmem
  have hnontrivCokerR : Nontrivial (LocalizedModule S E ⧸ LinearMap.range gR) :=
    not_subsingleton_iff_nontrivial.mp (by
      intro hs
      have : Subsingleton (LocalizedModule S (E ⧸ LinearMap.range fR)) :=
        (localizedCokernelEquiv S fR).toEquiv.subsingleton_congr.mpr hs
      exact not_subsingleton_iff_nontrivial.mpr hnontrivBase this)
  have hnontrivCokerC : Nontrivial
      (LocalizedModule SC E ⧸ LinearMap.range (gC.restrictScalars (Localization S))) :=
    not_subsingleton_iff_nontrivial.mp (by
      intro hs
      exact not_subsingleton_iff_nontrivial.mpr hnontrivCokerR
        (ec.toEquiv.subsingleton_congr.mpr hs))
  have hrange : LinearMap.range gC =
      y • (⊤ : Submodule (Localization SC) (LocalizedModule SC E)) := by
    ext z
    rw [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and]
    rfl
  have hnontrivQuot : Nontrivial (QuotSMulTop y (LocalizedModule SC E)) := by
    change Nontrivial (LocalizedModule SC E ⧸
      y • (⊤ : Submodule (Localization SC) (LocalizedModule SC E)))
    rw [← hrange]
    exact hnontrivCokerC
  have hkbase : IsFiniteLength (Localization S) (LinearMap.ker gR) :=
    (localizedKernelEquiv S fR).isFiniteLength hkerfinite
  have hkfinite : IsFiniteLength (Localization S)
      (LinearMap.ker (gC.restrictScalars (Localization S))) :=
    ek.isFiniteLength hkbase
  -- the strict inequality over `T_𝔮`, from the paragraphs above
  have hpos := step_4_10_core (R := Localization S) (C := Localization SC)
    (E := LocalizedModule SC E) y havoid hnontrivQuot hkfinite
  have h1 : Module.length (Localization S) (LocalizedModule S (E ⧸ LinearMap.range fR)) =
      Module.length (Localization S)
        (LocalizedModule SC E ⧸ LinearMap.range (gC.restrictScalars (Localization S))) :=
    (localizedCokernelEquiv S fR).length_eq.trans ec.length_eq
  have hek : Module.length (Localization S) (LinearMap.ker gR) =
      Module.length (Localization S) (LinearMap.ker (gC.restrictScalars (Localization S))) := by
    exact ek.length_eq
  have h2 : Module.length (Localization S) (LocalizedModule S (LinearMap.ker fR)) =
      Module.length (Localization S) (LinearMap.ker (gC.restrictScalars (Localization S))) :=
    (localizedKernelEquiv S fR).length_eq.trans hek
  change Module.length (Localization S) (LocalizedModule S (LinearMap.ker fR)) <
    Module.length (Localization S) (LocalizedModule S (E ⧸ LinearMap.range fR))
  rw [h1, h2]
  exact hpos


end Generic

section Canonical

variable {k : Type*} [Field k] [CharZero k] [Algebra ℚ k] {n N : ℕ}
  {d : PresentedWeyl k (n + 1)}

attribute [local instance] Characteristic.CanonicalKoszulContradiction.gradedModule
  Characteristic.CanonicalKoszulContradiction.coefficientAlgebra
  Characteristic.CanonicalKoszulContradiction.coefficientTower

omit [Algebra ℚ k] in
/-- **Gabber paragraph.**  `J = √Ann M` is involutive (Gabber), so are its minimal
primes `𝔭`; if `x₁ ∈ 𝔭`, the iterated brackets `{x₁, …{x₁, P}}` are the
`ξ₁`-derivatives of `P ∈ 𝔭` and the `N`-th is `N! ≠ 0`, so `x₁ ∉ 𝔭`. -/
theorem step_4_10_gabber (hN : 0 < N) (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    ∀ P ∈ (Module.annihilator (Symbol k n) (GrQ k n N d)).minimalPrimes,
      symbolCoordinate k n ∉ P :=
  fun _ hP => canonical_minimalPrime_mem_of_normalCoordinate_false d hN hd hP

omit [Algebra ℚ k] in
/-- **Localization paragraph.**  With `S = T∖𝔮` and `k[x,ξ]_𝔮 = S⁻¹k[x,ξ]`, the
minimal primes of `Ann(M_𝔮) = S⁻¹Ann(M)` are `S⁻¹𝔭` for minimal primes `𝔭` of
`J`, so they do not contain `x₁`. -/
theorem step_4_10_localized_avoid (hN : 0 < N)
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) (S : Submonoid (Tangential k n)) :
    ∀ Q ∈ (Module.annihilator (Localization (Algebra.algebraMapSubmonoid (Symbol k n) S))
        (LocalizedModule (Algebra.algebraMapSubmonoid (Symbol k n) S) (GrQ k n N d))).minimalPrimes,
      algebraMap (Symbol k n) (Localization (Algebra.algebraMapSubmonoid (Symbol k n) S))
        (symbolCoordinate k n) ∉ Q :=
  localized_minimalPrime_avoids _ _ (step_4_10_gabber hN hd)

omit [Algebra ℚ k] in
/-- **Lemma 4.10.** For every minimal prime `𝔮` of `Supp_T U`,
`ℓ_{T_𝔮}(U_𝔮) > ℓ_{T_𝔮}(V_𝔮)`, for `d̃` in the form (3.1) with `N ≥ 1`. -/
theorem lemma_4_10 (hN : 0 < N) (hform : IsMonicNormalForm k N d)
    (q : PrimeSpectrum (Tangential k n))
    (hqmem : q ∈ Module.support (Tangential k n) (cokernelU k n N d))
    (hqmin : ∀ p ∈ Module.support (Tangential k n) (cokernelU k n N d),
      p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal) :
    Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl (cokernelU k n N d)) >
      Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl (kernelV k n N d)) := by
  -- Lemma 4.8: `V_𝔮` has finite length
  have hd := isPBWMonicAt_of_isMonicNormalForm k hform
  obtain ⟨-, -, -, hfin⟩ := lemma_4_8 hform
  have h := step_4_10_localized (R := Tangential k n) (symbolCoordinate k n) q
    (by rw [setup_coordinateMap_eq]; exact hqmem)
    (by rw [setup_coordinateMap_eq]; exact (hfin q hqmem hqmin).2)
    (step_4_10_localized_avoid hN hd q.asIdeal.primeCompl)
  rwa [setup_coordinateMap_eq] at h

end Canonical

#print axioms step_4_10_stable_kernel
#print axioms step_4_10_two_facts
#print axioms step_4_10_kernel_length
#print axioms step_4_10_length_split
#print axioms step_4_10_residual_nonzero
#print axioms step_4_10_core
#print axioms step_4_10_localized
#print axioms step_4_10_gabber
#print axioms step_4_10_localized_avoid
#print axioms lemma_4_10

end

end Stafford38.Paper.Section4
