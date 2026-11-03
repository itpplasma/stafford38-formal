module

public import Stafford38.Paper.Section4.Surjectivity
public import Stafford38.Paper.Section4.TangentialFiniteness
public import Stafford38.Characteristic.CanonicalPageEulerInequality

@[expose] public section

/-!
# Lemma 4.9: the page inequality `ℓ(U_𝔮) ≤ ℓ(V_𝔮)`

The filtered complex `Q --f--> Q`, `G^p = F_{-p}Q`, is
`CanonicalFilteredTwoTerm.canonicalFilteredTwoTerm` (`complex k n N d hd`); its
source and target pages `A_r`, `B_r` are `SourceTotal r`, `TargetTotal r`
(direct sums over `p` of the printed quotients), `d_r` is `tangentialDrop r`.
The steps below are the paragraphs of the printed proof: the pages and their
`T`-structure; localization and finite length; exhaustion `(B_R)_𝔮 = 0` from
`Q = Qx₁` (Proposition 4.3); equation (additivity); the telescoping sum.
-/

namespace Stafford38.Paper.Section4

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.Characteristic.CanonicalFilteredTwoTerm
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.Characteristic.CanonicalTangentialTotalAction
open Stafford38.Characteristic.CanonicalGradedTangentialEquivalences
open Stafford38.Characteristic.LocalizedKernelCokernelEquivalences
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport

noncomputable section

universe v

/-! ## Generic length bookkeeping -/

section Generic

variable {R : Type*} [Ring R] {A B : ℕ → Type*}
  [∀ r, AddCommGroup (A r)] [∀ r, Module R (A r)]
  [∀ r, AddCommGroup (B r)] [∀ r, Module R (B r)]

/-- **Later pages have finite length.**  `A_{r+1} ⊆ A_r` and `B_{r+1}` is a
quotient of `B_r`, so finite length of `A_1, B_1` passes to all `r ≥ 1`. -/
theorem step_4_9_pages_finite_length
    (d : ∀ r, A r →ₗ[R] B r)
    (sourceSucc : ∀ r, A (r + 1) ≃ₗ[R] LinearMap.ker (d r))
    (targetSucc : ∀ r, B (r + 1) ≃ₗ[R] B r ⧸ LinearMap.range (d r))
    (hA1 : IsFiniteLength R (A 1)) (hB1 : IsFiniteLength R (B 1)) :
    ∀ r, 1 ≤ r → IsFiniteLength R (A r) ∧ IsFiniteLength R (B r) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact ⟨hA1, hB1⟩
  | succ r _ ih =>
      exact ⟨(sourceSucc r).symm.isFiniteLength
          (IsFiniteLength.of_injective ih.1 (Submodule.subtype_injective _)),
        (targetSucc r).symm.isFiniteLength
          (IsFiniteLength.of_surjective ih.2 (Submodule.mkQ_surjective _))⟩

/-- **Equation (additivity).**  `0 → A_{r+1} → A_r → B_r → B_{r+1} → 0` splits at
`im d_r` into two short exact sequences; additivity of length (Definition 4.6)
gives `ℓ(B_r) + ℓ(A_{r+1}) = ℓ(A_r) + ℓ(B_{r+1})`. -/
theorem step_4_9_additivity {R : Type*} [Ring R] {A₀ A₁ B₀ B₁ : Type v}
    [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁]
    [AddCommGroup B₀] [Module R B₀] [AddCommGroup B₁] [Module R B₁]
    (d : A₀ →ₗ[R] B₀) (es : A₁ ≃ₗ[R] LinearMap.ker d)
    (et : B₁ ≃ₗ[R] B₀ ⧸ LinearMap.range d) :
    Module.length R B₀ + Module.length R A₁ = Module.length R A₀ + Module.length R B₁ := by
  have hsource : Module.length R A₀ =
      Module.length R (LinearMap.ker d) + Module.length R (LinearMap.range d) :=
    (definition_4_6 (T := R) (M := A₀)).2 (LinearMap.ker d).subtype d.rangeRestrict
      (Submodule.subtype_injective _)
      (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict d))
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  have htarget : Module.length R B₀ =
      Module.length R (LinearMap.range d) + Module.length R (B₀ ⧸ LinearMap.range d) :=
    (definition_4_6 (T := R) (M := B₀)).2 (LinearMap.range d).subtype (LinearMap.range d).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  rw [es.length_eq, et.length_eq, hsource, htarget]
  ac_rfl

/-- **Summing (additivity) over `r = 1,…,R−1`.**  The intermediate terms cancel:
`ℓ(B_1) + ℓ(A_R) = ℓ(A_1) + ℓ(B_R)`. -/
theorem step_4_9_telescope (a b : ℕ → ℕ∞) (ha : ∀ r, a r ≠ ⊤) (hb : ∀ r, b r ≠ ⊤)
    (hadd : ∀ r, 1 ≤ r → b r + a (r + 1) = a r + b (r + 1)) :
    ∀ R, 1 ≤ R → b 1 + a R = a 1 + b R := by
  have ha' : ∀ r, a r = ((a r).toNat : ℕ∞) := fun r => (ENat.natCast_toNat (ha r)).symm
  have hb' : ∀ r, b r = ((b r).toNat : ℕ∞) := fun r => (ENat.natCast_toNat (hb r)).symm
  have hadd' : ∀ r, 1 ≤ r → (b r).toNat + (a (r + 1)).toNat = (a r).toNat + (b (r + 1)).toNat :=
    fun r hr => by
      have h := hadd r hr
      rw [ha' r, ha' (r + 1), hb' r, hb' (r + 1)] at h
      exact_mod_cast h
  intro R hR
  rw [ha' 1, ha' R, hb' 1, hb' R]
  norm_cast
  induction R, hR using Nat.le_induction with
  | base => exact add_comm _ _
  | succ R hR ih =>
      have h := hadd' R hR
      omega

end Generic

/-! ## The canonical pages -/

section Canonical

variable {k : Type*} [Field k] [Algebra ℚ k] {n N : ℕ} {d : PresentedWeyl k (n + 1)}

attribute [local instance] sourceModule targetModule
attribute [local instance] Characteristic.CanonicalKoszulContradiction.gradedModule

/-- **The pages and their `T`-structure.**  `A_{r+1} = ker d_r` and
`B_{r+1} = coker d_r`, `T`-linearly, and `A_1 ≅ V`, `B_1 ≅ U`.  The `T`-action on
the pages comes from the symbols of the transverse generators, whose commutators
lower the filtration (`generator_commutator_lowers`). -/
theorem step_4_9_pages (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (∀ r, Nonempty ((complex k n N d hd).SourceTotal (r + 1) ≃ₗ[Tangential k n]
        LinearMap.ker (tangentialDrop k n N d hd r))) ∧
      (∀ r, Nonempty ((complex k n N d hd).TargetTotal (r + 1) ≃ₗ[Tangential k n]
        ((complex k n N d hd).TargetTotal r ⧸ LinearMap.range (tangentialDrop k n N d hd r)))) ∧
      Nonempty ((complex k n N d hd).SourceTotal 1 ≃ₗ[Tangential k n] kernelV k n N d) ∧
      Nonempty ((complex k n N d hd).TargetTotal 1 ≃ₗ[Tangential k n] cokernelU k n N d) :=
  ⟨fun r => ⟨tangentialSourceSuccEquiv k n N d hd r⟩,
    fun r => ⟨tangentialTargetSuccEquiv k n N d hd r⟩,
    ⟨firstSourceGradedKernelEquiv k n N d hd⟩, ⟨firstTargetGradedCokernelEquiv k n N d hd⟩⟩

/-- `f : Q → Q` of the filtered complex is onto: this is `Q = Qx₁`
(Proposition 4.3). -/
theorem step_4_9_f_surjective (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Function.Surjective (complex k n N d hd).f := by
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (rightIdealKSubmodule k (presentedCanonicalRightIdeal (k := k) n N d)) q
  obtain ⟨y, hy⟩ := proposition_4_3 hd (qmk (presentedCanonicalRightIdeal (k := k) n N d) z)
  obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective
    (rightIdealKSubmodule k (presentedCanonicalRightIdeal (k := k) n N d)) y
  rw [← hy'] at hy
  refine ⟨Submodule.Quotient.mk y', ?_⟩
  change rightMulLinearMap k (presentedCanonicalRightIdeal (k := k) n N d)
      (presentedCoordinate k n) (Submodule.Quotient.mk y') = Submodule.Quotient.mk z
  rw [rightMulLinearMap_mk]
  exact hy

/-- **Exhaustion: `(B_R)_𝔮 = 0` for some `R`.**  The maps `B_1 → B_r` are onto with
increasing kernels `K_r`.  A homogeneous class `z ∈ G^p` of `B_1` has a preimage
`z = wx₁` (Proposition 4.3) with `w ∈ G^s`, so `z` vanishes in `B_r` once
`p − r + 1 ≤ s`; hence `⋃ K_r = (B_1)_𝔮`.  As `(B_1)_𝔮` is Noetherian the chain
stabilizes at some `K_R = (B_1)_𝔮`, and `(B_R)_𝔮 = 0`. -/
theorem step_4_9_exhaustion (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (S : Submonoid (Tangential k n))
    [IsNoetherian (Localization S) (LocalizedModule S ((complex k n N d hd).TargetTotal 1))] :
    ∃ R, Subsingleton (LocalizedModule S ((complex k n N d hd).TargetTotal (R + 1))) :=
  AlgebraicAnalysis.exists_uniform_subsingleton_localized S
    (fun r => tangentialBoundaryMap k n N d hd r)
    (tangentialBoundaryMap_ker_mono k n N d hd)
    (fun z => (complex k n N d hd).totalBoundaryMap_eventually_zero
      (canonicalOrderFiltration_exhaustive k _) (step_4_9_f_surjective hd) z)
    (fun r => tangentialBoundaryMap_surjective k n N d hd r)

/-- **Lemma 4.9.** For every minimal prime `𝔮` of `Supp_T U`,
`ℓ_{T_𝔮}(U_𝔮) ≤ ℓ_{T_𝔮}(V_𝔮)`. -/
theorem lemma_4_9 (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (q : PrimeSpectrum (Tangential k n))
    (hqmem : q ∈ Module.support (Tangential k n) (cokernelU k n N d))
    (hqmin : ∀ p ∈ Module.support (Tangential k n) (cokernelU k n N d),
      p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal) :
    Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl (cokernelU k n N d)) ≤
      Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl (kernelV k n N d)) := by
  let S := q.asIdeal.primeCompl
  let A : ℕ → Type _ := fun r => LocalizedModule S ((complex k n N d hd).SourceTotal r)
  let B : ℕ → Type _ := fun r => LocalizedModule S ((complex k n N d hd).TargetTotal r)
  let : ∀ r, AddCommGroup (A r) := fun r => by dsimp only [A]; infer_instance
  let : ∀ r, Module (Localization S) (A r) := fun r => by dsimp only [A]; infer_instance
  let : ∀ r, AddCommGroup (B r) := fun r => by dsimp only [B]; infer_instance
  let : ∀ r, Module (Localization S) (B r) := fun r => by dsimp only [B]; infer_instance
  -- the pages and their localization; exactness keeps the successor identities
  obtain ⟨hsucc, htsucc, ⟨eV⟩, ⟨eU⟩⟩ := step_4_9_pages hd
  let dd : ∀ r, A r →ₗ[Localization S] B r := fun r =>
    localizedMap S (tangentialDrop k n N d hd r)
  let es : ∀ r, A (r + 1) ≃ₗ[Localization S] LinearMap.ker (dd r) := fun r =>
    (localizedEquiv S (hsucc r).some).trans (localizedKernelEquiv S _)
  let et : ∀ r, B (r + 1) ≃ₗ[Localization S] B r ⧸ LinearMap.range (dd r) := fun r =>
    (localizedEquiv S (htsucc r).some).trans (localizedCokernelEquiv S _)
  let eV' : A 1 ≃ₗ[Localization S] LocalizedModule S (kernelV k n N d) := localizedEquiv S eV
  let eU' : B 1 ≃ₗ[Localization S] LocalizedModule S (cokernelU k n N d) :=
    localizedEquiv S eU
  -- Lemma 4.8: `(A_1)_𝔮 = V_𝔮` and `(B_1)_𝔮 = U_𝔮` have finite length
  obtain ⟨-, -, -, hfin⟩ := lemma_4_8 hd
  obtain ⟨hU, hV⟩ := hfin q hqmem hqmin
  have hfl := step_4_9_pages_finite_length dd es et (eV'.symm.isFiniteLength hV)
    (eU'.symm.isFiniteLength hU)
  -- exhaustion: `(B_R)_𝔮 = 0`
  let : IsNoetherian (Localization S) (B 1) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hfl 1 le_rfl).2).1
  obtain ⟨R', hR'⟩ := step_4_9_exhaustion hd S
  -- equation (additivity) and the telescoping sum
  have hlen := step_4_9_telescope
    (fun r => if 1 ≤ r then Module.length (Localization S) (A r) else 0)
    (fun r => if 1 ≤ r then Module.length (Localization S) (B r) else 0)
    (fun r => by
      split_ifs with h
      · exact Module.length_ne_top_iff.mpr (hfl r h).1
      · exact ENat.zero_ne_top)
    (fun r => by
      split_ifs with h
      · exact Module.length_ne_top_iff.mpr (hfl r h).2
      · exact ENat.zero_ne_top)
    (fun r hr => by
      simp only [hr, ite_true, show 1 ≤ r + 1 by omega]
      exact step_4_9_additivity (dd r) (es r) (et r))
    (R' + 1) (by omega)
  simp only [le_refl, ite_true, show 1 ≤ R' + 1 by omega] at hlen
  have hBR : Module.length (Localization S) (B (R' + 1)) = 0 :=
    Module.length_eq_zero_iff.mpr hR'
  -- `ℓ(U_𝔮) + ℓ((A_R)_𝔮) = ℓ(V_𝔮)`, and `ℓ((A_R)_𝔮) ≥ 0`
  calc Module.length (Localization S) (LocalizedModule S (cokernelU k n N d))
        = Module.length (Localization S) (B 1) := eU'.length_eq.symm
    _ ≤ Module.length (Localization S) (B 1) + Module.length (Localization S) (A (R' + 1)) :=
        le_self_add
    _ = Module.length (Localization S) (A 1) := by rw [hlen, hBR, add_zero]
    _ = Module.length (Localization S) (LocalizedModule S (kernelV k n N d)) := eV'.length_eq

end Canonical

#print axioms step_4_9_pages_finite_length
#print axioms step_4_9_additivity
#print axioms step_4_9_telescope
#print axioms step_4_9_pages
#print axioms step_4_9_f_surjective
#print axioms step_4_9_exhaustion
#print axioms lemma_4_9

end

end Stafford38.Paper.Section4
