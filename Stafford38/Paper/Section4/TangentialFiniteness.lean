module

public import Stafford38.Paper.Section4.Support
public import Stafford38.Paper.Section4.Setup
public import AlgebraicAnalysis.Module.MinimalPrimeFiniteLengthLocalization
public import Stafford38.Paper.Section3.OrderSymbol

@[expose] public section

/-!
# Lemma 4.8: tangential finiteness

The three paragraphs of the printed proof: `U, V` are finite over `T`;
`Supp_T V ⊆ Supp_T U` (Lemma 4.7 and Vasconcelos' theorem); at a minimal prime
`𝔮` of `Supp_T U`, `U_𝔮` and `V_𝔮` have finite length.  The last two are proved
for any commutative Noetherian algebra `T → C` and finite `C`-module.
-/

namespace Stafford38.Paper.Section4

open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalOldTangentialFiniteness
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.Paper.Section3 (IsMonicNormalForm isPBWMonicAt_of_isMonicNormalForm)

noncomputable section

/-- **Vasconcelos paragraph.**  For a finite module `M` over a commutative
Noetherian ring `C` and `f ∈ End_C M`, `Supp_C(ker f) ⊆ Supp_C(coker f)`: if
`(coker f)_𝔔 = coker(f_𝔔) = 0`, then `f_𝔔` is a surjective endomorphism of a finite
module, hence injective, and `(ker f)_𝔔 = ker(f_𝔔) = 0`. -/
theorem step_4_8_vasconcelos {C E : Type*} [CommRing C] [IsNoetherianRing C]
    [AddCommGroup E] [Module C E] [Module.Finite C E] (f : Module.End C E) :
    Module.support C (LinearMap.ker f) ⊆ Module.support C (E ⧸ LinearMap.range f) := by
  intro Q hQ
  by_contra hc
  let S := Q.asIdeal.primeCompl
  have hzero : Subsingleton (LocalizedModule S (E ⧸ LinearMap.range f)) :=
    Module.notMem_support_iff.mp hc
  -- exactness of localization: `(coker f)_𝔔 = coker(f_𝔔)`
  have hexc := (definition_4_4 S).2.2 f (LinearMap.range f).mkQ
    (LinearMap.exact_map_mkQ_range f)
  have hsurj : Function.Surjective (LocalizedModule.map S f) := by
    intro z
    exact (hexc z).mp (Subsingleton.elim _ _)
  -- Vasconcelos: a surjective endomorphism of a finite module is injective
  have hinj : Function.Injective (LocalizedModule.map S f) :=
    IsNoetherian.injective_of_surjective_endomorphism _ hsurj
  -- exactness again: `(ker f)_𝔔 = ker(f_𝔔) = 0`
  have hexk := (definition_4_4 S).2.2 (LinearMap.ker f).subtype f
    (LinearMap.exact_subtype_ker_map f)
  have hsub : Subsingleton (LocalizedModule S (LinearMap.ker f)) := by
    refine ⟨fun a b => LocalizedModule.map_injective S _ (Submodule.subtype_injective _) ?_⟩
    have ha : LocalizedModule.map S f (LocalizedModule.map S (LinearMap.ker f).subtype a) =
        LocalizedModule.map S f (LocalizedModule.map S (LinearMap.ker f).subtype b) := by
      rw [hexk.apply_apply_eq_zero, hexk.apply_apply_eq_zero]
    exact hinj ha
  exact Module.notMem_support_iff.mpr hsub hQ

/-- **Second paragraph: `Supp_T V ⊆ Supp_T U`.**  For `𝔭 ∈ Supp_T V` pick `v` with
`Ann_T(v) ⊆ 𝔭` (Lemma 4.7); `Ann_{k[x,ξ]}(v)` misses `S = T∖𝔭`, so lies in a prime
`𝔔` with `𝔔 ∩ S = ∅`; `𝔔 ∈ Supp(ker f)` (Lemma 4.7), hence `𝔔 ∈ Supp(coker f)`
(Vasconcelos), so some `u ∈ U` has `Ann(u) ⊆ 𝔔` (Lemma 4.7), whence
`Ann_T(u) ⊆ 𝔭` and `𝔭 ∈ Supp_T U` (Lemma 4.7). -/
theorem step_4_8_support_inclusion {R C E : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup E] [Module C E] [Module R E] [IsScalarTower R C E]
    [IsNoetherianRing C] [Module.Finite C E] (f : Module.End C E) :
    Module.support R (LinearMap.ker (f.restrictScalars R)) ⊆
      Module.support R (E ⧸ LinearMap.range (f.restrictScalars R)) := by
  intro p hp
  obtain ⟨v, hv⟩ := (lemma_4_7 p).mp hp
  let vC : LinearMap.ker f := ⟨v.1, v.2⟩
  let I : Ideal C := (C ∙ vC).annihilator
  have hdisj : Disjoint (I : Set C) (p.asIdeal.primeCompl.map (algebraMap R C)) := by
    rw [Set.disjoint_left]
    rintro c hc ⟨r, hr, rfl⟩
    have hrv : r • v = 0 := by
      apply Subtype.ext
      change r • v.1 = 0
      have hcv : algebraMap R C r • vC = 0 :=
        (Submodule.mem_annihilator_span_singleton _ _).mp hc
      simpa [vC, IsScalarTower.algebraMap_smul C r v.1] using congrArg Subtype.val hcv
    exact hr (hv ((Submodule.mem_annihilator_span_singleton _ _).mpr hrv))
  obtain ⟨Q, hQprime, hIQ, hQdisj⟩ := I.exists_le_prime_disjoint _ hdisj
  let Q' : PrimeSpectrum C := ⟨Q, hQprime⟩
  have hQker : Q' ∈ Module.support C (LinearMap.ker f) := (lemma_4_7 Q').mpr ⟨vC, hIQ⟩
  have hQcoker := step_4_8_vasconcelos f hQker
  obtain ⟨u, hu⟩ := (lemma_4_7 Q').mp hQcoker
  refine (lemma_4_7 p).mpr ⟨u, fun r hr => ?_⟩
  have hmap : algebraMap R C r ∈ (C ∙ u).annihilator := by
    rw [Submodule.mem_annihilator_span_singleton]
    have hru : r • u = 0 := (Submodule.mem_annihilator_span_singleton _ _).mp hr
    simpa [IsScalarTower.algebraMap_smul C r u] using hru
  by_contra hrp
  exact Set.disjoint_left.mp hQdisj (hu hmap) ⟨r, hrp, rfl⟩

/-- A minimal prime of `Supp_T L` (`L` finite over the Noetherian `T`) is minimal
over `Ann_T L`, since `Supp L = V(Ann L)` [Stacks 00L2], so `L_𝔮` has finite
length [Atiyah–Macdonald 8.5, Stacks 00KH]. -/
theorem step_4_8_localized_isFiniteLength {R L : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup L] [Module R L] [Module.Finite R L] (q : PrimeSpectrum R)
    (hqmem : q ∈ Module.support R L)
    (hq : ∀ p ∈ Module.support R L, p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal) :
    IsFiniteLength (Localization q.asIdeal.primeCompl)
      (LocalizedModule q.asIdeal.primeCompl L) := by
  have hmin : q.asIdeal ∈ (Module.annihilator R L).minimalPrimes := by
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
      (Module.mem_support_iff_of_finite.mp hqmem)
    have hp' : (⟨p, hp.1.1⟩ : PrimeSpectrum R) ∈ Module.support R L :=
      Module.mem_support_iff_of_finite.mpr hp.1.2
    have heq : p = q.asIdeal := le_antisymm hpq (hq _ hp' hpq)
    simpa [heq] using hp
  exact AlgebraicAnalysis.MinimalPrimeFiniteLengthLocalization.localizedModule_isFiniteLength
    q.asIdeal hmin

/-- **Third paragraph.**  At a minimal prime `𝔮` of `Supp_T U`, the supports of
`U_𝔮` and `V_𝔮` are contained in `{𝔮T_𝔮}` (for `V` by `Supp V ⊆ Supp U`), so
both have finite length over `T_𝔮` (`V_𝔮` possibly zero). -/
theorem step_4_8_finite_length {R U V : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup U] [Module R U] [Module.Finite R U]
    [AddCommGroup V] [Module R V] [Module.Finite R V]
    (hsupp : Module.support R V ⊆ Module.support R U) (q : PrimeSpectrum R)
    (hqmem : q ∈ Module.support R U)
    (hq : ∀ p ∈ Module.support R U, p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal) :
    IsFiniteLength (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl U) ∧
      IsFiniteLength (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl V) := by
  refine ⟨step_4_8_localized_isFiniteLength q hqmem hq, ?_⟩
  by_cases hk : q ∈ Module.support R V
  · exact step_4_8_localized_isFiniteLength q hk fun p hp hpq => hq p (hsupp hp) hpq
  · have : Subsingleton (LocalizedModule q.asIdeal.primeCompl V) :=
      Module.notMem_support_iff.mp hk
    exact IsFiniteLength.of_subsingleton

section Canonical

variable {k : Type*} [Field k] [Algebra ℚ k] {n N : ℕ} {d : PresentedWeyl k (n + 1)}

attribute [local instance] Characteristic.CanonicalKoszulContradiction.gradedModule
  Characteristic.CanonicalKoszulContradiction.coefficientAlgebra
  Characteristic.CanonicalKoszulContradiction.coefficientTower

omit [Algebra ℚ k] in
/-- **First paragraph: `U` and `V` are finite over `T`.**  `M = gr Q` is finite
over `k[x,ξ] = T[x₁,ξ₁]` (cyclic generator `q̄`).  Since `P` annihilates `M`
(Proposition 3.6) and is monic of degree `N` in `ξ₁`, `M` is finite over `T[x₁]`
(`canonical_orderAssociatedGradedModule_finite_normalCoeffRing_of_mem_annihilator`);
`V` and `U` are then finite over the Noetherian `T[x₁]` and, being killed by `x₁`,
over `T` (`canonical_finite_old_coordinate_kernel_cokernel_of_mem_annihilator`). -/
theorem step_4_8_finite (hform : IsMonicNormalForm k N d) :
    Module.Finite (Tangential k n) (cokernelU k n N d) ∧
      Module.Finite (Tangential k n) (kernelV k n N d) :=
  (canonical_finite_old_coordinate_kernel_cokernel_of_mem_annihilator
    (isPBWMonicAt_of_isMonicNormalForm k hform)
    (Stafford38.Paper.Section3.proposition_3_6 k hform
      (Stafford38.Paper.Section3.bernsteinDegree_eq_of_isMonicNormalForm k hform))).symm

omit [Algebra ℚ k] in
/-- **Lemma 4.8.** `U` and `V` are finite over `T`, `Supp_T V ⊆ Supp_T U`, and at a
minimal prime `𝔮` of `Supp_T U`, `U_𝔮` and `V_𝔮` have finite length over `T_𝔮`.
Here `d̃` is in the form (3.1), used through `IsPBWMonicAt`. -/
theorem lemma_4_8 (hform : IsMonicNormalForm k N d) :
    Module.Finite (Tangential k n) (cokernelU k n N d) ∧
      Module.Finite (Tangential k n) (kernelV k n N d) ∧
      Module.support (Tangential k n) (kernelV k n N d) ⊆
        Module.support (Tangential k n) (cokernelU k n N d) ∧
      ∀ q ∈ Module.support (Tangential k n) (cokernelU k n N d),
        (∀ p ∈ Module.support (Tangential k n) (cokernelU k n N d),
          p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal) →
        IsFiniteLength (Localization q.asIdeal.primeCompl)
            (LocalizedModule q.asIdeal.primeCompl (cokernelU k n N d)) ∧
          IsFiniteLength (Localization q.asIdeal.primeCompl)
            (LocalizedModule q.asIdeal.primeCompl (kernelV k n N d)) := by
  obtain ⟨hU, hV⟩ := step_4_8_finite hform
  have hsupp : Module.support (Tangential k n) (kernelV k n N d) ⊆
      Module.support (Tangential k n) (cokernelU k n N d) := by
    have h := step_4_8_support_inclusion (R := Tangential k n)
      (LinearMap.lsmul (Symbol k n) (GrQ k n N d) (symbolCoordinate k n))
    rwa [setup_coordinateMap_eq] at h
  exact ⟨hU, hV, hsupp, fun q hqmem hq => step_4_8_finite_length hsupp q hqmem hq⟩

end Canonical

#print axioms step_4_8_vasconcelos
#print axioms step_4_8_support_inclusion
#print axioms step_4_8_finite_length
#print axioms step_4_8_finite
#print axioms lemma_4_8

end

end Stafford38.Paper.Section4
