import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section
set_option autoImplicit false

namespace Stafford38.Geometry

/-- If a prime of a subring is the contraction of the maximal ideal of a valuation
subring, then the corresponding local ring is dominated by that valuation subring.

This is the local algebra step in a center construction: it does not assert that the
prime is height one or that the valuation comes from a specified projective model. -/
theorem localRing_at_contracted_maximalIdeal_le_valuationSubring
    {K : Type*} [Field K] (A : Subring K) (V : ValuationSubring K)
    (hAV : A ≤ V.toSubring) (p : Ideal A) [p.IsPrime]
    (hcenter : (IsLocalRing.maximalIdeal V.toLocalSubring.toSubring).comap
      (Subring.inclusion hAV) = p) :
    LocalSubring.ofPrime A p ≤ V.toLocalSubring := by
  let i : A →+* V.toLocalSubring.toSubring := Subring.inclusion hAV
  let W : LocalSubring K := V.toLocalSubring
  have hcenter' : (IsLocalRing.maximalIdeal W.toSubring).comap i = p := by
    convert hcenter using 1 <;> rfl
  have hiK : W.toSubring.subtype.comp i = A.subtype := by
    ext a
    rfl
  have hunit (s : p.primeCompl) : IsUnit (i s.1) := by
    have hsnotmax : i s.1 ∉ IsLocalRing.maximalIdeal W.toSubring := by
      intro hs
      apply s.2
      have hs' : s.1 ∈ (IsLocalRing.maximalIdeal W.toSubring).comap i :=
        Ideal.mem_comap.mpr hs
      rw [hcenter'] at hs'
      exact hs'
    exact IsLocalRing.notMem_maximalIdeal.mp hsnotmax
  let B := Localization.AtPrime p
  let g : B →+* W.toSubring := IsLocalization.lift
    (M := p.primeCompl) (S := B) (g := i) hunit
  have hglocal : IsLocalHom g := by
    apply (IsLocalRing.local_hom_TFAE g).out 2 1 |>.mp
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    have haB : algebraMap A B a ∈ IsLocalRing.maximalIdeal B :=
      (IsLocalization.mk'_mem_iff (M := p.primeCompl)).mp hx
    have hap : a ∈ p :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff B p a).mp haB
    have hai : i a ∈ IsLocalRing.maximalIdeal W.toSubring := by
      have ha' : a ∈ (IsLocalRing.maximalIdeal W.toSubring).comap i := by
        rw [hcenter']
        exact hap
      exact Ideal.mem_comap.mp ha'
    rw [IsLocalization.lift_mk']
    let u : W.toSubringˣ := IsUnit.liftRight
      (i.toMonoidHom.domRestrict p.primeCompl) hunit s
    change i a * ↑u⁻¹ ∈ IsLocalRing.maximalIdeal W.toSubring
    convert (IsLocalRing.maximalIdeal W.toSubring).mul_mem_left (↑u⁻¹) hai using 1
    rw [mul_comm]
  let h0 : B →+* K := IsLocalization.lift
    (M := p.primeCompl) (S := B) (g := A.subtype)
    (by intro s; exact isUnit_iff_ne_zero.mpr (by
      intro hz
      have hsA : s.1 = 0 := Subtype.val_injective hz
      apply s.2
      rw [hsA]
      exact p.zero_mem))
  have hgK : W.toSubring.subtype.comp g = h0 := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    simp [g, h0]
    exact RingHom.congr_fun hiK a
  let S := LocalSubring.ofPrime A p
  let e : B ≃ₐ[A] S.toSubring := LocalSubring.ofPrimeEquiv A p
  have heK : S.toSubring.subtype.comp e.toRingHom = h0 := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    simp only [RingHom.comp_apply]
    rw [IsLocalization.lift_eq]
    have hcomm : e.toRingEquiv.toRingHom (algebraMap A B a) =
        algebraMap A S.toSubring a := by
      change e (algebraMap A B a) = algebraMap A S.toSubring a
      exact e.commutes a
    rw [hcomm]
    rfl
  let j : S.toSubring →+* W.toSubring := g.comp e.symm.toRingHom
  have hjK : ∀ x : S.toSubring, ((j x : W.toSubring) : K) = (x : K) := by
    intro x
    have h := RingHom.congr_fun hgK (e.symm x)
    have h' := RingHom.congr_fun heK (e.symm x)
    calc
      ((j x : W.toSubring) : K) = ((g (e.symm x) : W.toSubring) : K) := rfl
      _ = h0 (e.symm x) := h
      _ = (x : K) := by simpa using h'.symm
  have hS : S.toSubring ≤ W.toSubring := by
    intro x hx
    have hx' : ((⟨x, hx⟩ : S.toSubring) : K) ∈ W.toSubring := by
      rw [← hjK ⟨x, hx⟩]
      exact (j ⟨x, hx⟩).property
    exact hx'
  have heLocal : IsLocalHom e.symm.toRingHom := by
    refine ⟨fun x hx => ?_⟩
    have hx' := hx.map e.toRingHom
    simpa using hx'
  letI : IsLocalHom g := hglocal
  letI : IsLocalHom e.symm.toRingHom := heLocal
  have hjlocal : IsLocalHom j := by
    dsimp [j]
    infer_instance
  have hjEq : j = Subring.inclusion hS := by
    ext x
    change ((j x : W.toSubring) : K) = (x : K)
    exact hjK x
  rw [LocalSubring.le_def]
  exact ⟨hS, by rw [← hjEq]; exact hjlocal⟩

end Stafford38.Geometry
