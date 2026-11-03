module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

/-!
# Definition 5.3: valuation rings, discrete valuation rings, formal series

The paper's notions are Mathlib's `ValuationSubring`, `IsDiscreteValuationRing`,
`PowerSeries` and `LaurentSeries`.  `definition_5_3` states the printed
definitions as properties of these: (a) a subring `W ⊆ F` is a valuation ring
iff `a ∈ W` or `a⁻¹ ∈ W` for every `a ∈ F^×`, and then `W` is local with
`𝔪_W = W ∖ W^×`; (b) a valuation ring `V` is a discrete valuation ring iff it is
Noetherian and `V ≠ F`, and then `𝔪_V = (ϖ)` and every `f ∈ F^×` is `ϖ^k u` with a
unique `k = ord_V(f) ∈ ℤ` and `u ∈ V^×`; (c) `κ((t))` is the fraction field of
`κ[[t]]`.  Lemmas 5.9 and 5.10 use (a) and (b) through `definition_5_3`.
-/

namespace Stafford38.Paper.Section5

open IsLocalRing

noncomputable section

universe u

/-- The local ring structure of a valuation ring `W`, on the subring `W.toSubring`
used throughout Section 5.2. -/
instance valuationSubring_toSubring_isLocalRing {F : Type*} [Field F] (V : ValuationSubring F) :
    IsLocalRing V.toSubring :=
  ValuationSubring.isLocalRing V

theorem step_5_3_valuationRing {F : Type*} [Field F] (V : ValuationSubring F) :
    ValuationRing V.toSubring :=
  inferInstanceAs (ValuationRing V)

/-- A valuation ring equal to `F` is a field. -/
theorem step_5_3_isField_iff {F : Type*} [Field F] (V : ValuationSubring F) :
    IsField V.toSubring ↔ V = ⊤ := by
  constructor
  · intro hV
    rw [eq_top_iff]
    intro f _
    rcases V.mem_or_inv_mem f with h | h
    · exact h
    · by_cases hf : f = 0
      · rw [hf]; exact V.zero_mem
      · obtain ⟨g, hg⟩ := hV.mul_inv_cancel
          (a := (⟨f⁻¹, h⟩ : V.toSubring)) (fun h0 => inv_ne_zero hf (congrArg Subtype.val h0))
        have hg' : f⁻¹ * (g : F) = 1 := congrArg Subtype.val hg
        have : (g : F) = f := by
          rw [← one_mul (g : F), ← mul_inv_cancel₀ hf, mul_assoc, hg', mul_one]
        exact this ▸ g.2
  · rintro rfl
    refine ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩,
      fun a b => mul_comm a b, fun {a} ha => ?_⟩
    refine ⟨⟨(a : F)⁻¹, ValuationSubring.mem_top _⟩, Subtype.ext ?_⟩
    exact mul_inv_cancel₀ fun h => ha (Subtype.ext h)

/-- Uniqueness of `ord_V`: `ϖ^k u = ϖ^l u'` with units `u, u'` forces `k = l`. -/
theorem step_5_3_ord_unique {F : Type*} [Field F] (V : ValuationSubring F) {ϖ : V.toSubring}
    (hϖ : Irreducible ϖ) {k l : ℤ} {u u' : V.toSubringˣ}
    (h : (ϖ : F) ^ k * ((u : V.toSubring) : F) = (ϖ : F) ^ l * ((u' : V.toSubring) : F)) :
    k = l := by
  have hϖ0 : (ϖ : F) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hu : ∀ w : V.toSubringˣ, ((w : V.toSubring) : F) ≠ 0 := fun w h0 =>
    w.ne_zero (Subtype.ext h0)
  -- `ϖ^m` with `m ≥ 1` is not the image of a unit
  have key : ∀ (m : ℕ) (w : V.toSubringˣ), (ϖ : F) ^ (m + 1) ≠ ((w : V.toSubring) : F) := by
    intro m w hw
    have : ϖ ^ (m + 1) = (w : V.toSubring) := Subtype.ext (by simpa using hw)
    exact hϖ.not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero m)).mp (this ▸ w.isUnit))
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m : ℕ, l - k = (m + 1 : ℕ) := ⟨(l - k - 1).toNat, by omega⟩
    apply key m (u * u'⁻¹)
    have : (ϖ : F) ^ (l - k) = ((u : V.toSubring) : F) * ((u'⁻¹ : V.toSubringˣ) : V.toSubring) := by
      have hinv : ((u' : V.toSubring) : F) * ((u'⁻¹ : V.toSubringˣ) : V.toSubring) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      rw [zpow_sub₀ hϖ0, div_eq_iff (zpow_ne_zero _ hϖ0)]
      calc (ϖ : F) ^ l = (ϖ : F) ^ l * ((u' : V.toSubring) : F) *
            ((u'⁻¹ : V.toSubringˣ) : V.toSubring) := by rw [mul_assoc, hinv, mul_one]
        _ = _ := by rw [← h]; ring
    rw [hm, zpow_natCast] at this
    rw [this, Units.val_mul]
    rfl
  · exact hkl
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k - l = (m + 1 : ℕ) := ⟨(k - l - 1).toNat, by omega⟩
    apply key m (u' * u⁻¹)
    have : (ϖ : F) ^ (k - l) = ((u' : V.toSubring) : F) * ((u⁻¹ : V.toSubringˣ) : V.toSubring) := by
      have hinv : ((u : V.toSubring) : F) * ((u⁻¹ : V.toSubringˣ) : V.toSubring) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      rw [zpow_sub₀ hϖ0, div_eq_iff (zpow_ne_zero _ hϖ0)]
      calc (ϖ : F) ^ k = (ϖ : F) ^ k * ((u : V.toSubring) : F) *
            ((u⁻¹ : V.toSubringˣ) : V.toSubring) := by rw [mul_assoc, hinv, mul_one]
        _ = _ := by rw [h]; ring
    rw [hm, zpow_natCast] at this
    rw [this, Units.val_mul]
    rfl

/-- Existence of `f = ϖ^k u` in a discrete valuation ring `V ⊆ F`. -/
theorem step_5_3_ord_exists {F : Type*} [Field F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V.toSubring] {ϖ : V.toSubring} (hϖ : Irreducible ϖ)
    {f : F} (hf : f ≠ 0) :
    ∃ (k : ℤ) (u : V.toSubringˣ), f = (ϖ : F) ^ k * ((u : V.toSubring) : F) := by
  rcases V.mem_or_inv_mem f with h | h
  · obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, h⟩ : V.toSubring)) (fun h0 => hf (congrArg Subtype.val h0)) hϖ
    refine ⟨m, u, ?_⟩
    have := congrArg Subtype.val hu
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at this
    rw [zpow_natCast, mul_comm]
    exact this
  · obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f⁻¹, h⟩ : V.toSubring)) (fun h0 => inv_ne_zero hf (congrArg Subtype.val h0)) hϖ
    refine ⟨-(m : ℤ), u⁻¹, ?_⟩
    have := congrArg Subtype.val hu
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at this
    have hinv : ((u : V.toSubring) : F) * ((u⁻¹ : V.toSubringˣ) : V.toSubring) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have hϖ0 : (ϖ : F) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
    rw [zpow_neg, zpow_natCast]
    calc f = (f⁻¹)⁻¹ := (inv_inv f).symm
      _ = ((u : V.toSubring) : F)⁻¹ * ((ϖ : F) ^ m)⁻¹ := by rw [this, mul_inv]
      _ = _ := by rw [mul_comm, eq_inv_of_mul_eq_one_right hinv]

/-- **Definition 5.3.** Let `F` be a field.
(a) A subring `W ⊆ F` is a valuation ring of `F` iff `a ∈ W` or `a⁻¹ ∈ W` for
every `a ∈ F^×`; it is a local ring with maximal ideal `𝔪_W = W ∖ W^×`.
(b) A valuation ring `V` is a discrete valuation ring iff it is Noetherian and
`V ≠ F`; then `𝔪_V` is generated by some `ϖ ∈ V`, and every `f ∈ F^×` is
`f = ϖ^k u` with `u ∈ V^×` and a unique `k = ord_V(f) ∈ ℤ`.
(c) For a field `κ`, `κ((t))` (`LaurentSeries κ`) is the fraction field of
`κ[[t]]` (`PowerSeries κ`). -/
theorem definition_5_3 {F : Type u} [Field F] :
    (∀ S : Subring F,
        (∀ a : F, a ≠ 0 → a ∈ S ∨ a⁻¹ ∈ S) ↔ ∃ W : ValuationSubring F, W.toSubring = S) ∧
      (∀ W : ValuationSubring F,
        IsLocalRing W.toSubring ∧ ∀ w : W.toSubring, w ∈ maximalIdeal W.toSubring ↔ ¬ IsUnit w) ∧
      (∀ V : ValuationSubring F,
        IsDiscreteValuationRing V.toSubring ↔ IsNoetherianRing V.toSubring ∧ V ≠ ⊤) ∧
      (∀ V : ValuationSubring F, IsDiscreteValuationRing V.toSubring →
        ∃ ϖ : V.toSubring, maximalIdeal V.toSubring = Ideal.span {ϖ} ∧
          ∀ f : F, f ≠ 0 → ∃! k : ℤ, ∃ u : V.toSubringˣ,
            f = (ϖ : F) ^ k * ((u : V.toSubring) : F)) ∧
      ∀ (κ : Type u) [Field κ], IsFractionRing (PowerSeries κ) (LaurentSeries κ) := by
  refine ⟨fun S => ⟨fun h => ?_, ?_⟩, fun W => ⟨inferInstance, fun w => ?_⟩,
    fun V => ⟨fun hV => ?_, fun ⟨hN, hV⟩ => ?_⟩, fun V hV => ?_, fun κ _ => inferInstance⟩
  · refine ⟨⟨S, fun a => ?_⟩, rfl⟩
    by_cases ha : a = 0
    · exact Or.inl (ha ▸ S.zero_mem)
    · exact h a ha
  · rintro ⟨W, rfl⟩ a _
    exact W.mem_or_inv_mem a
  · rw [mem_maximalIdeal, mem_nonunits_iff]
  · refine ⟨inferInstance, fun hVtop => IsDiscreteValuationRing.not_isField V.toSubring ?_⟩
    exact (step_5_3_isField_iff V).2 hVtop
  · have hfield : ¬ IsField V.toSubring := fun h => hV ((step_5_3_isField_iff V).1 h)
    have := step_5_3_valuationRing V
    exact ((IsDiscreteValuationRing.TFAE V.toSubring hfield).out 1 2).2 this
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V.toSubring
    refine ⟨ϖ, hϖ.maximalIdeal_eq, fun f hf => ?_⟩
    obtain ⟨k, u, hku⟩ := step_5_3_ord_exists V hϖ hf
    exact ⟨k, ⟨u, hku⟩, fun l ⟨u', hl⟩ => step_5_3_ord_unique V hϖ (hl.symm.trans hku)⟩

#print axioms step_5_3_valuationRing
#print axioms step_5_3_isField_iff
#print axioms step_5_3_ord_unique
#print axioms step_5_3_ord_exists
#print axioms definition_5_3

end

end Stafford38.Paper.Section5
