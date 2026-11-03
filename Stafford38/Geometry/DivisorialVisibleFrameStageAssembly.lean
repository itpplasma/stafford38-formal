module
public import Stafford38.Geometry.DivisorialVisibleFrameCore
public import Stafford38.Geometry.DivisorialVisibleFrameStage2
public import Stafford38.Geometry.DivisorialVisibleFrameStage4
public import Stafford38.Geometry.DivisorialVisibleFrameStage5
public import Stafford38.Paper.Section5.Place

@[expose] public section

open IsLocalRing Polynomial
open Stafford38.Geometry.NormalizationHeightOne

noncomputable section
set_option maxHeartbeats 1000000

universe u v

namespace Stafford38.Geometry.LaneC

theorem stage2_of_verified : Stage2Obligation.{u} := by
  intro k K _ _ _ _ r y i hgen hx
  exact DivisorialVisibleFrameStage2.stage2_exists_chart_normalization y i hgen hx

theorem stage4_of_verified : Stage4Obligation.{u, v} := by
  intro k K _ _ _ A p _ V _ _ _ hAV hp hsurj _ι c hc hint
  exact DivisorialVisibleFrameStage4.stage4_residueField_isAlgebraic_of_isIntegral
    A p V hAV hp hsurj c hc hint

theorem stage5_of_verified : Stage5Obligation.{u} := by
  intro k K _ _ _ A hAft p _ V _ hAV hp hsurj
  obtain ⟨E, hEV, hfin⟩ :=
    DivisorialVisibleFrameStage5.stage5_exists_coefficientField A p V hAV hp hsurj
  refine ⟨E, hEV, ?_⟩
  exact hfin

/-- The place at infinity of the paper's proof of Theorem 5.7: the valuation
ring and chart of Lemma 5.9, the discrete valuation ring `V = A_{𝔭_D}` of
Lemma 5.10, and a coefficient field `E` over which `κ` is finite (the input to
the coefficient field of the completion, Matsumura Thm. 28.3). -/
theorem divisorialVisibleFrameExistenceWithChart
    (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
    (r : ℕ) (y : Fin r → K) (i : Fin r)
    (hgen : IntermediateField.adjoin k (Set.range y) = ⊤)
    (hx : Transcendental k (y i)) :
    ∃ (E : IntermediateField k K) (V : ValuationSubring K)
      (hEV : ∀ z : E, (z : K) ∈ V.toSubring)
      (hVdvr : IsDiscreteValuationRing V.toSubring)
      (hxV : y i ∈ V.toSubring),
      letI : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
      letI : Algebra E V.toSubring := (coeffHom E V hEV).toAlgebra
      letI : Algebra k V.toSubring := (groundHom E V hEV).toAlgebra
      Transcendental E (y i) ∧
      (⟨y i, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring ∧
      Module.Finite E (ResidueField V.toSubring) ∧
      Module.Finite V.toSubring (Ω[V.toSubring⁄k]) ∧
      (∀ (s : K) (q : Fin (r + 1) → V.toSubring),
        (∀ a, (q a : K) = s * Fin.cases 1 y a) →
        (∃ j, q j = 1) → ¬ IsUnit (q 0) →
        Algebra.IsAlgebraic
          (IntermediateField.adjoin k
            (Set.range fun j : Fin r ↦ residue V.toSubring (q (Fin.succ j))) :
            IntermediateField k (ResidueField V.toSubring))
          (ResidueField V.toSubring)) ∧
      -- The chart `j` of Lemma 5.9, with `q_a = x̄_a / x̄_j ∈ V` (Lemma 5.10(a)).
      ∃ j, (Fin.cases 1 y j : K) ≠ 0 ∧
        ∀ a, (Fin.cases 1 y a : K) / Fin.cases 1 y j ∈ V.toSubring := by
  -- Lemma 5.9.
  obtain ⟨W, j, hkW, -, hxW, hj, hqW⟩ := Stafford38.Paper.Section5.lemma_5_9 y i hx
  -- Lemma 5.10.
  obtain ⟨L⟩ := Stafford38.Paper.Section5.lemma_5_10 y i hgen hx W j hkW hxW hj hqW
  let A := L.A
  let p := L.p
  let V : ValuationSubring K := L.V
  have hVdvr : IsDiscreteValuationRing V.toSubring := L.isDVR
  letI : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
  have hAV : ∀ a : A, (a : K) ∈ V.toSubring := fun a => ofField_mem_algebraMap_v A p L.place a
  have hpV : ∀ a : A, (⟨a, hAV a⟩ : V.toSubring) ∈ maximalIdeal V.toSubring ↔ a ∈ p :=
    fun a => ofField_mem_maximalIdeal_iff_v A p L.place a
  have hsurj : ∀ z : ResidueField V.toSubring, ∃ (a b : A), b ∉ p ∧
      z = residue V.toSubring ⟨a, hAV a⟩ / residue V.toSubring ⟨b, hAV b⟩ :=
    fun z => ofField_residue_surjective_v A p L.place z
  have hy0 : y i ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hxV : y i ∈ V.toSubring := hAV ⟨y i, L.x_mem⟩
  have hxm : (⟨y i, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring :=
    (hpV ⟨y i, L.x_mem⟩).2 L.x_mem_p
  obtain ⟨E, hEV, hEfin⟩ := stage5_of_verified A p V hAV hpV hsurj
  letI : Algebra E V.toSubring := (coeffHom E V hEV).toAlgebra
  have htrans : Transcendental E (y i) :=
    stage6_transcendental_of_mem_maximalIdeal E V hEV (y i) hy0 hxV hxm
  have hk : ∀ c : k, algebraMap k K c ∈ V.toSubring := fun c => hAV (algebraMap k A c)
  let cod : Algebra k V.toSubring := ((algebraMap k K).codRestrict _ hk).toAlgebra
  let ground : Algebra k V.toSubring := (groundHom E V hEV).toAlgebra
  have hcod_ground : cod = ground := by
    apply Algebra.algebra_ext
    intro c
    apply Subtype.ext
    rfl
  letI : Algebra k V.toSubring := ground
  letI : IsScalarTower k V.toSubring K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k K c = algebraMap k K c
      rfl
  have hkaehler : Module.Finite V.toSubring (Ω[V.toSubring⁄k]) := by
    have h := L.kaehler_finite
    change (letI : Algebra k V.toSubring := cod; Module.Finite V.toSubring (Ω[V.toSubring⁄k])) at h
    rw [hcod_ground] at h
    exact h
  -- The normalized column `q_a = x̄_a / x̄_j` of Lemma 5.10.
  let s : K := (Fin.cases 1 y j : K)⁻¹
  have hjs : (Fin.cases 1 y j : K) * s = 1 := mul_inv_cancel₀ hj
  let c : Fin (r + 1) → V.toSubring := fun a =>
    ⟨(Fin.cases 1 y a : K) / Fin.cases 1 y j, hAV ⟨_, L.q_mem a⟩⟩
  have hc : ∀ a, (c a : K) = (Fin.cases 1 y a : K) * s := fun a => div_eq_mul_inv _ _
  have hcj : c j = 1 := Subtype.ext (div_self hj)
  have halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range fun a => residue V.toSubring (c a)) :
        IntermediateField k (ResidueField V.toSubring))
      (ResidueField V.toSubring) := by
    have h := L.residue_algebraic
    change (letI : Algebra k V.toSubring := cod; Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range fun a => residue V.toSubring (c a)) :
        IntermediateField k (ResidueField V.toSubring))
      (ResidueField V.toSubring)) at h
    rw [hcod_ground] at h
    exact h
  refine ⟨E, V, hEV, hVdvr, hxV, htrans, hxm, hEfin, hkaehler, ?_, j, hj, fun a ↦ (c a).2⟩
  intro s' q hq hq1 hq0
  by_cases hj0 : j = 0
  · obtain ⟨j', hj'⟩ := hq1
    exfalso
    have hsone : s = 1 := by simpa [hj0] using hjs
    have hprod : ∀ a, q a = q 0 * c a := by
      intro a
      apply Subtype.ext
      change (q a : K) = (q 0 : K) * (c a : K)
      rw [hq a, hq 0, hc a]
      simp [hsone]
    have hq0res : residue V.toSubring (q 0) = 0 := by
      by_contra hnz
      exact hq0 ((residue_ne_zero_iff_isUnit _).1 hnz)
    have hqjres : residue V.toSubring (q j') = 0 := by
      rw [hprod j', map_mul, hq0res, zero_mul]
    have hqjunit : IsUnit (q j') := by rw [hj']; exact isUnit_one
    exact ((residue_ne_zero_iff_isUnit _).2 hqjunit) hqjres
  · exact DivisorialVisibleFrameStage4.stage4'_isAlgebraic_of_normalized_column
      V y j hj0 s c hc hcj halg
      s' q hq hq1 hq0

/-- `divisorialVisibleFrameExistenceWithChart` without its chart. -/
theorem divisorialVisibleFrameExistence : DivisorialVisibleFrameExistence.{u} := by
  intro k K _ _ _ _ r y i hgen hx
  obtain ⟨E, V, hEV, hVdvr, hxV, h₁, h₂, h₃, h₄, h₅, -⟩ :=
    divisorialVisibleFrameExistenceWithChart k K r y i hgen hx
  exact ⟨E, V, hEV, hVdvr, hxV, h₁, h₂, h₃, h₄, h₅⟩

end Stafford38.Geometry.LaneC

#print axioms Stafford38.Geometry.LaneC.divisorialVisibleFrameExistenceWithChart
#print axioms Stafford38.Geometry.LaneC.divisorialVisibleFrameExistence
