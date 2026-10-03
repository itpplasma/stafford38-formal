module
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Finiteness.Cardinality

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace Stafford38.Geometry.FiniteBirationalAway

universe u v w

/-- A finite birational algebra becomes the original domain after inverting
one nonzero element.  The common denominator is chosen for a finite module
generating family, then linearity gives the localization map's surjectivity. -/
theorem exists_nonzero_away_equiv_of_finite
    {Q : Type u} [CommRing Q] [IsDomain Q]
    {F : Type v} [Field F] [Algebra Q F] [IsFractionRing Q F]
    {B : Type w} [CommRing B] [Algebra Q B] [Algebra B F]
    [IsScalarTower Q B F] [Module.Finite Q B]
    (hinj : Function.Injective (algebraMap B F)) :
    ∃ f : Q, f ≠ 0 ∧
      Nonempty (Localization.Away f ≃ₐ[Q]
        Localization.Away (algebraMap Q B f)) := by
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin (R := Q) (M := B)
  obtain ⟨f₀, hf₀⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (M := nonZeroDivisors Q) (fun i : Fin n => algebraMap B F (gen i))
  let f : Q := f₀
  have hf : f ≠ 0 := by
    exact nonZeroDivisors.ne_zero f₀.property
  let p : Submodule Q B :=
    { carrier := {x | ∃ q : Q, algebraMap Q B q = algebraMap Q B f * x}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        intro x y hx hy
        rcases hx with ⟨q, hq⟩
        rcases hy with ⟨r, hr⟩
        refine ⟨q + r, ?_⟩
        rw [map_add, hq, hr, mul_add]
      smul_mem' := by
        intro a x hx
        rcases hx with ⟨q, hq⟩
        refine ⟨a * q, ?_⟩
        rw [map_mul, hq, Algebra.smul_def]
        ring }
  have hgen_mem : ∀ i : Fin n, gen i ∈ p := by
    intro i
    obtain ⟨q, hq⟩ := hf₀ i
    have hqF : algebraMap Q F q =
        algebraMap Q F f * algebraMap B F (gen i) := by
      simpa [f, Algebra.smul_def] using hq
    have hqB : algebraMap B F (algebraMap Q B q) =
        algebraMap B F (algebraMap Q B f * gen i) := by
      calc
        algebraMap B F (algebraMap Q B q) = algebraMap Q F q :=
          (IsScalarTower.algebraMap_apply Q B F q).symm
        _ = algebraMap Q F f * algebraMap B F (gen i) := hqF
        _ = algebraMap B F (algebraMap Q B f * gen i) := by
          rw [map_mul, IsScalarTower.algebraMap_apply Q B F f]
    exact ⟨q, hinj hqB⟩
  have hp : (⊤ : Submodule Q B) ≤ p := by
    rw [← hgen]
    apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    exact hgen_mem i
  have hclear : ∀ x : B, ∃ q : Q,
      algebraMap Q B q = algebraMap Q B f * x := by
    intro x
    have hx : x ∈ p := hp (Submodule.mem_top)
    exact hx
  have hQB : Function.Injective (algebraMap Q B) := by
    intro x y hxy
    exact IsFractionRing.injective Q F <| by
      calc
        algebraMap Q F x = algebraMap B F (algebraMap Q B x) :=
          IsScalarTower.algebraMap_apply Q B F x
        _ = algebraMap B F (algebraMap Q B y) := congrArg (algebraMap B F) hxy
        _ = algebraMap Q F y := (IsScalarTower.algebraMap_apply Q B F y).symm
  have hmap_injective :
      Function.Injective (Localization.awayMap (algebraMap Q B) f) := by
    rw [Localization.awayMap_injective_iff]
    intro x hx
    have hx0 : x = 0 := hQB (by simpa using hx)
    exact ⟨0, by simp [hx0]⟩
  have hmap_surjective :
      Function.Surjective (Localization.awayMap (algebraMap Q B) f) := by
    rw [Localization.awayMap_surjective_iff]
    intro x
    obtain ⟨q, hq⟩ := hclear x
    exact ⟨q, 1, by simpa using hq⟩
  refine ⟨f, hf, ?_⟩
  exact ⟨AlgEquiv.ofBijective
    (Localization.awayMapₐ (Algebra.ofId Q B) f)
    ⟨hmap_injective, hmap_surjective⟩⟩

end Stafford38.Geometry.FiniteBirationalAway
