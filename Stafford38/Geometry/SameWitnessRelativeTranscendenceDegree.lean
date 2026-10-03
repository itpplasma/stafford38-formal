module
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Stafford38.Geometry.DVRParameterSmoothness

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.SameWitnessRelativeTranscendenceDegree

universe u

/-- A finite relative base cancels from the same-witness total-degree bound.
If the residue field is algebraic over that base, the component field has
relative transcendence degree at most one; one transcendental parameter makes
the bound exact. -/
theorem eq_one_of_same_total_bound
    {k E F κ : Type u}
    [Field k] [Field E] [Field F] [Field κ]
    [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]
    [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (hEfinite : Algebra.trdeg k E < Cardinal.aleph0)
    (hκalg : Algebra.IsAlgebraic E κ)
    (hbound : Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1)
    (htrans : Algebra.Transcendental E F) :
    Algebra.trdeg E F = 1 := by
  have hκ : Algebra.trdeg k κ = Algebra.trdeg k E := by
    have hsum : Algebra.trdeg k E + Algebra.trdeg E κ = Algebra.trdeg k κ :=
      trdeg_add_eq k E (A := κ)
    rw [trdeg_eq_zero_iff.mpr hκalg, add_zero] at hsum
    exact hsum.symm
  have htotal : Algebra.trdeg k E + Algebra.trdeg E F ≤
      Algebra.trdeg k E + 1 := by
    calc
      Algebra.trdeg k E + Algebra.trdeg E F = Algebra.trdeg k F :=
        trdeg_add_eq k E (A := F)
      _ ≤ Algebra.trdeg k κ + 1 := hbound
      _ = Algebra.trdeg k E + 1 := by rw [hκ]
  have hrel : Algebra.trdeg E F ≤ 1 := by
    apply (Cardinal.add_le_add_iff_of_lt_aleph0 hEfinite).mp
    simpa only [add_comm (Algebra.trdeg E F) (Algebra.trdeg k E),
      add_comm 1 (Algebra.trdeg k E)] using htotal
  have hpos : 1 ≤ Algebra.trdeg E F :=
    Cardinal.one_le_iff_ne_zero.mpr (trdeg_ne_zero_iff.mpr htrans)
  exact le_antisymm hrel hpos

/-- The finite-base hypothesis in `eq_one_of_same_total_bound` follows
directly from an explicitly supplied finite transcendence basis. -/
theorem eq_one_of_same_total_bound_of_finite_basis
    {k E F κ ι : Type u}
    [Field k] [Field E] [Field F] [Field κ] [Fintype ι]
    [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]
    [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (basis : ι → E) (hbasis : IsTranscendenceBasis k basis)
    (hκalg : Algebra.IsAlgebraic E κ)
    (hbound : Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1)
    (htrans : Algebra.Transcendental E F) :
    Algebra.trdeg E F = 1 := by
  have hEfinite : Algebra.trdeg k E < Cardinal.aleph0 := by
    rw [← hbasis.cardinalMk_eq_trdeg]
    rw [Cardinal.mk_fintype]
    exact Cardinal.natCast_lt_aleph0
  exact eq_one_of_same_total_bound hEfinite hκalg hbound htrans

/-- A nonzero parameter in a local domain proves the required lower bound
after embedding that domain into the component field. -/
theorem eq_one_of_same_total_bound_of_parameter
    {k E V F κ : Type u}
    [Field k] [Field E] [CommRing V] [IsDomain V] [IsLocalRing V]
    [Field F] [Field κ]
    [Algebra k E] [Algebra E V] [Algebra E F] [Algebra V F]
    [IsScalarTower E V F] [Algebra k F] [IsScalarTower k E F]
    [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (hVF : Function.Injective (algebraMap V F))
    (x : V) (hx0 : x ≠ 0) (hxM : x ∈ IsLocalRing.maximalIdeal V)
    (hEfinite : Algebra.trdeg k E < Cardinal.aleph0)
    (hκalg : Algebra.IsAlgebraic E κ)
    (hbound : Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1) :
    Algebra.trdeg E F = 1 := by
  let f : V →ₐ[E] F := IsScalarTower.toAlgHom E V F
  have hnot : ¬ IsAlgebraic E (f x) := by
    intro hfx
    have hxalg : IsAlgebraic E x :=
      (isAlgebraic_algHom_iff f hVF).mp (by simpa [f] using hfx)
    exact Stafford38.Geometry.DVRParameterSmoothness.not_isAlgebraic_of_nonzero_mem_maximalIdeal
      hx0 hxM hxalg
  have htransx : Transcendental E (f x) := hnot
  have htrans : Algebra.Transcendental E F := ⟨f x, htransx⟩
  exact eq_one_of_same_total_bound hEfinite hκalg hbound htrans

/-- The finite-basis version packages the cardinal-finiteness step together
with the actual local-parameter lower bound. -/
theorem eq_one_of_same_total_bound_of_finite_basis_and_parameter
    {k E V F κ ι : Type u}
    [Field k] [Field E] [Fintype ι] [CommRing V] [IsDomain V] [IsLocalRing V]
    [Field F] [Field κ]
    [Algebra k E] [Algebra E V] [Algebra E F] [Algebra V F]
    [IsScalarTower E V F] [Algebra k F] [IsScalarTower k E F]
    [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (basis : ι → E) (hbasis : IsTranscendenceBasis k basis)
    (hVF : Function.Injective (algebraMap V F))
    (x : V) (hx0 : x ≠ 0) (hxM : x ∈ IsLocalRing.maximalIdeal V)
    (hκalg : Algebra.IsAlgebraic E κ)
    (hbound : Algebra.trdeg k F ≤ Algebra.trdeg k κ + 1) :
    Algebra.trdeg E F = 1 := by
  have hEfinite : Algebra.trdeg k E < Cardinal.aleph0 := by
    rw [← hbasis.cardinalMk_eq_trdeg]
    rw [Cardinal.mk_fintype]
    exact Cardinal.natCast_lt_aleph0
  exact eq_one_of_same_total_bound_of_parameter hVF x hx0 hxM
    hEfinite hκalg hbound



end Stafford38.Geometry.SameWitnessRelativeTranscendenceDegree
