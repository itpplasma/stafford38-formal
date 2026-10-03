module
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

@[expose] public section

/-!
# Nondegenerate symplectic planes and their orthogonal complements

An alternating nondegenerate bilinear form splits off any normalized pair
`v,w` with `B v w = 1`.  The statement is phrased with Mathlib's right
orthogonal complement convention `B u x = 0` for all `u` in the subspace.
-/

open LinearMap (BilinForm)
open Module

namespace Stafford38.LinearAlgebra.SymplecticComplement

universe u v

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/-- The two-dimensional candidate symplectic plane spanned by `v` and `w`. -/
def pairPlane (v w : V) : Submodule k V := Submodule.span k {v, w}

theorem pairComplementData [Module.Finite k V]
    (B : BilinForm k V) (hAlt : ∀ x, B x x = 0) (hB : B.Nondegenerate)
    (v w : V) (hvw : B v w = 1) :
    let U : Submodule k V := Submodule.span k {v, w}
    (B.restrict U).Nondegenerate ∧
      IsCompl U (B.orthogonal U) ∧
      (B.restrict (B.orthogonal U)).Nondegenerate ∧
      Module.finrank k (B.orthogonal U) + 2 = Module.finrank k V := by
  let U : Submodule k V := pairPlane v w
  have hAlt' : B.IsAlt := hAlt
  have hRefl : B.IsRefl := hAlt'.isRefl
  have hwv : B w v = -1 := by
    simpa [hvw] using (hAlt'.neg_eq v w).symm
  have hvU : v ∈ U := Submodule.subset_span (by simp)
  have hwU : w ∈ U := Submodule.subset_span (by simp)
  have hdisj : Disjoint U (B.orthogonal U) := by
    rw [Submodule.disjoint_def]
    intro x hxU hxO
    obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair).1 (by simpa [U, pairPlane] using hxU)
    have hvx : B v x = 0 := hxO v hvU
    have hwx : B w x = 0 := hxO w hwU
    rw [← hab, BilinForm.add_right, BilinForm.smul_right, BilinForm.smul_right,
      hAlt v, hvw] at hvx
    rw [← hab, BilinForm.add_right, BilinForm.smul_right, BilinForm.smul_right,
      hwv, hAlt w] at hwx
    have hb : b = 0 := by simpa using hvx
    have ha : a = 0 := by simpa [mul_comm] using hwx
    rw [← hab, ha, hb]
    simp
  have hU_nd : (B.restrict U).Nondegenerate :=
    BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hRefl hdisj
  have hcompl : IsCompl U (B.orthogonal U) :=
    BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hRefl hU_nd
  have hdouble : B.orthogonal (B.orthogonal U) = U :=
    BilinForm.orthogonal_orthogonal hB hRefl U
  have hdisj' : Disjoint (B.orthogonal U) (B.orthogonal (B.orthogonal U)) := by
    rw [hdouble]
    exact hcompl.disjoint.symm
  have horth_nd : (B.restrict (B.orthogonal U)).Nondegenerate :=
    BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hRefl hdisj'
  have hli : LinearIndependent k ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hvsum : B (a • v + b • w) w = 0 := by rw [hab, BilinForm.zero_left]
    have hwsum : B (a • v + b • w) v = 0 := by rw [hab, BilinForm.zero_left]
    rw [BilinForm.add_left, BilinForm.smul_left, BilinForm.smul_left,
      hvw, hAlt w] at hvsum
    rw [BilinForm.add_left, BilinForm.smul_left, BilinForm.smul_left,
      hAlt v, hwv] at hwsum
    constructor
    · simpa using hvsum
    · simpa [mul_comm] using hwsum
  have hU_finrank : finrank k U = 2 := by
    have hUeq : U = Submodule.span k (Set.range ![v, w]) := by
      rw [show Set.range ![v, w] = ({v, w} : Set V) by
        ext x
        simp [or_comm]]
      rfl
    rw [hUeq]
    simpa using (finrank_span_eq_card hli)
  have hdim : finrank k (B.orthogonal U) = finrank k V - 2 := by
    rw [BilinForm.finrank_orthogonal hB U, hU_finrank]
  refine ⟨hU_nd, hcompl, horth_nd, ?_⟩
  change finrank k (B.orthogonal U) + 2 = finrank k V
  rw [hdim]
  have hle : 2 ≤ finrank k V := by
    rw [← hU_finrank]
    exact Submodule.finrank_le _
  omega

end Stafford38.LinearAlgebra.SymplecticComplement
