import Stafford38.Geometry.PaperGenericTangentRank

set_option autoImplicit false

namespace Stafford38.Geometry.PaperVisibleFrameFieldRank

open IsLocalRing
open Stafford38.Geometry.DivisorTangentLattice
open Stafford38.Geometry.PaperGenericTangentRank

universe u v

theorem component_fraction_field_rank_bound
    {k V F : Type u}
    [instFieldK : Field k] [instCharZeroK : CharZero k]
    [instCommRingV : CommRing V] [instLocalV : IsLocalRing V]
    [instFieldF : Field F]
    [instAlgebraKV : Algebra k V] [instAlgebraKF : Algebra k F]
    [instAlgebraVF : Algebra V F] [instTower : IsScalarTower k V F]
    {ι : Type v} [instFintype : Fintype ι]
    (D : VisibleDivisorFrame (V := V) (KaehlerDifferential.D k F) ι)
    (hmax : maximalIdeal V = Ideal.span {D.t})
    (himage : ∀ ω : Ω[V⁄k],
      KaehlerDifferential.map k k V F ω ∈ D.W)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun j : ι ↦ residue V (D.Q j)) : IntermediateField k (ResidueField V))
      (ResidueField V))
    (x : ι → F)
    (hcoordinate : ∀ j,
      x j = algebraMap V F (D.Q j) / algebraMap V F D.Q₀)
    (hgen : IntermediateField.adjoin k (Set.range x) = ⊤) :
    Module.finrank F (Ω[F⁄k]) ≤ Module.finrank (ResidueField V) (Ω[ResidueField V⁄k]) + 1 := by
  exact @componentFractionField_kaehler_finrank_le_residue_add_one
    k V F instFieldK instCharZeroK instCommRingV instLocalV instFieldF
    instAlgebraKV instAlgebraKF instAlgebraVF instTower ι instFintype
    D hmax himage halg x hcoordinate hgen

#print axioms component_fraction_field_rank_bound

end Stafford38.Geometry.PaperVisibleFrameFieldRank
