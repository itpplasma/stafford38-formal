import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

set_option autoImplicit false

namespace Stafford38.Geometry.ResidueLiftIndependence

/-- Algebraic independence survives lifting elements from a residue field into
an injectively embedded local domain. A polynomial relation among the lifts
would reduce to the same relation among their residues. -/
theorem algebraicIndependent_of_residue
    {k V K ι : Type*} [Field k] [CommRing V] [IsLocalRing V]
    [Field K] [Algebra k V] [Algebra k K] [Algebra V K]
    [IsScalarTower k V K] [Algebra k (IsLocalRing.ResidueField V)]
    [IsScalarTower k V (IsLocalRing.ResidueField V)]
    (hinj : Function.Injective (algebraMap V K))
    (x : ι → V)
    (hx : AlgebraicIndependent k (fun i ↦ IsLocalRing.residue V (x i))) :
    AlgebraicIndependent k (fun i ↦ algebraMap V K (x i)) := by
  rw [algebraicIndependent_iff]
  intro p hp
  have hcompK :
      (algebraMap V K) (MvPolynomial.aeval x p) =
        MvPolynomial.aeval (fun i ↦ algebraMap V K (x i)) p := by
    have hcoeff : (algebraMap V K).comp (algebraMap k V) = algebraMap k K := by
      ext c
      exact (IsScalarTower.algebraMap_apply k V K c).symm
    rw [MvPolynomial.map_aeval, MvPolynomial.aeval_eq_eval₂Hom, hcoeff]
  have hzeroV : MvPolynomial.aeval x p = 0 := by
    apply hinj
    rw [map_zero, hcompK]
    exact hp
  have hcompκ : IsLocalRing.residue V (MvPolynomial.aeval x p) =
      MvPolynomial.aeval (fun i ↦ IsLocalRing.residue V (x i)) p := by
    have hcoeff : (IsLocalRing.residue V).comp (algebraMap k V) =
        algebraMap k (IsLocalRing.ResidueField V) := by
      ext c
      exact (IsScalarTower.algebraMap_apply k V (IsLocalRing.ResidueField V) c).symm
    rw [MvPolynomial.map_aeval, MvPolynomial.aeval_eq_eval₂Hom, hcoeff]
  have hzeroκ : MvPolynomial.aeval (fun i ↦ IsLocalRing.residue V (x i)) p = 0 := by
    rw [← hcompκ, hzeroV, map_zero]
  exact hx.eq_zero_of_aeval_eq_zero p hzeroκ


end Stafford38.Geometry.ResidueLiftIndependence
