import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Etale.Locus
import Stafford38.Geometry.ClosedPointOnDivisor

set_option autoImplicit false

namespace Stafford38.Geometry.PrescribedEtaleGroundPoint

noncomputable section

/-- Every prime in a formally étale principal open has a formally étale
local ring for the original coordinate-algebra map. -/
theorem formallyEtale_atPrime_of_away
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (f : B) (M : Ideal B) [M.IsPrime]
    (hfM : f ∉ M)
    [Algebra.FormallyEtale R (Localization.Away f)] :
    Algebra.FormallyEtale R (Localization.AtPrime M) := by
  have hopen : ↑(PrimeSpectrum.basicOpen f) ⊆ Algebra.etaleLocus R B :=
    (Algebra.basicOpen_subset_etaleLocus_iff (R := R) (A := B)).mpr inferInstance
  exact hopen (show (⟨M, inferInstance⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen f from hfM)

/-- Choose a ground point on the divisor where both the original coordinate
map is étale and an additional regularity function does not vanish. -/
theorem exists_standardEtale_neighborhood_and_formallyEtale_ground_point_avoiding
    {k R B : Type*} [Field k] [IsAlgClosed k] [CommRing R] [CommRing B]
    [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
    [Algebra.FiniteType k B] [Algebra.FinitePresentation R B]
    (p : Ideal B) [p.IsPrime] (g : B) (hgp : g ∉ p)
    (hEt : Algebra.FormallyEtale R (Localization.AtPrime p)) :
    ∃ (f : B) (M : Ideal B) (hM : M.IsMaximal),
      f ∉ p ∧ p ≤ M ∧ f ∉ M ∧ g ∉ M ∧
      Algebra.IsStandardEtale R (Localization.Away f) ∧
      Nonempty ((B ⧸ M) ≃ₐ[k] k) ∧
      (letI : M.IsMaximal := hM
       Algebra.FormallyEtale R (Localization.AtPrime M)) := by
  let : Algebra.IsEtaleAt R p := hEt
  obtain ⟨f, hfp, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) p
  have hfgp : f * g ∉ p := by
    intro h
    rcases (inferInstance : p.IsPrime).mem_or_mem h with hf | hg
    · exact hfp hf
    · exact hgp hg
  obtain ⟨M, hM, hpM, hfgM, hres⟩ :=
    Stafford38.Geometry.ClosedPointOnDivisor.exists_ground_closed_point_over_prime_avoiding
      (k := k) (R := B) p inferInstance (f * g) hfgp
  have hfM : f ∉ M := fun hf => hfgM (M.mul_mem_right g hf)
  have hgM : g ∉ M := fun hg => hfgM (M.mul_mem_left f hg)
  let : M.IsMaximal := hM
  let : Algebra.IsStandardEtale R (Localization.Away f) := hstd
  let : Algebra.FormallyEtale R (Localization.Away f) := inferInstance
  exact ⟨f, M, hM, hfp, hpM, hfM, hgM, hstd, hres,
    formallyEtale_atPrime_of_away f M hfM⟩

/-- A formally etale local map from the prescribed coordinate algebra has a standard-etale
neighborhood of the divisor prime, and that neighborhood contains a ground-rational closed
point when the target is finite type over an algebraically closed field.  The coordinate map is
the original algebra map `R → B`; this lemma does not alter or choose a replacement chart. -/
theorem exists_standardEtale_neighborhood_and_ground_point
    {k R B : Type*} [Field k] [IsAlgClosed k] [CommRing R] [CommRing B]
    [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
    [Algebra.FiniteType k B] [Algebra.FinitePresentation R B]
    (p : Ideal B) [p.IsPrime]
    (hEt : Algebra.FormallyEtale R (Localization.AtPrime p)) :
    ∃ (f : B) (M : Ideal B), f ∉ p ∧ M.IsMaximal ∧ p ≤ M ∧ f ∉ M ∧
      Algebra.IsStandardEtale R (Localization.Away f) ∧
      Nonempty ((B ⧸ M) ≃ₐ[k] k) := by
  have h1p : (1 : B) ∉ p := Ideal.one_notMem p
  obtain ⟨f, M, hM, hfp, hpM, hfM, _, hstd, hres, _⟩ :=
    exists_standardEtale_neighborhood_and_formallyEtale_ground_point_avoiding
      (k := k) (R := R) (B := B) p 1 h1p hEt
  exact ⟨f, M, hfp, hM, hpM, hfM, hstd, hres⟩

/-- The chosen ground point lies on the prescribed divisor and has a formally
étale local ring for the same coordinate map used at the divisor prime. -/
theorem exists_standardEtale_neighborhood_and_formallyEtale_ground_point
    {k R B : Type*} [Field k] [IsAlgClosed k] [CommRing R] [CommRing B]
    [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
    [Algebra.FiniteType k B] [Algebra.FinitePresentation R B]
    (p : Ideal B) [p.IsPrime]
    (hEt : Algebra.FormallyEtale R (Localization.AtPrime p)) :
    ∃ (f : B) (M : Ideal B) (hM : M.IsMaximal),
      f ∉ p ∧ p ≤ M ∧ f ∉ M ∧
      Algebra.IsStandardEtale R (Localization.Away f) ∧
      Nonempty ((B ⧸ M) ≃ₐ[k] k) ∧
      (letI : M.IsMaximal := hM
       Algebra.FormallyEtale R (Localization.AtPrime M)) := by
  have h1p : (1 : B) ∉ p := Ideal.one_notMem p
  obtain ⟨f, M, hM, hfp, hpM, hfM, _, hstd, hres, hlocal⟩ :=
    exists_standardEtale_neighborhood_and_formallyEtale_ground_point_avoiding
      (k := k) (R := R) (B := B) p 1 h1p hEt
  exact ⟨f, M, hM, hfp, hpM, hfM, hstd, hres, hlocal⟩

end
end Stafford38.Geometry.PrescribedEtaleGroundPoint
