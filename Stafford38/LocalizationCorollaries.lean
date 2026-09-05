import Stafford38.Statement
import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity
import AlgebraicAnalysis.Ore.RightLocalization

/-! Right Ore localization corollaries for the Stafford 3.8 identity.
The generic unit-denominator transport proof lives in AlgebraicAnalysis. -/

namespace Stafford38.LocalizationCorollaries

universe u v

abbrev S38 := AlgebraicAnalysis.TwoGeneratorIdentity

/-- A fraction-clearing formulation sufficient to transport `S38`. The unit
condition concerns only the denominator chosen for the given fraction. -/
theorem s38_of_rightClearing
    {R : Type u} {L : Type v} [Ring R] [Ring L]
    {f : R →+* L} (hR : S38 R)
    (hclear : ∀ q : L, q ≠ 0 →
      ∃ a s : R, IsUnit (f s) ∧ q * f s = f a) : S38 L :=
  AlgebraicAnalysis.TwoGeneratorIdentity.of_rightUnitClearing hR hclear

/- Compatibility exports for the reusable right Ore localization API. -/
export AlgebraicAnalysis.OreRightLocalization
  (oppositeSubmonoid RightOreLocalization rightNumeratorRingHom rightOre_clear)

/-- Stafford 3.8 is preserved by genuine right Ore localization. -/
theorem s38_rightOreLocalization
    {R : Type u} [Ring R] {S : Submonoid R}
    [OreLocalization.OreSet (oppositeSubmonoid S)]
    (hR : S38 R) : S38 (RightOreLocalization R S) :=
  AlgebraicAnalysis.TwoGeneratorIdentity.of_rightOreLocalization hR

#print axioms s38_of_rightClearing
#print axioms rightOre_clear
#print axioms s38_rightOreLocalization

end Stafford38.LocalizationCorollaries
