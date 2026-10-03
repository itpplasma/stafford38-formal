module
public import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

@[expose] public section

/-! Compatibility exports for reusable localized polynomial derivations. -/
namespace Stafford38.LocalizedPolynomialDerivations

export AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations
  (extendDerivation extendDerivation_compAlgebraMap derivation_ext_of_compAlgebraMap_eq
   PolynomialRing localizedPderiv localizedPderiv_compAlgebraMap
   localizedPderiv_apply_algebraMap_X localizedPderiv_comm)

end Stafford38.LocalizedPolynomialDerivations
