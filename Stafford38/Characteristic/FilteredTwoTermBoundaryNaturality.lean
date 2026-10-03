module
public import AlgebraicAnalysis.Module.FilteredTwoTermBoundaryNaturality
public import Stafford38.Characteristic.FilteredTwoTermTotalActions
public import Stafford38.Characteristic.FilteredTwoTermBoundaryExhaustion

@[expose] public section

/- Compatibility exports for the neutral AlgebraicAnalysis API. -/

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (FilteredTwoTerm.PageOperator.targetBoundaryMap_naturality FilteredTwoTerm.PageOperator.totalBoundaryMap_naturality)

end Stafford38.Characteristic.FilteredTwoTermPages
