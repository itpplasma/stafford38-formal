module
public import AlgebraicAnalysis.Module.UniformBoundaryVanishing

@[expose] public section

/- Compatibility exports for the neutral AlgebraicAnalysis API. -/

export AlgebraicAnalysis (exists_uniform_zero_of_noetherian
  exists_uniform_subsingleton_of_noetherian exists_uniform_zero_localized
  exists_uniform_subsingleton_localized)
