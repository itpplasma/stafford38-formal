import PaperPairChallenge
import Stafford38.TorsionCyclicity

namespace Stafford38PaperPairChallenge

theorem pairGeneratorStatement_consumer : pairGeneratorStatement.{u, v} := by
  intro A _ M _ _ x y d F R S hx hy hcert
  exact Stafford38.TorsionCyclicity.span_adjusted_pair_eq_span_pair x y d F R S hx hy hcert

#print axioms pairGeneratorStatement_consumer
end Stafford38PaperPairChallenge
