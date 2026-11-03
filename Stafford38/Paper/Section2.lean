module

public import Stafford38.Paper.Section2.Weyl
public import Stafford38.Paper.Section2.Filtration
public import Stafford38.Paper.Section2.Geometry
public import Stafford38.Paper.Section2.CharacteristicVariety
public import Stafford38.Paper.Section2.Symplectic

@[expose] public section

/-!
# Section 2 of the paper: preliminaries

* `Stafford38.Paper.Section2.Weyl`: Definition 2.1 (`IsTorsion`, `IsCyclic`)
  and Convention 2.2 (`x₁`, `p`, `transverse`, `C`, `C_eq_range`,
  `convention_2_2_relations`, `convention_2_2_exists`, `convention_2_2_unique`).
* `Stafford38.Paper.Section2.Filtration`: Definition 2.3 (`IsFiltration`,
  `gr`, `filtrationDegree`, `symbol`; `bernsteinFiltration`,
  `orderFiltration`, `bernsteinDegree`, `grEquivSymbolRing`) and Definition 2.4
  (`IsCompatibleFiltration`, `cyclicFiltration`, `grCyclic`, `grCyclic_good`;
  `qClass`, `cyclicFiltration_order_isCompatible` and `grCyclicEquiv`, which
  identifies `grCyclic` with `gr` of `Q_m = qF_m`).
* `Stafford38.Paper.Section2.Geometry`: Definitions 2.5–2.7
  (`CotangentBundle`, `proj`, `fibre`; `V`, `VK`, `vanishingIdealOf`,
  `maxIdealAt`) and Theorem 2.12 (`theorem_2_12`).
* `Stafford38.Paper.Section2.CharacteristicVariety`: Definitions 2.4 and 2.7 for
  every module (`IsGoodFiltration`, `CharOf`, independence of the good filtration
  `definition_2_7_independent`) and the cyclic case `Char`.
* `Stafford38.Paper.Section2.Symplectic`: Definitions 2.8–2.10
  (`IsSymplectic`, `gramMatrix`, `IsSymplecticBasis`, `omega`; `poisson`;
  `IsInvolutive`, `IsInvolutiveSet`) and Theorem 2.11 (`theorem_2_11`, general
  finitely generated modules; `theorem_2_11_cyclic`, the case `A_n(K)/I`).
-/

namespace Stafford38.Paper.Section2

#print axioms C_eq_range
#print axioms convention_2_2_exists
#print axioms convention_2_2_unique
#print axioms grEquivSymbolRing
#print axioms grCyclic_good
#print axioms grCyclicEquiv
#print axioms theorem_2_11
#print axioms theorem_2_11_cyclic
#print axioms theorem_2_12

end Stafford38.Paper.Section2
