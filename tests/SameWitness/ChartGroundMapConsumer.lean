module
public import Stafford38.Geometry.SameWitness.ChartGroundMap

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness.ChartGroundMapConsumer

open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap

universe u v w

/-- Consumer for the ground-map lemma of the original-affine chart:
`Stafford38.Geometry.SameWitness.originalAffineChartToCommonOpen_groundMap`
is restated literally and proved by applying that theorem. -/
theorem originalAffineChartToCommonOpen_groundMap_consumer
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    {B : Type w} [CommRing B] [Algebra Q B]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q)
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let U := genericOpenExtraAwayB M f e g
    letI : Semiring U := (inferInstance : CommSemiring U).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
    (originalAffineChartToCommonOpen P j hxj hsel M f e).comp
        (algebraMap k (OriginalAffineChartQuotient (k := k) P)) =
      (algebraMap Q U).comp (algebraMap k Q) := by
  exact Stafford38.Geometry.SameWitness.originalAffineChartToCommonOpen_groundMap
    P j hxj hsel M f e

#print axioms originalAffineChartToCommonOpen_groundMap_consumer

end Stafford38.Geometry.SameWitness.ChartGroundMapConsumer
