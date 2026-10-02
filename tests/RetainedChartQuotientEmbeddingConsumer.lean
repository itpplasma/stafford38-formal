import Stafford38.Geometry.RetainedChartQuotientEmbedding

noncomputable section
set_option autoImplicit false

open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.RetainedChartQuotientEmbedding

universe u

/-- Independent semantic consumer: the kernel of the normalized chart map to the
retained valuation ring is exactly the dehomogenized homogeneous component ideal. -/
theorem retained_chart_map_kernel_exact
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {V : Type u} [CommRing V]
    (coeff : k →+* V)
    (ι : V →+* ComponentFractionField P)
    (hι : Function.Injective ι)
    (hcoeff : ι.comp coeff = algebraMap k (ComponentFractionField P))
    (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1)
    (scale : ComponentFractionField P)
    (hq : ∀ a, ι (q a) = scale * componentProjectivePoint P a)
    (a : MvPolynomial (Fin m) k) :
    a ∈ componentChartEquationIdeal P chart e ↔
      componentChartEquationQuotientMap P coeff ι hι hcoeff q chart e
        hqchart scale hq (Ideal.Quotient.mk
          (componentChartEquationIdeal P chart e) a) = 0 := by
  let f := componentChartEquationQuotientMap P coeff ι hι hcoeff q chart e
    hqchart scale hq
  have hchart : componentProjectivePoint P chart ≠ 0 := by
    have hscale : scale * componentProjectivePoint P chart = 1 := by
      simpa [hqchart] using (hq chart).symm
    intro hz
    rw [hz, mul_zero] at hscale
    exact one_ne_zero hscale.symm
  let evalF : MvPolynomial (Fin m) k →+* ComponentFractionField P :=
    MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
      (chartGenericPoint P chart e)
  have heq : componentChartEquationIdeal P chart e = RingHom.ker evalF := by
    simpa [evalF] using componentChartEquationIdeal_eq_genericEvalKer P chart e hchart
  constructor
  · intro ha
    have ha' : a ∈ RingHom.ker evalF := heq.symm ▸ ha
    apply hι
    calc
      ι (f (Ideal.Quotient.mk (componentChartEquationIdeal P chart e) a)) = evalF a :=
        componentChartEquationQuotientMap_mk_comp_genericEval
          P coeff ι hι hcoeff q chart e hqchart scale hq a
      _ = 0 := RingHom.mem_ker.mp ha'
      _ = ι 0 := (map_zero ι).symm
  · intro h
    have heval : evalF a = 0 := by
      calc
        evalF a = ι (f (Ideal.Quotient.mk (componentChartEquationIdeal P chart e) a)) :=
          (componentChartEquationQuotientMap_mk_comp_genericEval
            P coeff ι hι hcoeff q chart e hqchart scale hq a).symm
        _ = ι 0 := congrArg ι h
        _ = 0 := map_zero ι
    exact heq ▸ RingHom.mem_ker.mpr heval

#print axioms retained_chart_map_kernel_exact
