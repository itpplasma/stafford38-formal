module
public import Stafford38.Geometry.SameWitness.EndpointOfAlgHoms
public import Stafford38.Geometry.SameWitness.ChartSetup
public import Stafford38.Geometry.SameWitness.CoordinatePresentation
public import Stafford38.Geometry.SameWitness.CommonOpen
public import Stafford38.Geometry.SameWitness.CommonOpenArc
public import Stafford38.Geometry.SameWitness.CommonOpenPositions
public import Stafford38.Geometry.SameWitness.CommonOpenColumns
public import Stafford38.Geometry.SameWitness.CommonOpenEtale

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.PrescribedAffineResidueCompletion
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

universe u

/-- The smooth affine-conormal axis lies in the fibre closure through the
retained ground-point output and its same-witness common-open arc. -/
theorem axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hpoint : actualSameWitnessGroundPointOutput hm P w)
    (hsmoothOpen : ∃ fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal,
      fbar ≠ 0 ∧ Algebra.Smooth k (Localization.Away fbar)) :
    (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal)) := by
  classical
  obtain ⟨setup⟩ := nonempty_chartSetup hm P w hsmoothOpen
  obtain ⟨coords⟩ := nonempty_coordinatePresentation hm P w setup hpoint
  obtain ⟨common⟩ := nonempty_commonOpenData hm P w setup coords hpoint
  obtain ⟨arc⟩ := exists_commonOpenArcData hm P w setup coords common
  let arcData := arc.common
  obtain ⟨etale⟩ := nonempty_commonOpenEtaleData hm P w setup coords arc
  let positions := commonOpenPositionData_of_arc hm P w setup coords arc etale
  let cols := commonOpenColumnsData_of_arc hm P w setup coords arc etale positions
  let d := @Fintype.card coords.t coords.htFinite
  let beta : Fin d → k := fun z =>
    residueCoordinates arcData.M arcData.eM (some z)
  let u₀ : MvPowerSeries (Fin (d + 1)) k :=
    localToFinSuccPowerSeries (k := k) (B := actualSelectedNormalization P w)
      (d := d) arcData.M arcData.eM arcData.u0
  let u₁ : MvPowerSeries (Fin (d + 1)) k :=
    localToFinSuccPowerSeries (k := k) (B := actualSelectedNormalization P w)
      (d := d) arcData.M arcData.eM arcData.u1
  exact axis_mem_smoothConormalFibreProjection_closure_of_algHoms
    (k := k) (E := arc.common.U) (n := m) (d := d) (I := P.asIdeal)
    etale.φk etale.ψU etale.hφEtale etale.hψEtale arc.rhoU arc.hgroundU
    arc.common.qU positions.qPre coords.rows w.column.chart (⟨0, hm⟩ : Fin m)
    w.differential.core.D.a
    (w.differential.core.D.a + w.differential.core.D.e)
    beta arcData.alpha u₀ u₁ positions.hchartPre arcData.hdata
    positions.hpositionL cols.htransverse cols.hraw arcData.hchartU
    setup.p setup.fbar setup.hrep setup.hsmooth cols.hnumerator

end Stafford38.Geometry.SameWitness

end
