module
public import Stafford38.Geometry.SameWitness.CommonOpenArc
public import Stafford38.Geometry.ActualOptionCommonOpenColumns
public import Stafford38.Geometry.ActualCommonOpenCompletionDerivation
public import Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace Stafford38.Geometry.SameWitness
open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
  Stafford38.Geometry.ActualOptionCommonOpenColumns
  Stafford38.Geometry.EtaleGenericOpenTransport
  Stafford38.Geometry.GeneralDivisorialVisibleFrame
  Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
  Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
universe u

/-- The existing point-local column theorem yields the common-open position.
The ring variables stay abstract while its required instances are installed. -/
private theorem commonOpen_position_of_pointColumns
    {k B Q : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing B] [CommSemiring Q]
    {d n : ℕ} (coeff : k →+* B) (qToB : Q →+* B)
    (fFin : @AlgHom k (MvPolynomial (Option (Fin d)) k) B _ _ _ _ coeff.toAlgebra)
    (M : Ideal B) [M.IsPrime] [M.IsMaximal]
    : letI : Algebra k B := coeff.toAlgebra
      letI : Algebra Q B := qToB.toAlgebra
      ∀ (f : Q) (e : Localization.Away f ≃ₐ[Q]
        Localization.Away (algebraMap Q B f)) (g : Q)
      (eM : (B ⧸ M) ≃ₐ[k] k) (alpha : Fin d → k)
      (hf : IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM alpha) (algebraMap Q B f)))
      (hunitM : ∀ b, b ∉ M → IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := B) M eM alpha) b))
      (hg : IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM alpha) (algebraMap Q B g)))
      (n : ℕ) (qT : Fin (n + 1) → Localization.AtPrime M)
      (qU : Fin (n + 1) → genericOpenExtraAwayB M f e g)
      (hq : ∀ i, qU i = pointLocalToCommonOpen (A := B) M f e g (qT i))
      (hEtM :
      let R := MvPolynomial (Option (Fin d)) k
      letI : Algebra R B := fFin.toRingHom.toAlgebra
      letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
        ext c; exact (fFin.commutes c).symm)
      letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
      letI : Algebra R (Localization.AtPrime M) := inferInstance
      Algebra.FormallyEtale R (Localization.AtPrime M)) :
      ∀ i, genericArcToGenericOpenExtraAwayB M f e
      (originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := B) M eM alpha) hf hunitM g hg (qU i) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (tiltedArc (k := k) alpha
          (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM (qT i))) := by
  intro f e g eM alpha hf hunitM hg n qT qU hq hEtM
  let R := MvPolynomial (Option (Fin d)) k
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    ext c; exact (fFin.commutes c).symm)
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra R (Localization.AtPrime M) := inferInstance
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  exact (actual_option_columns (k := k) (d := d) (A := B) M f e g eM alpha
    hf hunitM hg n qT qU hq).1

/-- The selected same-witness columns have the prescribed tilted positions
on the common open (paper proof, common-open column position step). -/
structure CommonOpenPositionData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords) where
  qPre : Fin (m + 1) → MvPowerSeries
    (Fin (@Fintype.card coords.t coords.htFinite + 1)) k
  qL : Fin (m + 1) → LaurentSeries k
  hchartPre : qPre (Fin.succ setup.j) = 1
  hcoords : ∀ i, arc.common.qU i = genericOpenExtraAwayBMap
    arc.common.M setup.f setup.e arc.common.g
    (actualNormalizedProjectiveColumnInIntegralClosure hm P w i)
  hpositionL : ∀ i, arc.rhoU (arc.common.qU i) = qL i

/-- Build the positions from the retained point-local columns and their
common-open images, preserving the same witness throughout. -/
theorem commonOpenPositionData_of_arc
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords) :
    CommonOpenPositionData hm P w setup coords arc := by
  classical
  let d := @Fintype.card coords.t coords.htFinite
  let B := actualSelectedNormalization P w
  let Q := actualSelectedChartAlgebra P w
  let qB : Fin (m + 1) → B :=
    actualNormalizedProjectiveColumnInIntegralClosure hm P w
  let qPre : Fin (m + 1) → MvPowerSeries (Fin (d + 1)) k := fun i =>
    localToFinSuccPowerSeries (k := k) (B := B) (d := d)
      arc.common.M arc.common.eM (arc.common.qT i)
  have hchartPre : qPre (Fin.succ setup.j) = 1 := by
    simp [qPre, arc.common.qT, coords.hqchartB, setup.hchart]
  have hf := arc.hf
  rw [arc.hcanonicalRhoA] at hf
  have hunitM := arc.hunitM
  rw [arc.hcanonicalRhoA] at hunitM
  have hg := arc.hg
  rw [arc.hcanonicalRhoA] at hg
  have hcanonicalRhoU : arc.rhoU =
      genericArcToGenericOpenExtraAwayB arc.common.M setup.f setup.e
        (originalToPointLocalFinSuccArcLaurentSeries
          (k := k) (d := d) (A := B) arc.common.M arc.common.eM arc.common.alpha)
        hf hunitM arc.common.g hg := by
    simpa only [arc.hcanonicalRhoA] using arc.hcanonicalRhoU
  have hcols := commonOpen_position_of_pointColumns
    (coeff := coords.coeff)
    (qToB := chartSubalgebraToIntegralClosure Q)
    (fFin := coords.fFin) arc.common.M setup.f setup.e arc.common.g arc.common.eM arc.common.alpha
    hf hunitM hg (n := m) arc.common.qT arc.common.qU arc.common.hqUPoint arc.common.hEtM
  have hcoords : ∀ i, arc.common.qU i = genericOpenExtraAwayBMap
      arc.common.M setup.f setup.e arc.common.g (qB i) := by
    intro i
    calc
      arc.common.qU i = pointLocalToCommonOpen (A := B) arc.common.M setup.f setup.e
          arc.common.g (arc.common.qT i) := arc.common.hqUPoint i
      _ = pointLocalToCommonOpen (A := B) arc.common.M setup.f setup.e
          arc.common.g (algebraMap B (Localization.AtPrime arc.common.M) (qB i)) := rfl
      _ = genericOpenExtraAwayBMap arc.common.M setup.f setup.e arc.common.g (qB i) := by
        have h := congrArg (fun φ : B →+* arc.common.U => φ (qB i))
          (pointLocalToCommonOpen_comp_algebraMap (A := B)
            arc.common.M setup.f setup.e arc.common.g)
        simpa only [RingHom.comp_apply] using h
  let qL : Fin (m + 1) → LaurentSeries k :=
    laurentColumn (fun i => tiltedArc arc.common.alpha (qPre i))
  have hpositionL : ∀ i, arc.rhoU (arc.common.qU i) = qL i := by
    intro i
    rw [hcanonicalRhoU]
    simpa [qL, qPre] using hcols i
  exact ⟨qPre, qL, hchartPre, hcoords, hpositionL⟩

end Stafford38.Geometry.SameWitness

end
