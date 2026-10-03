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
open Stafford38.Geometry.SelectedResidueCoefficientLocalization
  Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
  Stafford38.Geometry.ActualOptionColumnBinding
  Stafford38.Geometry.ActualSelectedNormalizationChartTransport
  Stafford38.Geometry.ActualCommonOpenCompletionDerivation
  Stafford38.Geometry.ActualOptionCommonOpenColumns
  Stafford38.Geometry.EtaleGenericOpenTransport
  Stafford38.Geometry.GeneralDivisorialVisibleFrame
  Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
  Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
universe u

/-- The prescribed completion chart as a ring homomorphism, with all
coordinate scalar structures installed only over the abstract ring B. -/
noncomputable def pointLocalPowerSeriesChart
    {k B : Type u} [Field k] [CommRing B] {d : ℕ}
    (coeff : k →+* B)
    (fFin : @AlgHom k (MvPolynomial (Option (Fin d)) k) B _ _ _ _ coeff.toAlgebra)
    (hfinite : @Algebra.FiniteType k B _ _ coeff.toAlgebra)
    (M : Ideal B) [M.IsMaximal] :
    letI : Algebra k B := coeff.toAlgebra
    let R := MvPolynomial (Option (Fin d)) k
    letI : Algebra R B := fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
      ext c; exact (fFin.commutes c).symm)
    letI : Algebra.FiniteType k B := hfinite
    letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
    ∀ (eM : (B ⧸ M) ≃ₐ[k] k)
    (hEtM : Algebra.FormallyEtale R (Localization.AtPrime M)),
    Localization.AtPrime M →+* MvPowerSeries (Fin (d + 1)) k := by
  letI : Algebra k B := coeff.toAlgebra
  dsimp only
  intro eM hEtM
  let R := MvPolynomial (Option (Fin d)) k
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    ext c; exact (fFin.commutes c).symm)
  letI : Algebra.FiniteType k B := hfinite
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  exact (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM).toRingHom

/-- The existing point-local column theorem yields the common-open position.
The ring variables stay abstract while its required instances are installed. -/
theorem commonOpen_position_of_pointColumns
    {k B Q : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing B] [CommRing Q]
    {d : ℕ} (coeff : k →+* B) (qToB : Q →+* B)
    (fFin : @AlgHom k (MvPolynomial (Option (Fin d)) k) B _ _ _ _ coeff.toAlgebra)
    (hfinite : @Algebra.FiniteType k B _ _ coeff.toAlgebra)
    (M : Ideal B) [M.IsPrime] [M.IsMaximal]
    : letI : Algebra k B := coeff.toAlgebra
    letI : Algebra Q B := qToB.toAlgebra
    let R := MvPolynomial (Option (Fin d)) k
    letI : Algebra R B := fFin.toRingHom.toAlgebra
    letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
      ext c; exact (fFin.commutes c).symm)
    letI : Algebra.FiniteType k B := hfinite
    letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
      ∀ (f : Q) (e : Localization.Away f ≃ₐ[Q]
        Localization.Away (algebraMap Q B f)) (g : Q)
      (eM : (B ⧸ M) ≃ₐ[k] k)
      (hEtM : Algebra.FormallyEtale R (Localization.AtPrime M)),
      letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
      ∀ (alpha : Fin d → k)
      (hf : IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM alpha) (algebraMap Q B f)))
      (hunitM : ∀ b, b ∉ M → IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := B) M eM alpha) b))
      (hg : IsUnit ((originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM alpha) (algebraMap Q B g)))
      (n : ℕ) (qT : Fin (n + 1) → Localization.AtPrime M)
      (qU : Fin (n + 1) → genericOpenExtraAwayB M f e g)
      (hq : ∀ i, qU i = pointLocalToCommonOpen (A := B) M f e g (qT i))
      (rho : genericOpenExtraAwayB M f e g →+* LaurentSeries k)
      (hcanonical : rho = genericArcToGenericOpenExtraAwayB M f e
        (originalToPointLocalFinSuccArcLaurentSeries
          (k := k) (d := d) (A := B) M eM alpha) hf hunitM g hg)
      (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
      (hqPre : qPre = fun i =>
        pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM (qT i))
      (qL : Fin (n + 1) → LaurentSeries k)
      (hqL : qL = fun i => algebraMap (PowerSeries k) (LaurentSeries k)
        (tiltedArc alpha (qPre i))),
      ∀ i, rho (qU i) = qL i := by
  letI : Algebra k B := coeff.toAlgebra
  letI : Algebra Q B := qToB.toAlgebra
  dsimp only
  intro f e g eM hEtM alpha hf hunitM hg n qT qU hq
    rho hcanonical qPre hqPre qL hqL
  let R := MvPolynomial (Option (Fin d)) k
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    ext c; exact (fFin.commutes c).symm)
  letI : Algebra.FiniteType k B := hfinite
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra R (Localization.AtPrime M) := inferInstance
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  have hchart (x : Localization.AtPrime M) :
      pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM x =
        localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM x := by
    unfold pointLocalPowerSeriesChart
    dsimp only [id_eq]
    exact congrFun (AlgHom.coe_toRingHom
      (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM)) x
  intro i
  rw [hcanonical, hqL, hqPre]
  exact ((actual_option_columns (k := k) (d := d) (A := B) M f e g eM alpha
    hf hunitM hg n qT qU hq).1 i).trans
      (congrArg (fun z => algebraMap (PowerSeries k) (LaurentSeries k)
        (tiltedArc alpha z)) (hchart (qT i)).symm)


/-- Equality of source arcs transports the localization lift together with
its dependent unit certificates, without installing coefficient actions. -/
theorem genericOpenArc_eq_of_source_eq
    {Q B L : Type u} [CommRing Q] [CommRing B] [Algebra Q B] [Field L]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q] Localization.Away (algebraMap Q B f))
    (g : Q) (rho canonical : B →+* L)
    (rhoU : genericOpenExtraAwayB M f e g →+* L)
    (hf : IsUnit (rho (algebraMap Q B f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (rho b))
    (hg : IsUnit (rho (algebraMap Q B g)))
    (hsource : rho = canonical)
    (hU : rhoU = genericArcToGenericOpenExtraAwayB M f e rho hf hunitM g hg) :
    rhoU = genericArcToGenericOpenExtraAwayB M f e canonical
      (hsource ▸ hf) (hsource ▸ hunitM) g (hsource ▸ hg) := by
  cases hsource
  exact hU

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
  hqPre :
    letI : arc.common.M.IsMaximal := arc.common.hM
    qPre = fun i => pointLocalPowerSeriesChart
    coords.coeff coords.fFin coords.hBfinite arc.common.M arc.common.eM
    arc.common.hEtM (arc.common.qT i)
  hchartPre : qPre (Fin.succ setup.j) = 1
  hcoords :
    letI : arc.common.M.IsMaximal := arc.common.hM
    ∀ i, arc.common.qU i = genericOpenExtraAwayBMap
    arc.common.M setup.f setup.e arc.common.g
    (actualNormalizedProjectiveColumnInIntegralClosure hm P w i)
  hpositionL : ∀ i, arc.rhoU (arc.common.qU i) = qL i

/-- Build the positions from the retained point-local columns and their
common-open images, preserving the same witness throughout. -/
noncomputable def commonOpenPositionData_of_arc
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords) :
    CommonOpenPositionData hm P w setup coords arc := by
  classical
  letI : arc.common.M.IsMaximal := arc.common.hM
  let d := @Fintype.card coords.t coords.htFinite
  let B := actualSelectedNormalization P w
  let Q := actualSelectedChartAlgebra P w
  let qB : Fin (m + 1) → B :=
    actualNormalizedProjectiveColumnInIntegralClosure hm P w
  let qPre : Fin (m + 1) → MvPowerSeries (Fin (d + 1)) k := fun i =>
    pointLocalPowerSeriesChart coords.coeff coords.fFin coords.hBfinite
      arc.common.M arc.common.eM arc.common.hEtM (arc.common.qT i)
  have hchartPre : qPre (Fin.succ setup.j) = 1 := by
    have hqT : arc.common.qT (Fin.succ setup.j) = 1 := by
      change algebraMap B (Localization.AtPrime arc.common.M)
        (actualNormalizedProjectiveColumnInIntegralClosure hm P w
          (Fin.succ setup.j)) = 1
      rw [← setup.hchart, coords.hqchartB]
      exact map_one _
    change (pointLocalPowerSeriesChart coords.coeff coords.fFin coords.hBfinite
      arc.common.M arc.common.eM arc.common.hEtM)
      (arc.common.qT (Fin.succ setup.j)) = 1
    rw [hqT, map_one]
  have hf := arc.hf
  rw [arc.hcanonicalRhoA] at hf
  have hunitM := arc.hunitM
  rw [arc.hcanonicalRhoA] at hunitM
  have hg := arc.hg
  rw [arc.hcanonicalRhoA] at hg
  have hcanonicalRhoU := genericOpenArc_eq_of_source_eq
    arc.common.M setup.f setup.e arc.common.g arc.rhoA _ arc.rhoU
    arc.hf arc.hunitM arc.hg arc.hcanonicalRhoA arc.hcanonicalRhoU
  let qL : Fin (m + 1) → LaurentSeries k :=
    Stafford38.Geometry.FormalDivisorLaurentConormal.laurentColumn
      (fun i => tiltedArc arc.common.alpha (qPre i))
  have hcols := commonOpen_position_of_pointColumns
    (k := k) (B := B) (Q := Q) (d := d)
    (coeff := coords.coeff)
    (qToB := chartSubalgebraToIntegralClosure Q)
    (fFin := coords.fFin) coords.hBfinite arc.common.M setup.f setup.e arc.common.g arc.common.eM arc.common.hEtM arc.common.alpha
    hf hunitM hg (n := m) arc.common.qT arc.common.qU arc.common.hqUPoint
    arc.rhoU hcanonicalRhoU qPre rfl qL rfl
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
  exact ⟨qPre, qL, rfl, hchartPre, hcoords, hcols⟩

end Stafford38.Geometry.SameWitness

end
