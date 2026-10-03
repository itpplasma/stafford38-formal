module
public import Stafford38.Geometry.SameWitness.CommonOpenPositions
public import Stafford38.Geometry.SameWitness.CommonOpenEtale

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.EtaleCotangentBasis
open Stafford38.Geometry.ActualCommonOpenCompletionDerivation
open Stafford38.Geometry.SelectedResidueCoefficientLocalization
open Stafford38.Geometry.ActualOptionColumnBinding
open Stafford38.Geometry.ActualSelectedNormalizationChartTransport
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ActualOptionCommonOpenColumns
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.HomogenizedAffineEvaluation
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart
open Stafford38.Geometry.SmoothLocalTiltedArcAxisLift
open Stafford38.Geometry.LocalizedProjectiveChartTransition

universe u

/-- The two common-open derivative identities with every scalar certificate
bound explicitly over the abstract algebra. -/
def commonOpenDerivativeIdentities
    {k U : Type u} [Field k] [CommRing U] {d n : ℕ}
    (a : Algebra (MvPolynomial (Option (Fin d)) k) U) (b : Algebra k U)
    (tower : @IsScalarTower k (MvPolynomial (Option (Fin d)) k) U
      (inferInstance : Algebra k (MvPolynomial (Option (Fin d)) k)).toSMul
      a.toSMul b.toSMul)
    (etale : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) U _ _ a)
    (rho : U →+* LaurentSeries k)
    (hground : rho.comp b.algebraMap = algebraMap k (LaurentSeries k))
    (alpha : Fin d → k) (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (qU : Fin (n + 1) → U) : Prop :=
    let R := MvPolynomial (Option (Fin d)) k
    letI : Algebra R U := a
    letI : SMul R U := a.toSMul
    letI : Algebra k U := b
    letI : SMul k U := b.toSMul
    letI : IsScalarTower k R U := tower
    letI : Algebra.FormallyEtale R U := etale
    letI : Algebra U (LaurentSeries k) :=
      RingHom.toAlgebra' rho (by intro x y; exact mul_comm _ _)
    letI : Algebra k (LaurentSeries k) :=
      RingHom.toAlgebra' (algebraMap k (LaurentSeries k))
        (by intro x y; exact mul_comm _ _)
    letI : Module k (LaurentSeries k) := Algebra.toModule
    letI : SMul k (LaurentSeries k) :=
      (Algebra.toModule : Module k (LaurentSeries k)).toSMul
    letI : IsScalarTower k U (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq' hground.symm
    letI : IsScalarTower U (LaurentSeries k) (LaurentSeries k) :=
      ⟨fun x y z => by
        change (algebraMap U (LaurentSeries k) x * y) * z = _
        exact mul_assoc _ _ _⟩
    (∀ j i, coordinateDerivation (k := k)
    (σ := Option (Fin d))
    (B := U) (L := LaurentSeries k) (some j)
    (qU i) = algebraMap (PowerSeries k) (LaurentSeries k)
      (tiltedTransverseDerivativeMatrix alpha qPre i j)) ∧
    (∀ i, algebraMap (PowerSeries k) (LaurentSeries k)
      (PowerSeries.derivative (R := k)
        (tiltedArc alpha (qPre i))) =
    coordinateDerivation (k := k)
      (σ := Option (Fin d))
      (B := U) (L := LaurentSeries k) none (qU i) +
      ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.C (alpha j)) *
        coordinateDerivation (k := k)
          (σ := Option (Fin d))
          (B := U) (L := LaurentSeries k) (some j)
          (qU i))

/-- Equal coordinate and ground actions transport the complete derivative
proposition together with its dependent tower and étale certificates. -/
theorem commonOpenDerivativeIdentities_transport
    {k U : Type u} [Field k] [CommRing U] {d n : ℕ}
    (a0 a1 : Algebra (MvPolynomial (Option (Fin d)) k) U)
    (b0 b1 : Algebra k U) (ha : a0 = a1) (hb : b0 = b1)
    (t0 : @IsScalarTower k (MvPolynomial (Option (Fin d)) k) U
      (inferInstance : Algebra k (MvPolynomial (Option (Fin d)) k)).toSMul
      a0.toSMul b0.toSMul)
    (t1 : @IsScalarTower k (MvPolynomial (Option (Fin d)) k) U
      (inferInstance : Algebra k (MvPolynomial (Option (Fin d)) k)).toSMul
      a1.toSMul b1.toSMul)
    (e0 : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) U _ _ a0)
    (e1 : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) U _ _ a1)
    (rho : U →+* LaurentSeries k)
    (h0 : rho.comp b0.algebraMap = algebraMap k (LaurentSeries k))
    (h1 : rho.comp b1.algebraMap = algebraMap k (LaurentSeries k))
    (alpha : Fin d → k) (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (qU : Fin (n + 1) → U)
    (h : commonOpenDerivativeIdentities a0 b0 t0 e0 rho h0 alpha qPre qU) :
    commonOpenDerivativeIdentities a1 b1 t1 e1 rho h1 alpha qPre qU := by
  cases ha
  cases hb
  exact h

/-- Derivative identities on an abstract common-open algebra, with its
retained coordinate and Laurent actions scoped in the certificate. -/
structure CommonOpenDerivativeData
    {k U : Type u} [Field k] [CommRing U] [Algebra k U] {d n : ℕ}
    (psi : MvPolynomial (Option (Fin d)) k →ₐ[k] U)
    (hEtale : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) U _ _
      psi.toRingHom.toAlgebra)
    (rho : U →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k U) = algebraMap k (LaurentSeries k))
    (alpha : Fin d → k) (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (qU : Fin (n + 1) → U) : Prop where
  htransverse :
    let R := MvPolynomial (Option (Fin d)) k
    letI : Algebra R U := psi.toRingHom.toAlgebra
    letI : SMul R U := (psi.toRingHom.toAlgebra).toSMul
    letI : IsScalarTower k R U :=
      IsScalarTower.of_algebraMap_eq' psi.comp_algebraMap.symm
    letI : Algebra.FormallyEtale R U := hEtale
    letI : Algebra U (LaurentSeries k) :=
      RingHom.toAlgebra' rho (by intro x y; exact mul_comm _ _)
    letI : Algebra k (LaurentSeries k) :=
      RingHom.toAlgebra' (algebraMap k (LaurentSeries k))
        (by intro x y; exact mul_comm _ _)
    letI : Module k (LaurentSeries k) := Algebra.toModule
    letI : SMul k (LaurentSeries k) :=
      (Algebra.toModule : Module k (LaurentSeries k)).toSMul
    letI : IsScalarTower k U (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq' hground.symm
    letI : IsScalarTower U (LaurentSeries k) (LaurentSeries k) :=
      ⟨fun x y z => by
        change (algebraMap U (LaurentSeries k) x * y) * z = _
        exact mul_assoc _ _ _⟩
    ∀ j i, coordinateDerivation (k := k)
    (σ := Option (Fin d))
    (B := U) (L := LaurentSeries k) (some j)
    (qU i) = algebraMap (PowerSeries k) (LaurentSeries k)
      (tiltedTransverseDerivativeMatrix alpha qPre i j)
  hraw :
    let R := MvPolynomial (Option (Fin d)) k
    letI : Algebra R U := psi.toRingHom.toAlgebra
    letI : SMul R U := (psi.toRingHom.toAlgebra).toSMul
    letI : IsScalarTower k R U :=
      IsScalarTower.of_algebraMap_eq' psi.comp_algebraMap.symm
    letI : Algebra.FormallyEtale R U := hEtale
    letI : Algebra U (LaurentSeries k) :=
      RingHom.toAlgebra' rho (by intro x y; exact mul_comm _ _)
    letI : Algebra k (LaurentSeries k) :=
      RingHom.toAlgebra' (algebraMap k (LaurentSeries k))
        (by intro x y; exact mul_comm _ _)
    letI : Module k (LaurentSeries k) := Algebra.toModule
    letI : SMul k (LaurentSeries k) :=
      (Algebra.toModule : Module k (LaurentSeries k)).toSMul
    letI : IsScalarTower k U (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq' hground.symm
    letI : IsScalarTower U (LaurentSeries k) (LaurentSeries k) :=
      ⟨fun x y z => by
        change (algebraMap U (LaurentSeries k) x * y) * z = _
        exact mul_assoc _ _ _⟩
    ∀ i, algebraMap (PowerSeries k) (LaurentSeries k)
      (PowerSeries.derivative (R := k)
        (tiltedArc alpha (qPre i))) =
    coordinateDerivation (k := k)
      (σ := Option (Fin d))
      (B := U) (L := LaurentSeries k) none (qU i) +
      ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.C (alpha j)) *
        coordinateDerivation (k := k)
          (σ := Option (Fin d))
          (B := U) (L := LaurentSeries k) (some j)
          (qU i)

/-- Assemble a derivative certificate from equal raw scalar actions over
an abstract open algebra, preserving all dependent proof certificates. -/
theorem commonOpenDerivativeData_of_rawCertificate
    {k U : Type u} [Field k] [CommRing U] [Algebra k U] {d n : ℕ}
    (psi : MvPolynomial (Option (Fin d)) k →ₐ[k] U)
    (hEtale : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) U _ _
      psi.toRingHom.toAlgebra)
    (rho : U →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k U) = algebraMap k (LaurentSeries k))
    (alpha : Fin d → k) (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (qU : Fin (n + 1) → U)
    (h : let targetAction : Algebra (MvPolynomial (Option (Fin d)) k) U :=
        psi.toRingHom.toAlgebra
      let canonicalGround : Algebra k U := inferInstance
      ∃ (a : Algebra (MvPolynomial (Option (Fin d)) k) U) (b : Algebra k U)
        (t : @IsScalarTower k (MvPolynomial (Option (Fin d)) k) U
          (inferInstance : Algebra k (MvPolynomial (Option (Fin d)) k)).toSMul
          a.toSMul b.toSMul)
        (et : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) U _ _ a)
        (hgnd : rho.comp b.algebraMap = algebraMap k (LaurentSeries k)),
        a = targetAction ∧ b = canonicalGround ∧
        commonOpenDerivativeIdentities a b t et rho hgnd alpha qPre qU) :
    CommonOpenDerivativeData psi hEtale rho hground alpha qPre qU := by
  let R := MvPolynomial (Option (Fin d)) k
  let groundAction : Algebra k U := inferInstance
  let psiAction : Algebra R U := psi.toRingHom.toAlgebra
  have hPsiGround := psi.comp_algebraMap
  obtain ⟨a, b, tower, etale, ground, ha, hb, hRaw⟩ := h
  letI : Algebra k U := groundAction
  letI : SMul k U := groundAction.toSMul
  letI : Algebra R U := psiAction
  letI : SMul R U := psiAction.toSMul
  have targetTower : IsScalarTower k R U :=
    IsScalarTower.of_algebraMap_eq' hPsiGround.symm
  have hTarget := commonOpenDerivativeIdentities_transport a psiAction
    b groundAction ha hb tower targetTower etale hEtale rho ground hground
    alpha qPre qU hRaw
  exact @CommonOpenDerivativeData.mk k U inferInstance inferInstance groundAction
    d n psi hEtale rho hground alpha qPre qU hTarget.1 hTarget.2

/-- The point-local derivative columns retain their values after extension
along the common-open Laurent arc and its given coordinate algebra map. -/
theorem commonOpen_rawDerivativeCertificate_of_pointColumns
    {k B Q : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing B] [CommRing Q] [Algebra k Q]
    {d n : ℕ} (coeff : k →+* B) (qToB : Q →+* B)
    (fFin : @AlgHom k (MvPolynomial (Option (Fin d)) k) B _ _ _ _ coeff.toAlgebra)
    (hfinite : @Algebra.FiniteType k B _ _ coeff.toAlgebra)
    (M : Ideal B) [M.IsPrime] [M.IsMaximal] :
    letI : Algebra k B := coeff.toAlgebra
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
    (qT : Fin (n + 1) → Localization.AtPrime M)
    (qU : Fin (n + 1) → genericOpenExtraAwayB M f e g)
    (hq : ∀ i, qU i = pointLocalToCommonOpen (A := B) M f e g (qT i))
    (psi : MvPolynomial (Option (Fin d)) k →ₐ[k] genericOpenExtraAwayB M f e g)
    (hpsi : ((algebraMap (genericOpenRing M f e) (genericOpenExtraAwayB M f e g)).comp
      ((algebraMap B (genericOpenRing M f e)).comp fFin.toRingHom)).toAlgebra =
      (@RingHom.toAlgebra (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) inferInstance inferInstance psi.toRingHom))
    (hpsiEtale : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (genericOpenExtraAwayB M f e g) _ _ (@RingHom.toAlgebra (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) inferInstance inferInstance psi.toRingHom))
    (rho : genericOpenExtraAwayB M f e g →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k (genericOpenExtraAwayB M f e g)) =
      algebraMap k (LaurentSeries k))
    (hcanonical : rho = genericArcToGenericOpenExtraAwayB M f e
      (originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := B) M eM alpha) hf hunitM g hg),
    let targetAction : Algebra (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) :=
      @RingHom.toAlgebra (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) inferInstance inferInstance psi.toRingHom
    let canonicalGround : Algebra k (genericOpenExtraAwayB M f e g) := inferInstance
    ∃ (a : Algebra (MvPolynomial (Option (Fin d)) k) (genericOpenExtraAwayB M f e g))
      (b : Algebra k (genericOpenExtraAwayB M f e g))
      (t : @IsScalarTower k (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g)
        (inferInstance : Algebra k (MvPolynomial (Option (Fin d)) k)).toSMul
        a.toSMul b.toSMul)
      (et : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) _ _ a)
      (hgnd : rho.comp b.algebraMap = algebraMap k (LaurentSeries k)),
      a = targetAction ∧ b = canonicalGround ∧
      commonOpenDerivativeIdentities a b t et rho hgnd alpha
        (fun i => pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM (qT i)) qU := by
  letI : Algebra k B := coeff.toAlgebra
  letI : Algebra Q B := qToB.toAlgebra
  dsimp only
  intro f e g eM hEtM alpha hf hunitM hg qT qU hq psi hpsi hpsiEtale rho hground hcanonical
  let R := MvPolynomial (Option (Fin d)) k
  let U := genericOpenExtraAwayB M f e g
  let psiAction : Algebra R U :=
    @RingHom.toAlgebra R U inferInstance inferInstance psi.toRingHom
  have hPsiGround := psi.comp_algebraMap
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    ext c; exact (fFin.commutes c).symm)
  letI : Algebra.FiniteType k B := hfinite
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  let Cq := genericOpenRing M f e
  letI : Algebra R Cq := ((algebraMap B Cq).comp (algebraMap R B)).toAlgebra
  let rawAction : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  have hRawAction : rawAction =
      psiAction := by
    apply Algebra.algebra_ext
    intro x
    have hpoint := congrArg (fun a : Algebra R U => a.algebraMap x) hpsi
    exact hpoint
  have hcols := actual_option_columns (k := k) (d := d) (A := B)
    M f e g eM alpha hf hunitM hg n qT qU hq
  let groundAction : Algebra k U := inferInstance
  letI : Algebra R U := psiAction
  letI : SMul R U :=
    psiAction.toSMul
  letI : IsScalarTower k R U := IsScalarTower.of_algebraMap_eq' psi.comp_algebraMap.symm
  have hGroundAction : Algebra.compHom U (algebraMap k R) = groundAction := by
    apply Algebra.algebra_ext
    intro c
    exact RingHom.congr_fun psi.comp_algebraMap c
  letI : Algebra R U := rawAction
  letI : SMul R U := rawAction.toSMul
  let rawGround : Algebra k U := Algebra.compHom U (algebraMap k R)
  have hRawGround : rawGround = groundAction := by
    apply Algebra.algebra_ext
    intro c
    have hpoint := congrArg (fun a : Algebra R U =>
      a.algebraMap (algebraMap k R c)) hRawAction
    exact hpoint.trans (RingHom.congr_fun hPsiGround c)
  letI : Algebra k U := rawGround
  letI : SMul k U := rawGround.toSMul
  letI : IsScalarTower k R U := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rfl)
  letI : Algebra.FormallyEtale R U :=
    Eq.mp (congrArg (fun a : Algebra R U =>
      @Algebra.FormallyEtale R U inferInstance inferInstance a)
      hRawAction.symm) hpsiEtale
  have hgroundRaw : rho.comp (algebraMap k U) =
      algebraMap k (LaurentSeries k) := by
    apply RingHom.ext
    intro c
    have hpoint := congrArg (fun a : Algebra k U => rho (a.algebraMap c))
      hRawGround
    exact hpoint.trans (RingHom.congr_fun hground c)
  dsimp only at hcols
  rcases hcols with ⟨hposition, htransverse, hraw⟩
  have hposition' := hposition
  have htransverse' := htransverse
  have hraw' := hraw
  rw [← hcanonical] at hposition' htransverse' hraw'
  have hcolumns := actual_option_columns_to_laurent
    (k := k) (d := d) (A := B) (U := U) (M := M)
    eM (algebraMap (PowerSeries k) (LaurentSeries k)) rho hgroundRaw alpha qT qU
    hposition' htransverse' hraw'
  have hchart : (fun i => pointLocalPowerSeriesChart coeff fFin hfinite
      M eM hEtM (qT i)) = fun i =>
      localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM (qT i) := by
    funext i
    unfold pointLocalPowerSeriesChart
    dsimp only [id_eq]
    exact congrFun (AlgHom.coe_toRingHom
      (localToFinSuccPowerSeries (k := k) (B := B) (d := d) M eM)) (qT i)
  have hRawIdentities : commonOpenDerivativeIdentities rawAction rawGround
      (inferInstance : IsScalarTower k R U)
      (inferInstance : Algebra.FormallyEtale R U) rho hgroundRaw alpha
      (fun i => pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM (qT i)) qU := by
    rw [hchart]
    simpa only [commonOpenDerivativeIdentities,
      tiltedTransverseDerivativeMatrix, localTransverseDerivativeMatrix] using hcolumns.2
  exact ⟨rawAction, rawGround,
    (inferInstance : IsScalarTower k R U),
    (inferInstance : Algebra.FormallyEtale R U), hgroundRaw,
    hRawAction, hRawGround, hRawIdentities⟩

/-- The point-local derivative columns retain their values after extension
along the common-open Laurent arc and its given coordinate algebra map. -/
theorem commonOpen_derivatives_of_pointColumns
    {k B Q : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing B] [CommRing Q] [Algebra k Q]
    {d n : ℕ} (coeff : k →+* B) (qToB : Q →+* B)
    (fFin : @AlgHom k (MvPolynomial (Option (Fin d)) k) B _ _ _ _ coeff.toAlgebra)
    (hfinite : @Algebra.FiniteType k B _ _ coeff.toAlgebra)
    (M : Ideal B) [M.IsPrime] [M.IsMaximal] :
    letI : Algebra k B := coeff.toAlgebra
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
    (qT : Fin (n + 1) → Localization.AtPrime M)
    (qU : Fin (n + 1) → genericOpenExtraAwayB M f e g)
    (hq : ∀ i, qU i = pointLocalToCommonOpen (A := B) M f e g (qT i))
    (psi : MvPolynomial (Option (Fin d)) k →ₐ[k] genericOpenExtraAwayB M f e g)
    (hpsi : ((algebraMap (genericOpenRing M f e) (genericOpenExtraAwayB M f e g)).comp
      ((algebraMap B (genericOpenRing M f e)).comp fFin.toRingHom)).toAlgebra =
      (@RingHom.toAlgebra (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) inferInstance inferInstance psi.toRingHom))
    (hpsiEtale : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (genericOpenExtraAwayB M f e g) _ _ (@RingHom.toAlgebra (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) inferInstance inferInstance psi.toRingHom))
    (rho : genericOpenExtraAwayB M f e g →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k (genericOpenExtraAwayB M f e g)) =
      algebraMap k (LaurentSeries k))
    (hcanonical : rho = genericArcToGenericOpenExtraAwayB M f e
      (originalToPointLocalFinSuccArcLaurentSeries
        (k := k) (d := d) (A := B) M eM alpha) hf hunitM g hg),
    CommonOpenDerivativeData psi hpsiEtale rho hground alpha
      (fun i => pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM (qT i)) qU := by
  letI : Algebra k B := coeff.toAlgebra
  letI : Algebra Q B := qToB.toAlgebra
  dsimp only
  intro f e g eM hEtM alpha hf hunitM hg qT qU hq psi hpsi hpsiEtale rho hground hcanonical
  let R := MvPolynomial (Option (Fin d)) k
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    ext c; exact (fFin.commutes c).symm)
  letI : Algebra.FiniteType k B := hfinite
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  exact commonOpenDerivativeData_of_rawCertificate psi hpsiEtale rho hground alpha
    (fun i => pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM (qT i)) qU
    (commonOpen_rawDerivativeCertificate_of_pointColumns
      (k := k) (B := B) (Q := Q) (d := d) (n := n)
      coeff qToB fFin hfinite M f e g eM hEtM alpha hf hunitM hg
      qT qU hq psi hpsi hpsiEtale rho hground hcanonical)

/-- Transport the retained arc and prescribed columns entirely over abstract rings. -/
theorem commonOpen_derivatives_of_retainedArc
    {k B Q : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing B] [CommRing Q] [Algebra k Q]
    {d n : ℕ} (coeff : k →+* B) (qToB : Q →+* B)
    (fFin : @AlgHom k (MvPolynomial (Option (Fin d)) k) B _ _ _ _ coeff.toAlgebra)
    (hfinite : @Algebra.FiniteType k B _ _ coeff.toAlgebra)
    (M : Ideal B) [M.IsPrime] [M.IsMaximal] :
    letI : Algebra k B := coeff.toAlgebra
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
    (rhoA : B →+* LaurentSeries k)
    (hf : IsUnit (rhoA (algebraMap Q B f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (rhoA b))
    (hg : IsUnit (rhoA (algebraMap Q B g)))
    (hsource : rhoA = originalToPointLocalFinSuccArcLaurentSeries
      (k := k) (d := d) (A := B) M eM alpha)
    (qT : Fin (n + 1) → Localization.AtPrime M)
    (qU : Fin (n + 1) → genericOpenExtraAwayB M f e g)
    (hq : ∀ i, qU i = pointLocalToCommonOpen (A := B) M f e g (qT i))
    (psi : MvPolynomial (Option (Fin d)) k →ₐ[k] genericOpenExtraAwayB M f e g)
    (hpsi : ((algebraMap (genericOpenRing M f e) (genericOpenExtraAwayB M f e g)).comp
      ((algebraMap B (genericOpenRing M f e)).comp fFin.toRingHom)).toAlgebra =
      (@RingHom.toAlgebra (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) inferInstance inferInstance psi.toRingHom))
    (hpsiEtale : @Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k)
      (genericOpenExtraAwayB M f e g) _ _ (@RingHom.toAlgebra (MvPolynomial (Option (Fin d)) k)
        (genericOpenExtraAwayB M f e g) inferInstance inferInstance psi.toRingHom))
    (rho : genericOpenExtraAwayB M f e g →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k (genericOpenExtraAwayB M f e g)) =
      algebraMap k (LaurentSeries k))
    (hcanonical : rho = genericArcToGenericOpenExtraAwayB M f e
      rhoA hf hunitM g hg)
    (qPre : Fin (n + 1) → MvPowerSeries (Fin (d + 1)) k)
    (hqPre : qPre = fun i => pointLocalPowerSeriesChart coeff fFin hfinite M eM hEtM (qT i)),
    CommonOpenDerivativeData psi hpsiEtale rho hground alpha
      qPre qU := by
  letI : Algebra k B := coeff.toAlgebra
  letI : Algebra Q B := qToB.toAlgebra
  dsimp only
  intro f e g eM hEtM alpha rhoA hf hunitM hg hsource qT qU hq psi hpsi hpsiEtale rho hground hcanonical qPre hqPre
  let R := MvPolynomial (Option (Fin d)) k
  letI : Algebra R B := fFin.toRingHom.toAlgebra
  letI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    ext c; exact (fFin.commutes c).symm)
  letI : Algebra.FiniteType k B := hfinite
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp k R B
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  have hf' := hf
  rw [hsource] at hf'
  have hunitM' := hunitM
  rw [hsource] at hunitM'
  have hg' := hg
  rw [hsource] at hg'
  have hcanonical' := genericOpenArc_eq_of_source_eq
    M f e g rhoA _ rho hf hunitM hg hsource hcanonical
  rw [hqPre]
  exact commonOpen_derivatives_of_pointColumns coeff qToB fFin hfinite
    M f e g eM hEtM alpha hf' hunitM' hg' qT qU hq
    psi hpsi hpsiEtale rho hground hcanonical'

end Stafford38.Geometry.SameWitness

end
