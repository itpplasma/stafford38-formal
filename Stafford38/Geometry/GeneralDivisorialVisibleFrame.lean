import Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
import Stafford38.Geometry.CompletedDVRPowerSeriesEquiv
import Stafford38.Geometry.GeneralDivisorialVisibleFrameData

set_option autoImplicit false

/-!
# Divisorial visible frames for arbitrary prime affine components

An invertible, transcendental coordinate on a prime affine component gives
a normalized visible divisor frame. This removes the canonical Weyl-support
hypotheses from the boundary producer. Identification of the resulting Laurent
direction with the smooth projective conormal closure is performed downstream
in the general asymptotic-conormal construction.
-/

namespace Stafford38.Geometry.GeneralDivisorialVisibleFrame

open IsLocalRing Polynomial
open Stafford38
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.ComponentProjectiveOrder
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
open Stafford38.Geometry.ExactVisibleDivisorFrameInterface
open Stafford38.Geometry.KaehlerDVRVisibility
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.DivisorTangentLattice

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

universe u

set_option maxHeartbeats 4000000 in

/-- The general divisorial producer with its actual Lane-C residue
algebraicity retained.  The algebraicity is for the same normalized column
and the same visible frame, under the ground algebra structure induced by the
retained coefficient map. -/
theorem generalDivisorialVisibleFrameWithResidueAlgebraicity
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k
      (componentCoordinate P ⟨0, hm⟩)) :
    Nonempty (GeneralDivisorialVisibleFrameWitness hm P) := by
  let i : Fin m := ⟨0, hm⟩
  let K := ComponentFractionField P
  obtain ⟨E, V, hEV, hVdvr, hxV, htransE, hxm, hEfin, hkaehler, halgAll⟩ :=
    Stafford38.Geometry.LaneC.divisorialVisibleFrameExistence
      k K m (componentCoordinate P) i
        (componentCoordinate_adjoin_eq_top P) htrans
  letI : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
  letI : Algebra E V.toSubring :=
    (Stafford38.Geometry.LaneC.coeffHom E V hEV).toAlgebra
  letI : Algebra k V.toSubring :=
    (Stafford38.Geometry.LaneC.groundHom E V hEV).toAlgebra
  letI : Algebra V.toSubring K := V.toSubring.subtype.toAlgebra
  letI : IsScalarTower k V.toSubring K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k K c = (algebraMap k E c : K)
      exact IsScalarTower.algebraMap_apply k E K c
  letI : Module.Finite V.toSubring (Ω[V.toSubring⁄k]) := hkaehler
  let W : Data k K (componentCoordinate P i) :=
    retainedDataOfValuation E V hEV hVdvr (componentCoordinate P i) hxV
      htransE hxm hEfin
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  letI : IsScalarTower W.coefficientField
      (CoordinateZeroLocalRing W.coefficientField) K := W.coefficientTower
  obtain ⟨chart, qraw, scale, hscale, hchartRaw, hqraw⟩ :=
    exists_normalized_projective_lift V (componentProjectivePoint P)
      ⟨0, by
        simpa only [componentProjectivePoint_eq_finCases, Fin.cases_zero] using
          (one_ne_zero : (1 : ComponentFractionField P) ≠ 0)⟩
  let q : Fin (m + 1) → V.toSubring := fun a =>
    ⟨qraw a, (qraw a).property⟩
  have hchart : q chart = 1 := by
    apply Subtype.ext
    exact congrArg Subtype.val hchartRaw
  have hq : ∀ a, (q a : K) = scale * componentProjectivePoint P a := by
    intro a
    exact hqraw a
  have hq0 : q 0 ≠ 0 := by
    intro hzero
    apply hscale
    have hz : ((q 0 : V.toSubring) : K) = 0 :=
      congrArg (fun z : V.toSubring => (z : K)) hzero
    have h := hq 0
    rw [hz] at h
    simpa only [componentProjectivePoint_eq_finCases, Fin.cases_zero, mul_one]
      using h.symm
  let xV : V.toSubring := ⟨componentCoordinate P i, hxV⟩
  have hratioV : q (Fin.succ i) = q 0 * xV := by
    apply Subtype.ext
    change (q (Fin.succ i) : K) = (q 0 : K) * componentCoordinate P i
    rw [hq, hq]
    simp only [componentProjectivePoint_eq_finCases, Fin.cases_zero,
      Fin.cases_succ, mul_one]
  let coeff : k →+* V :=
    (relativeCoefficientMap W.coefficientField W.place).comp
      (algebraMap k W.coefficientField)
  have hcoeff : W.place.valuation.toSubring.subtype.comp coeff =
      algebraMap k K := by
    ext c
    change ((relativeCoefficientMap W.coefficientField W.place
      (algebraMap k W.coefficientField c) : V) : K) = algebraMap k K c
    calc
      ((relativeCoefficientMap W.coefficientField W.place
          (algebraMap k W.coefficientField c) : V) : K) =
          algebraMap W.coefficientField K
            (algebraMap k W.coefficientField c) :=
        DFunLike.congr_fun
          (relativeCoefficientMap_commutes W.coefficientField W.place)
          (algebraMap k W.coefficientField c)
      _ = algebraMap k K c :=
        IsScalarTower.algebraMap_apply k W.coefficientField K c
  have hLaneCoeff : W.place.valuation.toSubring.subtype.comp
      (Stafford38.Geometry.LaneC.groundHom E V hEV) = algebraMap k K := by
    ext c
    change ((algebraMap k E c : E) : K) = algebraMap k K c
    exact IsScalarTower.algebraMap_apply k E K c
  have hCoeffEq : coeff = Stafford38.Geometry.LaneC.groundHom E V hEV := by
    apply RingHom.ext
    intro c
    apply Subtype.ext
    change ((coeff c : V) : K) =
      ((Stafford38.Geometry.LaneC.groundHom E V hEV c : V) : K)
    calc
      ((coeff c : V) : K) = algebraMap k K c := by
        have hc := DFunLike.congr_fun hcoeff c
        change ((coeff c : V) : K) = algebraMap k K c at hc
        exact hc
      _ = ((Stafford38.Geometry.LaneC.groundHom E V hEV c : V) : K) := by
        have hc := DFunLike.congr_fun hLaneCoeff c
        change ((Stafford38.Geometry.LaneC.groundHom E V hEV c : V) : K) =
          algebraMap k K c at hc
        exact hc.symm
  have hq0nonunit : ¬ IsUnit (q 0) := by
    obtain ⟨g, hg⟩ := hunit
    let F := K
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F :=
      W.ambientAlgebra
    letI : IsScalarTower W.coefficientField
        (CoordinateZeroLocalRing W.coefficientField) F := W.coefficientTower
    let phi : MvPolynomial (Fin m) k →+* F :=
      (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal) F).comp
        (Ideal.Quotient.mk P.asIdeal)
    have hphiC : phi.comp MvPolynomial.C = algebraMap k F := by
      ext c
      exact IsScalarTower.algebraMap_apply k
        (MvPolynomial (Fin m) k ⧸ P.asIdeal) F c
    have hphiX : ∀ j, phi (MvPolynomial.X j) = componentCoordinate P j := by
      intro j
      rfl
    have hpoly : phi g = MvPolynomial.eval₂ (algebraMap k F)
        (fun j ↦ componentCoordinate P j) g := by
      rw [MvPolynomial.map_mvPolynomial_eq_eval₂ phi g]
      change MvPolynomial.eval₂Hom (phi.comp MvPolynomial.C)
          (fun j ↦ phi (MvPolynomial.X j)) g =
        MvPolynomial.eval₂Hom (algebraMap k F)
          (fun j ↦ componentCoordinate P j) g
      apply MvPolynomial.eval₂Hom_congr hphiC
      · funext j
        exact hphiX j
      · rfl
    have hinverse : componentCoordinate P i *
        MvPolynomial.eval₂ (algebraMap k F)
          (fun j ↦ componentCoordinate P j) g = 1 := by
      have hzero : phi (MvPolynomial.X i * g - 1) = 0 := by
        have hmk : Ideal.Quotient.mk P.asIdeal
            (MvPolynomial.X i * g - 1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hg
        simpa [phi] using (congrArg
          (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal) F) hmk)
      rw [map_sub, map_mul, map_one, sub_eq_zero, hphiX, hpoly] at hzero
      exact hzero
    exact normalized_denominator_nonunit_of_polynomial_inverse
      (V := W.place.valuation) (coeff := coeff) hcoeff
      (x := fun j ↦ componentCoordinate P j)
      (qzero := q 0) (q := fun j ↦ q (Fin.succ j)) (scale := scale)
      (i := i) (parameter := W.place.parameter) (g := g)
      (by simpa only [componentProjectivePoint_eq_finCases, Fin.cases_zero, mul_one] using hq 0)
      (by intro j; simpa only [componentProjectivePoint_eq_finCases, Fin.cases_succ]
        using hq (Fin.succ j))
      W.parameter_eq_coordinate W.place.parameter_nonunit hinverse
  let A_lane : Algebra k (ResidueField V) :=
    ((residue V).comp (Stafford38.Geometry.LaneC.groundHom E V hEV)).toAlgebra
  let A_retained : Algebra k (ResidueField V) :=
    retainedResidueGroundAlgebra P i W
  have hresMapEq :
      (residue V).comp (Stafford38.Geometry.LaneC.groundHom E V hEV) =
        (residue V).comp (retainedComponentCoefficientMap P i W) := by
    change (residue V).comp (Stafford38.Geometry.LaneC.groundHom E V hEV) =
      (residue V).comp coeff
    rw [← hCoeffEq]
  have hresAlgEq : A_lane = A_retained := by
    change ((residue V).comp
        (Stafford38.Geometry.LaneC.groundHom E V hEV)).toAlgebra =
      ((residue V).comp (retainedComponentCoefficientMap P i W)).toAlgebra
    exact congrArg RingHom.toAlgebra hresMapEq
  have halgLane :
      letI : Algebra k (ResidueField V) := A_lane
      Algebra.IsAlgebraic
        (IntermediateField.adjoin k
        (Set.range fun j : Fin m ↦ residue V (q (Fin.succ j))) :
        IntermediateField k (ResidueField V))
        (ResidueField V) := by
    letI : Algebra k (ResidueField V) := A_lane
    have hqFinCases : ∀ a,
        (q a : K) = scale * Fin.cases 1
          (fun i ↦ componentCoordinate P i) a := by
      intro a
      have hpoint : componentProjectivePoint P a =
          Fin.cases 1 (fun i ↦ componentCoordinate P i) a :=
        congrFun (componentProjectivePoint_eq_finCases P) a
      calc
        (q a : K) = scale * componentProjectivePoint P a := hq a
        _ = scale * Fin.cases 1 (fun i ↦ componentCoordinate P i) a := by
          rw [hpoint]
    exact halgAll scale q hqFinCases
      ⟨chart, hchart⟩ hq0nonunit
  have halg := algebraic_adjoin_transfer_of_algebra_eq
    A_lane A_retained hresAlgEq
    (Set.range fun j : Fin m ↦ residue V (q (Fin.succ j))) halgLane
  have hchart_ne : chart ≠ 0 := by
    intro hzero
    apply hq0nonunit
    rw [← hzero, hchart]
    exact isUnit_one
  obtain ⟨j₀, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hchart_ne
  let t := Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer
    V.toSubring
  have ht : Irreducible t :=
    Stafford38.Geometry.CompletedDVRPowerSeries.chosenUniformizer_irreducible
      V.toSubring
  have hq0max : q 0 ∈ maximalIdeal V.toSubring := by
    apply (IsLocalRing.mem_maximalIdeal (q 0)).2
    exact mem_nonunits_iff.mpr hq0nonunit
  have hxV_ne : xV ≠ 0 := by
    intro hx0
    apply htransE
    have hx0K : componentCoordinate P i = 0 := congrArg Subtype.val hx0
    exact hx0K ▸ isAlgebraic_zero
  obtain ⟨a, e, b, u₀, ur, u₁, ha, he, hb, hab,
      hq0factor, hparameterFactor, hu₁, hq1factor⟩ :=
    exists_uniformizer_strict_orderGap t ht (q 0) xV
      (q (Fin.succ i)) hq0 hxV_ne hq0max hxm hratioV
  let Q : Fin m → V.toSubring := fun j => q (Fin.succ j)
  have hQj₀ : Q j₀ = 1 := hchart
  have hq0frame : q 0 = t ^ a * (u₀ : V.toSubring) := by
    simpa [mul_comm] using hq0factor
  have hq1frame : q (Fin.succ i) = t ^ (a + e) * (u₁ : V.toSubring) := by
    simpa [hb, mul_comm] using hq1factor
  obtain ⟨D, hD0, hD1, hDt, hDu, hDw, hDQ, hDa, hDe, hDj, hDW⟩ :=
    exists_visibleDivisorFrame_of_kaehler_image
      (k := k) (F := K) (q 0) (q (Fin.succ i)) t
        (u₀ : V.toSubring) (u₁ : V.toSubring) Q a e j₀
        ht.maximalIdeal_eq ht.ne_zero u₀.isUnit
        (Nat.one_le_iff_ne_zero.mpr ha.ne')
        (Nat.one_le_iff_ne_zero.mpr he.ne') hq0frame hq1frame hQj₀ halgLane
  have hretMap :
      @algebraMap k (ResidueField V) _ _ A_retained =
        (residue V).comp (retainedComponentCoefficientMap P i W) := by
    exact RingHom.algebraMap_toAlgebra _
  let C : GeneralDivisorialVisibleFrameColumn hm P := {
    W := W
    chart := Fin.succ j₀
    q := q
    scale := scale
    scale_ne := hscale
    chart_one := hchart
    q0_ne := hq0
    q_commonScale := hq
    q_parameter := by
      apply Subtype.ext
      have hv := congrArg Subtype.val hratioV
      change (q (Fin.succ ⟨0, hm⟩) : K) =
        (q 0 : K) * componentCoordinate P ⟨0, hm⟩ at hv
      calc
        (q (Fin.succ ⟨0, hm⟩) : K) =
            (q 0 : K) * componentCoordinate P ⟨0, hm⟩ := hv
        _ = (q 0 : K) * (W.place.parameter : K) := by
          rw [W.parameter_eq_coordinate]
    groundCoeff := Stafford38.Geometry.LaneC.groundHom E V hEV
    groundCoeff_commutes := hLaneCoeff
    groundCoeff_eq_retained := hCoeffEq.symm
    groundTower := by
      let V' := W.place.valuation.toSubring
      letI : Algebra k V' :=
        (Stafford38.Geometry.LaneC.groundHom E V hEV).toAlgebra
      letI : Algebra V' (ComponentFractionField P) := V'.subtype.toAlgebra
      exact IsScalarTower.of_algebraMap_eq fun c => by
        exact (DFunLike.congr_fun hLaneCoeff c).symm
  }
  let core : GeneralDivisorialVisibleFrameCore hm P C := {
    D := D
    D_Q0 := hD0
    D_Q1 := hD1
    D_Q := fun j => by rw [hDQ]
    D_maximalIdeal := by
      rw [hDt]
      exact Stafford38.Geometry.CompletedDVRPowerSeries.maximalIdeal_eq_span_chosenUniformizer
        V.toSubring
    D_uniformizer := hDt
    D_w_unit := by
      rw [hDw]
      exact u₁.isUnit
  }
  let S : GeneralDivisorialVisibleFrameSourceImage hm P C core :=
    ⟨hDW⟩
  let F : GeneralDivisorialVisibleFrameDifferential hm P C :=
    ⟨core, S⟩
  exact ⟨{
    column := C
    differential := F
    retainedGroundMap := RingHom.algebraMap_toAlgebra _
    halg := halg
  }⟩

/-- The original interface is the projection of the richer Lane-C witness. -/
theorem generalDivisorialVisibleFrameExistence
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k
      (componentCoordinate P ⟨0, hm⟩)) :
    HasNormalizedCompatibleVisibleFrame P hm := by
  obtain ⟨w⟩ :=
    generalDivisorialVisibleFrameWithResidueAlgebraicity hm P hunit htrans
  let C := w.column
  let F := w.differential.core
  letI : Algebra (CoordinateZeroLocalRing C.W.coefficientField)
      (ComponentFractionField P) := C.W.ambientAlgebra
  let V := C.W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := C.W.place.isDiscrete
  exact ⟨C.W, C.chart, C.q, C.scale, C.scale_ne, C.chart_one, C.q0_ne,
    C.q_commonScale, C.q_parameter,
    ⟨F.D, F.D_Q0, F.D_Q1, F.D_Q⟩⟩

#print axioms generalDivisorialVisibleFrameWithResidueAlgebraicity

#print axioms generalDivisorialVisibleFrameExistence

end

end Stafford38.Geometry.GeneralDivisorialVisibleFrame
