module

public import Stafford38.Paper.Section5.Place
public import Stafford38.Paper.Section5.ResidueBasis
public import Stafford38.Paper.Section5.TangentCone
public import Stafford38.Paper.Section5.GenericTangentRank
public import Stafford38.Geometry.AlternativeAsymptoticConormal
public import Stafford38.Geometry.ProjectiveConormalDirections
public import Stafford38.Geometry.PaperActualWitnessConormalData
public import Stafford38.Geometry.PaperResidueDerivationFrame
public import Stafford38.Geometry.ExactDivisorialVisibleFrameExistence

@[expose] public section

/-!
# Section 5.2 of the paper: Theorem 5.7 and its lemmas

The paper's lemmas are stated and proved in
`Stafford38.Paper.Section5.Place` (Lemmas 5.9, 5.10),
`Stafford38.Paper.Section5.ResidueBasis` (Lemma 5.11),
`Stafford38.Paper.Section5.TangentCone` and
`Stafford38.Paper.Section5.GenericTangentRank` (Lemmas 5.12, 5.13).

Theorem 5.7 is proved along the paper's route by
`Stafford38.Geometry.AlternativeAsymptoticConormal`: the algebraic case, the
discrete valuation ring at infinity, the Laurent generic point `y`, the
matrix `M(t)` with a unit minor and the lifted row `ℓ(t)` with `ℓ(0) = u`.  The
theorems `witness_lemma_*` below show that the discrete valuation ring and the
Laurent column `q(t)` used in that proof satisfy Lemmas 5.11–5.13 and both parts
of Lemma 5.12(a).  The terminal theorem in `GeneralAsymptoticConormal` proves
the same statement by a second, chart-based route and is kept unchanged.
-/

namespace Stafford38.Paper.Section5

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ActualWitnessConormalAssembly
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.PaperRetainedChartAssembly
open Stafford38.Geometry.PaperResidueDerivationFrame
open Stafford38.Geometry.PaperSameWitnessComponentFieldRank
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.SmoothConormalFibreVanishing

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000

universe u

/-- **Theorem 5.7(i).** If `Y = V(𝔭)` is nonempty, irreducible and avoids
`H = {x_1 = 0}`, every polynomial vanishing on the conormal cone `N(Y)` over the
smooth locus vanishes at `(1, 0, …, 0)`.  Proved along the paper's route. -/
theorem theorem_5_7_i
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) :=
  Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure
    hm I havoid

/-- **Theorem 5.7(ii).** `[dx_1] ∈ Dir(Y)`. -/
theorem theorem_5_7_ii
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    Projectivization.mk k
        (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0)
        (by intro h; have := congrFun h ⟨0, hm⟩; simp at this) ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I.asIdeal)) :=
  mk_mem_projectiveHomogeneousClosure_of_fibre_zeroLocus I.asIdeal _ _
    (theorem_5_7_i hm I havoid)

/-- **Lemma 5.11 for the valuation ring of the formal proof.**  The residues
`res q_i` of its normalized column satisfy `res q_0 = res q_1 = 0`,
`res q_j = 1`, and some `res q_i` with `i ∉ {0, 1, j}` have differentials
forming a basis of `Ω_{κ/K}`. -/
theorem witness_lemma_5_11
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal) :
    let C := w.column
    let W := C.W
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    residue V (C.q 0) = 0 ∧ residue V (C.q (Fin.succ ⟨0, hm⟩)) = 0 ∧
      residue V (C.q C.chart) = 1 ∧
      ∃ (d' : ℕ) (rows : Fin d' → Fin (m + 1)),
        Function.Injective rows ∧
        (∀ l, rows l ≠ 0 ∧ rows l ≠ Fin.succ ⟨0, hm⟩ ∧ rows l ≠ C.chart) ∧
        LinearIndependent κ
          (fun l ↦ KaehlerDifferential.D k κ (residue V (C.q (rows l)))) ∧
        Submodule.span κ
          (Set.range fun l ↦ KaehlerDifferential.D k κ (residue V (C.q (rows l)))) = ⊤ ∧
        d' = Module.finrank κ (Ω[κ⁄k]) := by
  classical
  let C := w.column
  let W := C.W
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
    (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  obtain ⟨a, b, u₀, u₁, ha, hab, hq0, -, hq1⟩ := order_gap_of_actual_witness hm P w hunit
  have hres := constantCoeff_retainedToCompleted_eq_residue (k := k) W
  have hr0 : residue V (C.q 0) = 0 := by
    rw [← hres, hq0]
    simp [ha.ne']
  have hr1 : residue V (C.q (Fin.succ ⟨0, hm⟩)) = 0 := by
    rw [← hres, hq1]
    simp [(ha.trans hab).ne']
  have hrj : residue V (C.q C.chart) = 1 := by
    rw [C.chart_one, map_one]
  have halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range fun a ↦ residue V (C.q a)) :
        IntermediateField k κ) κ := by
    have h := w.halg
    have hle : IntermediateField.adjoin k
          (Set.range fun j : Fin m ↦ residue V (C.q (Fin.succ j))) ≤
        IntermediateField.adjoin k (Set.range fun a ↦ residue V (C.q a)) :=
      IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨j, rfl⟩; exact ⟨_, rfl⟩)
    exact ⟨fun z ↦ IsAlgebraic.tower_top_of_subalgebra_le
      (IntermediateField.toSubalgebra_le_toSubalgebra.mpr hle) (h.isAlgebraic z)⟩
  exact ⟨hr0, hr1, hrj,
    lemma_5_11 hm (fun a ↦ residue V (C.q a)) C.chart hr0 hr1 hrj halg⟩

/-- **Lemmas 5.12(a), 5.12(b) and 5.13 at the Laurent generic point of the
formal proof.**  For the column `q(t)` of `witness_lemma_5_11`, with
`y = q/q_0 ∈ κ((t))^n`: `dim Θ_y = dim_F Ω_{F/K}`, this equals
`trdeg_K F = m`, and `m ≤ d' + 1`; `dim 𝒞 = dim Θ_y + 1`; `δq ∈ 𝒞` for every
`K`-derivation `δ` of `κ((t))` and `q ∈ 𝒞`; and every row annihilating `𝒞` has
conormal affine part. -/
theorem witness_lemma_5_12_5_13
    {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P) :
    let C := w.column
    let W := C.W
    let F := ComponentFractionField P
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    let E := LaurentSeries κ
    letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
    letI : SMul k E := (inferInstance : Algebra k E).toSMul
    letI : Module k E := (inferInstance : Algebra k E).toModule
    let q : Fin (m + 1) → E :=
      laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)
    (Module.finrank E (tangentSpaceAt q P.asIdeal) = Module.finrank F (Ω[F⁄k]) ∧
      (Module.finrank F (Ω[F⁄k]) : Cardinal) = Algebra.trdeg k F ∧
      Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1 ∧
      Module.finrank E (tangentCone q P.asIdeal) =
        Module.finrank E (tangentSpaceAt q P.asIdeal) + 1) ∧
    ((∀ δ : Derivation k E E, (fun a ↦ δ (q a)) ∈ tangentCone q P.asIdeal) ∧
      q ∈ tangentCone q P.asIdeal) ∧
    (∀ ell : Fin (m + 1) → E, (∀ v ∈ tangentCone q P.asIdeal, ∑ a, ell a * v a = 0) →
      coordinateCovector (fun i : Fin m ↦ ell i.succ) ∈
        equationCovectorSpan (dehomogenizedPoint q)
          (P.asIdeal.map (MvPolynomial.map (algebraMap k E)))) := by
  classical
  let C := w.column
  let W := C.W
  let F := ComponentFractionField P
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  let E := LaurentSeries κ
  letI : Algebra k E := (groundLaurentMap (k := k) (K := κ)).toAlgebra
  letI : SMul k E := (inferInstance : Algebra k E).toSMul
  letI : Module k E := (inferInstance : Algebra k E).toModule
  let q : Fin (m + 1) → E :=
    laurentColumn fun a ↦ retainedToCompletedPowerSeries W (C.q a)
  letI : IsLocalRing V := W.place.isDiscrete.toIsLocalRing
  letI : CharZero κ :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k κ)
  let i₀ : Fin m := ⟨0, hm⟩
  let ell : F →+* E := retainedLaurentLift P i₀ W
  have hground : ell.comp (algebraMap k F) = groundLaurentMap (k := k) (K := κ) :=
    retainedLaurentLift_comp_algebraMap P i₀ W
  have hpoint : ell ∘ componentCoordinate P = dehomogenizedPoint q :=
    retainedLaurentLift_componentCoordinate P i₀ W C.q C.scale C.q_commonScale C.q0_ne
  have hq0 : q 0 ≠ 0 := by
    intro h
    apply C.q0_ne
    have h1 : HahnSeries.ofPowerSeries ℤ κ (retainedToCompletedPowerSeries W (C.q 0)) = 0 := by
      simpa [q, laurentColumn] using h
    have h' : retainedToCompletedPowerSeries W (C.q 0) = 0 :=
      HahnSeries.ofPowerSeries_injective (h1.trans (map_zero _).symm)
    exact (retainedToCompletedPowerSeries_injective W) (by rw [h', map_zero])
  have hbase : ∀ f ∈ P.asIdeal,
      MvPolynomial.eval₂ (algebraMap k E) (dehomogenizedPoint q) f = 0 :=
    fun f hf ↦ component_equations_vanish_after_point_transport P ell hground _ hpoint hf
  have hcone := lemma_5_12_a_cone q hq0 P.asIdeal
  have hb := lemma_5_12_b q hq0 P.asIdeal hbase
  have h13 := fun ell hell ↦ lemma_5_13 q hq0 P.asIdeal ell hell
  -- Lemma 5.12(a): `dim Θ_y = dim_F Ω_{F/K} = trdeg_K F ≤ d' + 1`.
  letI : Algebra F E := ell.toAlgebra
  letI : SMul k F := (inferInstance : Algebra k F).toSMul
  letI : Module k F := (inferInstance : Algebra k F).toModule
  letI : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun c ↦ by
    have h := congrArg (fun f : k →+* E ↦ f c) hground
    change (groundLaurentMap (k := k) (K := κ)) c = ell (algebraMap k F c)
    exact h.symm
  have hgenPoint : IntermediateField.adjoin k
      (Set.range (Stafford38.Geometry.GenericPointKaehlerConormal.genericPoint P.asIdeal F)) =
        ⊤ := by
    have hcoordinates :
        Stafford38.Geometry.GenericPointKaehlerConormal.genericPoint P.asIdeal F =
          componentCoordinate P := by
      funext j
      rfl
    rw [hcoordinates]
    exact componentCoordinate_adjoin_eq_top P
  have hchartPoint : (fun j : Fin m ↦ algebraMap F E
      (Stafford38.Geometry.GenericPointKaehlerConormal.genericPoint P.asIdeal F j)) =
        dehomogenizedPoint q := by
    funext j
    exact congrFun hpoint j
  have hdim := generic_tangent_finrank_eq_component_kaehler_finrank (E := E)
    (I := P.asIdeal) hgenPoint
  rw [hchartPoint] at hdim
  have htr := (component_kaehler_finrank_eq_trdeg (k := k) (componentCoordinate P)
    (componentCoordinate_adjoin_eq_top P)).1
  have hfieldRank : Module.finrank F (Ω[F⁄k]) ≤ Module.finrank κ (Ω[κ⁄k]) + 1 :=
    component_field_rank_of_witness hm P w
  exact ⟨⟨hdim, htr, hfieldRank, hcone⟩, hb, h13⟩

#print axioms theorem_5_7_i
#print axioms theorem_5_7_ii
#print axioms witness_lemma_5_11
#print axioms witness_lemma_5_12_5_13

end

end Stafford38.Paper.Section5
