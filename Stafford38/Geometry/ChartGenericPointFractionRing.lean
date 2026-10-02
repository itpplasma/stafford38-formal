import Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
import Stafford38.Geometry.RelativeDivisorialTower
import Stafford38.Geometry.RetainedChartQuotientEmbedding
import Stafford38.Geometry.ComponentProjectiveChartKernel
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000

namespace Stafford38.Geometry.ChartGenericPointFractionRing

open IsLocalRing
open scoped IntermediateField.algebraAdjoinAdjoin
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ComponentProjectiveChartFactorization
open Stafford38.Geometry.ProjectiveChartCoordinates
open Stafford38.Geometry.RetainedChartQuotientEmbedding

universe u
variable {k : Type u} [Field k] {m : ℕ}

/-- The affine coordinate algebra of a chosen projective chart, embedded in
the component function field. This is the shared owner for every selected or
arbitrary chart presentation of the same range of chart coordinates. -/
abbrev chartGenericPointSubalgebra
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) :
    Subalgebra k (ComponentFractionField P) :=
  Algebra.adjoin k (Set.range (chartGenericPoint P chart e))

/-- Ratios in any nonzero projective chart generate the same component function
field as the original affine coordinate family. -/
theorem chartGenericPoint_adjoin_eq_top
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    IntermediateField.adjoin k (Set.range (chartGenericPoint P chart e)) = ⊤ := by
  let L := IntermediateField.adjoin k (Set.range (chartGenericPoint P chart e))
  apply top_unique
  rw [← Stafford38.Geometry.ExactDivisorialVisibleFrameExistence.componentCoordinate_adjoin_eq_top P]
  apply IntermediateField.adjoin_le_iff.2
  rintro x ⟨j, rfl⟩
  change componentCoordinate P j ∈ L
  rcases Fin.eq_zero_or_eq_succ chart with hzero | ⟨c, hchartEq⟩
  · subst chart
    let ij := e.symm ⟨j.succ, Fin.succ_ne_zero j⟩
    have hij : (e ij).1 = j.succ := by
      have := Equiv.apply_symm_apply e ⟨j.succ, Fin.succ_ne_zero j⟩
      exact congrArg Subtype.val this
    have heval : chartGenericPoint P 0 e ij = componentCoordinate P j := by
      simp [chartGenericPoint, componentProjectivePoint, ij, hij]
    rw [← heval]
    exact IntermediateField.subset_adjoin k _ (Set.mem_range_self ij)
  · subst chart
    let i0 := e.symm ⟨0, (Fin.succ_ne_zero c).symm⟩
    have hi0 : (e i0).1 = 0 := by
      have := Equiv.apply_symm_apply e ⟨0, (Fin.succ_ne_zero c).symm⟩
      exact congrArg Subtype.val this
    have hr0 : chartGenericPoint P c.succ e i0 =
        (componentCoordinate P c)⁻¹ := by
      simp [chartGenericPoint, componentProjectivePoint, hi0]
    have hr0mem : chartGenericPoint P c.succ e i0 ∈ L :=
      IntermediateField.subset_adjoin k _ (Set.mem_range_self i0)
    have hxcnz : componentCoordinate P c ≠ 0 := by
      simpa [componentProjectivePoint] using hchart
    by_cases hjc : j = c
    · subst j
      have hxc : componentCoordinate P c =
          (chartGenericPoint P c.succ e i0)⁻¹ := by
        rw [hr0]
        simp [hxcnz]
      rw [hxc]
      exact L.inv_mem hr0mem
    · have hne : j.succ ≠ c.succ := by simpa [Fin.succ_inj] using hjc
      let ij := e.symm ⟨j.succ, hne⟩
      have hij : (e ij).1 = j.succ := by
        have := Equiv.apply_symm_apply e ⟨j.succ, hne⟩
        exact congrArg Subtype.val this
      have hrj : chartGenericPoint P c.succ e ij =
          componentCoordinate P j / componentCoordinate P c := by
        simp [chartGenericPoint, componentProjectivePoint, hij]
      have hrjmem : chartGenericPoint P c.succ e ij ∈ L :=
        IntermediateField.subset_adjoin k _ (Set.mem_range_self ij)
      have hxratio : componentCoordinate P j =
          chartGenericPoint P c.succ e ij / chartGenericPoint P c.succ e i0 := by
        rw [hrj, hr0]
        field_simp [hxcnz]
      rw [hxratio]
      exact L.div_mem hrjmem hr0mem

/-- Reindexing the normalized projective-column residues from the complement
of an arbitrary chart to the fixed tail `Fin.succ` changes only the residue
of coordinate zero (which is assumed zero) and the chart coordinate (which
is one). Thus both finite families generate the same residue subfield. -/
theorem chartCoordinateResidue_adjoin_eq_tail
    {V : Type*} [CommRing V] [IsLocalRing V]
    [Algebra k V] [Algebra k (ResidueField V)]
    [IsScalarTower k V (ResidueField V)]
    (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1)
    (hq0res : residue V (q 0) = 0) :
    IntermediateField.adjoin k
        (Set.range fun i : Fin m ↦ residue V (q (e i).1)) =
      IntermediateField.adjoin k
        (Set.range fun j : Fin m ↦ residue V (q (Fin.succ j))) := by
  let Lchart : IntermediateField k (ResidueField V) :=
    IntermediateField.adjoin k
      (Set.range fun i : Fin m ↦ residue V (q (e i).1))
  let Ltail : IntermediateField k (ResidueField V) :=
    IntermediateField.adjoin k
      (Set.range fun j : Fin m ↦ residue V (q (Fin.succ j)))
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨i, rfl⟩
    change residue V (q (e i).1) ∈ Ltail
    rcases Fin.eq_zero_or_eq_succ (e i).1 with hzero | ⟨j, hj⟩
    · rw [hzero, hq0res]
      exact Ltail.zero_mem
    · rw [hj]
      exact IntermediateField.subset_adjoin k _ ⟨j, rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨j, rfl⟩
    change residue V (q (Fin.succ j)) ∈ Lchart
    by_cases hjchart : Fin.succ j = chart
    · rw [hjchart, hqchart]
      simp only [map_one]
      exact Lchart.one_mem
    · let i := e.symm ⟨Fin.succ j, hjchart⟩
      have hi : e i = ⟨Fin.succ j, hjchart⟩ := Equiv.apply_symm_apply e _
      have hidx : (e i).1 = Fin.succ j := congrArg Subtype.val hi
      refine IntermediateField.subset_adjoin k _ ⟨i, ?_⟩
      change residue V (q (e i).1) = residue V (q (Fin.succ j))
      rw [hidx]

/-- Algebraicity over all tail-coordinate residues transfers to any projective
chart's affine residue-coordinate family. -/
theorem chartCoordinateResidue_algebraic_of_tail
    {V : Type*} [CommRing V] [IsLocalRing V]
    [Algebra k V] [Algebra k (ResidueField V)]
    [IsScalarTower k V (ResidueField V)]
    (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1)
    (hq0res : residue V (q 0) = 0)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun j : Fin m ↦ residue V (q (Fin.succ j))) :
        IntermediateField k (ResidueField V))
      (ResidueField V)) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun i : Fin m ↦ residue V (q (e i).1)) :
        IntermediateField k (ResidueField V))
      (ResidueField V) := by
  have hfield := chartCoordinateResidue_adjoin_eq_tail
    (k := k) (m := m) (V := V) q chart e hqchart hq0res
  exact hfield.symm ▸ halg

/-- An algebraic residue field generated by a finite family has a
transcendence basis selected from that family. This is the finite residue
basis needed before inverting the corresponding chart-coordinate lifts. -/
theorem exists_transcendenceBasis_subset_of_intermediateAdjoin_algebraic
    {κ : Type*} [Field κ] [Algebra k κ]
    (s : Set κ)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin k s) κ) :
    ∃ t : Set κ, t ⊆ s ∧ IsTranscendenceBasis k ((↑) : t → κ) := by
  let A := Algebra.adjoin k s
  let E := IntermediateField.adjoin k s
  letI : Algebra A E := (Subalgebra.inclusion
    (IntermediateField.algebra_adjoin_le_adjoin k s)).toAlgebra
  letI : Algebra E κ := E.toSubalgebra.toAlgebra
  letI : Algebra A κ := A.val.toAlgebra
  have hTower : IsScalarTower A E κ :=
    Subalgebra.inclusion.isScalarTower_right
      (IntermediateField.algebra_adjoin_le_adjoin k s) κ
  have hAEalg : Algebra.IsAlgebraic A E :=
    Stafford38.Geometry.RelativeDivisorialTower.intermediateAdjoin_isAlgebraic_over_algebraAdjoin
      k s
  letI : Algebra.IsAlgebraic A E := hAEalg
  letI : Algebra.IsAlgebraic E κ := halg
  have hAκ : Algebra.IsAlgebraic A κ :=
    @Algebra.IsAlgebraic.trans A E κ _ _ _ _ _ _ hTower _ hAEalg halg
  have hAκ' : Algebra.IsAlgebraic (Algebra.adjoin k s) κ := by
    simpa [A] using hAκ
  exact @exists_isTranscendenceBasis_subset k κ inferInstance inferInstance
    inferInstance inferInstance inferInstance s hAκ'

/-- In the retained projective chart, algebraicity of the tail-residue field
selects a transcendence basis from the actual affine chart-coordinate
residues, once the normalized denominator has residue zero. -/
theorem exists_chartCoordinate_residue_transcendenceBasis
    {V : Type*} [CommRing V] [IsLocalRing V]
    [Algebra k V] [Algebra k (ResidueField V)]
    [IsScalarTower k V (ResidueField V)]
    (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1) (hq0res : residue V (q 0) = 0)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun j : Fin m ↦ residue V (q (Fin.succ j))) :
        IntermediateField k (ResidueField V))
      (ResidueField V)) :
    ∃ t : Set (ResidueField V),
      t ⊆ Set.range (fun i : Fin m ↦ residue V (q (e i).1)) ∧
        IsTranscendenceBasis k ((↑) : t → ResidueField V) := by
  have hchartAlg := chartCoordinateResidue_algebraic_of_tail
    (k := k) (m := m) (V := V) q chart e hqchart hq0res halg
  exact exists_transcendenceBasis_subset_of_intermediateAdjoin_algebraic
    (k := k) _ hchartAlg

/-- The selected chart-coordinate residue basis is finite, so its elements can
be used as a finite coefficient family in a localization argument. -/
theorem exists_finite_chartCoordinate_residue_transcendenceBasis
    {V : Type*} [CommRing V] [IsLocalRing V]
    [Algebra k V] [Algebra k (ResidueField V)]
    [IsScalarTower k V (ResidueField V)]
    (q : Fin (m + 1) → V) (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hqchart : q chart = 1) (hq0res : residue V (q 0) = 0)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun j : Fin m ↦ residue V (q (Fin.succ j))) :
        IntermediateField k (ResidueField V))
      (ResidueField V)) :
    ∃ s : Set (ResidueField V), s.Finite ∧
      s ⊆
        Set.range (fun i : Fin m ↦ residue V (q (e i).1)) ∧
      IsTranscendenceBasis k ((↑) : s → ResidueField V) := by
  obtain ⟨t, htSub, htb⟩ := exists_chartCoordinate_residue_transcendenceBasis
    (k := k) q chart e hqchart hq0res halg
  have hfin : t.Finite := (Set.finite_range _).subset htSub
  exact ⟨t, hfin, htSub, htb⟩

/-- The chart equation quotient is the affine generic chart subalgebra inside
its component function field; this is an algebraic affine presentation. -/
noncomputable def componentChartEquationQuotient_equiv_genericSubalgebra
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e) ≃ₐ[k]
      chartGenericPointSubalgebra P chart e := by
  let evalA : MvPolynomial (Fin m) k →ₐ[k] ComponentFractionField P :=
    MvPolynomial.aeval (chartGenericPoint P chart e)
  have heval : (evalA : MvPolynomial (Fin m) k →+* ComponentFractionField P) =
      MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e) := rfl
  have hker : componentChartEquationIdeal P chart e =
      RingHom.ker (evalA : MvPolynomial (Fin m) k →+* ComponentFractionField P) := by
    rw [heval]
    exact componentChartEquationIdeal_eq_genericEvalKer P chart e hchart
  have hrange : Algebra.adjoin k (Set.range (chartGenericPoint P chart e)) = evalA.range := by
    simpa [evalA] using Algebra.adjoin_range_eq_range_aeval k
      (chartGenericPoint P chart e)
  exact (Ideal.quotientEquivAlgOfEq k hker).trans
    ((Ideal.quotientKerEquivRange evalA).trans
      (Subalgebra.equivOfEq evalA.range
        (Algebra.adjoin k (Set.range (chartGenericPoint P chart e))) hrange.symm))

/-- Compatibility name for the canonical chart quotient map owned by
`ComponentProjectiveChartKernel`. -/
abbrev componentChartEquationGenericPointMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e) →ₐ[k]
      ComponentFractionField P :=
  ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap
    P chart e hchart

@[simp] theorem componentChartEquationGenericPointMap_mk
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0)
    (f : MvPolynomial (Fin m) k) :
    componentChartEquationGenericPointMap P chart e hchart
        (Ideal.Quotient.mk _ f) =
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e) f := by
  exact ComponentProjectiveChartKernel.canonicalComponentChartEquationGenericPointMap_mk
    P chart e hchart f

/-- A normalized projective lift in a subring of the component function field
has exactly the generic chart coordinates as its affine coordinates. -/
theorem chartGenericPoint_eq_normalized_lift
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {V : Type u} [CommRing V] [Algebra k V]
    [Algebra V (ComponentFractionField P)]
    [IsScalarTower k V (ComponentFractionField P)]
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (q : Fin (m + 1) → V) (scale : ComponentFractionField P)
    (hqchart : q chart = 1)
    (hq : ∀ a, algebraMap V (ComponentFractionField P) (q a) =
      scale * componentProjectivePoint P a) :
    chartGenericPoint P chart e =
      fun i ↦ algebraMap V (ComponentFractionField P) (q (e i).1) := by
  funext i
  exact (chart_coordinates_agree_with_generic_point P
    (algebraMap V (ComponentFractionField P)) q chart e hqchart scale hq i).symm

/-- The actual affine generic chart domain is finite type over the ground field. -/
theorem chartGenericPointSubalgebra_finiteType
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart) :
    Algebra.FiniteType k (chartGenericPointSubalgebra P chart e) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

/-- The actual affine generic chart domain has the component function field as
its fraction field. -/
theorem chartGenericPointSubalgebra_isFractionRing
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    IsFractionRing (chartGenericPointSubalgebra P chart e)
      (ComponentFractionField P) := by
  let A := Algebra.adjoin k (Set.range (chartGenericPoint P chart e))
  have hgen := chartGenericPoint_adjoin_eq_top P chart e hchart
  refine IsFractionRing.of_field A (ComponentFractionField P) fun z => ?_
  have hz : z ∈ (⊤ : IntermediateField k (ComponentFractionField P)) := Set.mem_univ z
  rw [← hgen] at hz
  rw [IntermediateField.mem_adjoin_iff_div] at hz
  rcases hz with ⟨a, ha, b, hb, hab⟩
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩

/-- The exact dehomogenized chart equation quotient embeds in the component
function field and has that field as its fraction field. -/
theorem componentChartEquationQuotient_isFractionRing
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (chart : Fin (m + 1))
    (e : Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart)
    (hchart : componentProjectivePoint P chart ≠ 0) :
    let R := MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e
    letI : Algebra R (ComponentFractionField P) :=
      (componentChartEquationGenericPointMap P chart e hchart).toRingHom.toAlgebra
    IsFractionRing R (ComponentFractionField P) := by
  let A := Algebra.adjoin k (Set.range (chartGenericPoint P chart e))
  let eqv := componentChartEquationQuotient_equiv_genericSubalgebra P chart e hchart
  let f := componentChartEquationGenericPointMap P chart e hchart
  letI : IsFractionRing A (ComponentFractionField P) :=
    chartGenericPointSubalgebra_isFractionRing P chart e hchart
  letI : Algebra (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e)
      (ComponentFractionField P) := f.toRingHom.toAlgebra
  have hinj : Function.Injective f := by
    intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hEval : MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e) a =
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e) b := by
      dsimp only [f] at h
      simpa only [componentChartEquationGenericPointMap_mk] using h
    apply Ideal.Quotient.eq.mpr
    change (MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e)) a =
      (MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e)) b at hEval
    have hdiff : MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e) (a - b) = 0 := by
      change (MvPolynomial.eval₂Hom (algebraMap k (ComponentFractionField P))
        (chartGenericPoint P chart e)) (a - b) = 0
      rw [map_sub, hEval, sub_self]
    rw [componentChartEquationIdeal_eq_genericEvalKer P chart e hchart]
    exact RingHom.mem_ker.mpr hdiff
  letI : FaithfulSMul
      (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e)
      (ComponentFractionField P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field
    (MvPolynomial (Fin m) k ⧸ componentChartEquationIdeal P chart e)
    (ComponentFractionField P) fun z => ?_
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A z
  refine ⟨eqv.symm a, eqv.symm b, ?_⟩
  have hfa : f (eqv.symm a) = (a : ComponentFractionField P) := by
    change ((eqv (eqv.symm a) : A) : ComponentFractionField P) = _
    exact congrArg Subtype.val (eqv.apply_symm_apply a)
  have hfb : f (eqv.symm b) = (b : ComponentFractionField P) := by
    change ((eqv (eqv.symm b) : A) : ComponentFractionField P) = _
    exact congrArg Subtype.val (eqv.apply_symm_apply b)
  calc
    z = (a : ComponentFractionField P) / (b : ComponentFractionField P) := hab.symm
    _ = f (eqv.symm a) / f (eqv.symm b) := by rw [hfa, hfb]


#print axioms chartGenericPoint_adjoin_eq_top
#print axioms chartCoordinateResidue_adjoin_eq_tail
#print axioms chartCoordinateResidue_algebraic_of_tail
#print axioms exists_transcendenceBasis_subset_of_intermediateAdjoin_algebraic
#print axioms exists_chartCoordinate_residue_transcendenceBasis
#print axioms exists_finite_chartCoordinate_residue_transcendenceBasis
#print axioms componentChartEquationQuotient_equiv_genericSubalgebra
#print axioms componentChartEquationGenericPointMap
#print axioms chartGenericPoint_eq_normalized_lift
#print axioms componentChartEquationQuotient_isFractionRing
#print axioms chartGenericPointSubalgebra_finiteType
#print axioms chartGenericPointSubalgebra_isFractionRing

end Stafford38.Geometry.ChartGenericPointFractionRing
