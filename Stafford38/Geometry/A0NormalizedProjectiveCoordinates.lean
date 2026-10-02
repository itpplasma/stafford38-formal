import Stafford38.Geometry.A0ChartGeneratorCoordinates
import Stafford38.Geometry.ChartGenericPointFractionRing

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace Stafford38.Geometry.A0NormalizedProjectiveCoordinates

open Stafford38.Geometry.ProjectiveChartSameFieldOverlap
open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.A0ChartGeneratorCoordinates
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveChartKernel
open Stafford38.Geometry.ChartGenericPointFractionRing

universe u v w

private theorem selectedChartAwayEquiv_base
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q)
    (x : SelectedAffineChartQuotient (k := k) P j) :
    selectedChartAwayEquivOfQuotientEquiv P j hsel
      (algebraMap (SelectedAffineChartQuotient (k := k) P j)
        (SelectedAffineChartLocalization (k := k) P j) x) =
      algebraMap Q (Localization.Away (hsel (selectedAffineChartDenominator P j)))
        (hsel x) := by
  let R := SelectedAffineChartQuotient (k := k) P j
  let S := SelectedAffineChartLocalization (k := k) P j
  let T := Localization.Away (hsel (selectedAffineChartDenominator P j))
  let M := Submonoid.powers (selectedAffineChartDenominator P j)
  let N := Submonoid.powers (hsel (selectedAffineChartDenominator P j))
  letI : IsLocalization M S := Localization.isLocalization
  letI : IsLocalization.Away
      (hsel.toRingEquiv.toRingHom (selectedAffineChartDenominator P j)) T :=
    Localization.isLocalization
  have hmap : Submonoid.map hsel M = N := by
    simp [M, N, Submonoid.map_powers]
  change IsLocalization.algEquivOfAlgEquiv
      (S := S) (Q := T) (h := hsel) hmap
    (algebraMap R S x) = algebraMap Q T (hsel x)
  exact IsLocalization.algEquivOfAlgEquiv_eq
    (S := S) (Q := T) (h := hsel) hmap x

/-- In the common open, the original variable belonging to the selected
projective chart is the inverse of the distinguished chart coordinate. -/
theorem canonicalChart_selectedGenerator_product
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0)
    {B : Type w} [CommRing B]
    [Algebra
      (Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))) B]
    (M : Ideal B) [M.IsPrime]
    (f : Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j))))
    (e : Localization.Away f ≃ₐ[
      Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))]
      Localization.Away (algebraMap _ B f)) :
    let Q := Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
        (SelectedAffineCoordinateEquiv j) (by
          simpa [componentProjectivePoint] using hxj)
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    algebraMap Cq C (algebraMap Q Cq g) *
      originalAffineChartToCommonOpen P j hxj hsel M f e
        (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X j)) = 1 := by
  exact selectedGenerator_commonOpen_product P j hxj
    (componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
      (SelectedAffineCoordinateEquiv j) (by
        simpa [componentProjectivePoint] using hxj)) M f e

/-- The canonical selected-chart generic point, transported into the actual
common open, gives every normalized projective coordinate.  Its selected
coordinate is one, and every other coordinate equals the distinguished
coordinate times the corresponding original affine generator. -/
theorem canonicalChart_all_normalized_projective_coordinates
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0)
    {B : Type w} [CommRing B]
    [Algebra
      (Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))) B]
    (M : Ideal B) [M.IsPrime]
    (f : Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j))))
    (e : Localization.Away f ≃ₐ[
      Algebra.adjoin k (Set.range
        (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))]
      Localization.Away (algebraMap _ B f)) :
    let Q := Algebra.adjoin k (Set.range
      (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
    let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
      componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
        (SelectedAffineCoordinateEquiv j) (by
          simpa [componentProjectivePoint] using hxj)
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    let φ := originalAffineChartToCommonOpen P j hxj hsel M f e
    let q : Fin (m + 1) → C := Fin.cases
      (algebraMap Cq C (algebraMap Q Cq g))
      (fun i => if hij : i = j then 1 else
        algebraMap Cq C (algebraMap Q Cq
          (hsel (selectedAffineChartVariableClass P j i hij))))
    q (Fin.succ j) = 1 ∧
      ∀ i : Fin m, q (Fin.succ i) =
        q 0 * φ (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := by
  dsimp
  let Q := Algebra.adjoin k (Set.range
    (chartGenericPoint P (Fin.succ j) (SelectedAffineCoordinateEquiv j)))
  let hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q :=
    componentChartEquationQuotient_equiv_genericSubalgebra P (Fin.succ j)
      (SelectedAffineCoordinateEquiv j) (by
        simpa [componentProjectivePoint] using hxj)
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  let φ := originalAffineChartToCommonOpen P j hxj hsel M f e
  let q : Fin (m + 1) → C := Fin.cases
    (algebraMap Cq C (algebraMap Q Cq g))
    (fun i => if hij : i = j then 1 else
      algebraMap Cq C (algebraMap Q Cq
        (hsel (selectedAffineChartVariableClass P j i hij))))
  constructor
  · simp [q]
  · intro i
    by_cases hij : i = j
    · subst i
      simp only [q, Fin.cases_succ, dite_true]
      have hprod := canonicalChart_selectedGenerator_product P j hxj M f e
      simpa [Q, hsel, g, Cq, C, φ, Fin.cases, dite_true] using hprod.symm
    · simp only [q, Fin.cases_succ, dite_false, hij]
      exact originalGenerator_commonOpen_identity P j i hij hxj hsel M f e

/-- Any selected-chart column with the canonical denominator and variable
entries has its original-affine projective coordinates on the common open. -/
theorem q_column_commonOpen_coordinates
    {k : Type u} [Field k] {m : ℕ}
    {Q : Type v} [CommRing Q] [Algebra k Q]
    {B : Type w} [CommRing B] [Algebra Q B]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m)
    (hxj : componentCoordinate P j ≠ 0)
    (hsel : SelectedAffineChartQuotient (k := k) P j ≃ₐ[k] Q)
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f))
    (qQ : Fin (m + 1) → Q)
    (hchart : qQ (Fin.succ j) = 1)
    (hzero : qQ 0 = hsel (selectedAffineChartDenominator P j))
    (hrows : ∀ i : Fin m, ∀ hij : i ≠ j,
      qQ (Fin.succ i) = hsel (selectedAffineChartVariableClass P j i hij)) :
    let g := hsel (selectedAffineChartDenominator P j)
    let Cq := genericOpenRing M f e
    let C := genericOpenExtraAwayB M f e g
    letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
    letI : Algebra Q Cq := inferInstance
    letI : Algebra Cq C := inferInstance
    letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
    let qU : Fin (m + 1) → C := fun i =>
      algebraMap Cq C (algebraMap Q Cq (qQ i))
    ∀ i : Fin m,
      qU (Fin.succ i) = qU 0 *
        originalAffineChartToCommonOpen P j hxj hsel M f e
          (Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i)) := by
  classical
  dsimp
  let g := hsel (selectedAffineChartDenominator P j)
  let Cq := genericOpenRing M f e
  let C := genericOpenExtraAwayB M f e g
  letI : Semiring C := (inferInstance : CommSemiring C).toSemiring
  letI : Algebra Q Cq := inferInstance
  letI : Algebra Cq C := inferInstance
  letI : Algebra Q C := Algebra.compHom C (algebraMap Q Cq)
  intro i
  by_cases hij : i = j
  · subst i
    simpa [hzero, hchart] using
      (selectedGenerator_commonOpen_product P j hxj hsel M f e).symm
  · have hother := originalGenerator_commonOpen_identity
      P j i hij hxj hsel M f e
    simpa [hzero, hrows i hij] using hother

#print axioms canonicalChart_selectedGenerator_product
#print axioms canonicalChart_all_normalized_projective_coordinates

end Stafford38.Geometry.A0NormalizedProjectiveCoordinates
end
