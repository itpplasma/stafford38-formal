import Stafford38.Geometry.RetainedPlaceConormalTransport
import Stafford38.Geometry.ResidueMinorSelection
import Stafford38.Geometry.PaperResidueDerivationFrame
import Stafford38.Geometry.PaperCompletedResidueDerivationFrame
import Stafford38.Geometry.RetainedGroundMapIdentification

/-!
# Generic-point equations for an actual retained chart

The retained-place transport theorem identifies the point of its completed
projective column with the image of the component generic point.  These
abstract map lemmas extract the base equations and exact generic kernel from
that identification, without repeating the retained completion construction.
-/

namespace Stafford38.Geometry.PaperRetainedChartAssembly

open IsLocalRing
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.KaehlerVisibleDerivationFrame
open Stafford38.GeometryResidueMinorSelection
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.Geometry.PaperResidueDerivationFrame
open Stafford38.Geometry.PaperCompletedResidueDerivationFrame
open Stafford38.Geometry.RetainedGroundMapIdentification

universe u

variable {k : Type u} [Field k] {m : ℕ}
variable {κ : Type u} [Field κ] [Algebra k κ]

set_option maxHeartbeats 4000000 in
/-- Lane-C algebraicity of the residue coordinates on the affine tail
produces the actual coefficientwise derivation columns and a unit selected
minor on the full retained projective column. -/
theorem exists_retained_projective_derivation_columns
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    let κ := ResidueField V
    letI : Algebra k κ := retainedResidueGroundAlgebra P i W
    ∀ (q : Fin (m + 1) → V),
      Algebra.IsAlgebraic
        (IntermediateField.adjoin k
          (Set.range fun j : Fin m ↦ residue V (q (Fin.succ j))) :
            IntermediateField k κ) κ →
      ∃ (rows : Fin (Module.finrank κ (Ω[κ⁄k])) ↪ Fin (m + 1))
        (D : Fin (Module.finrank κ (Ω[κ⁄k])) → Derivation k κ κ),
        (∀ i j, D j (PowerSeries.constantCoeff
          (retainedToCompletedPowerSeries W (q (rows i)))) =
            if i = j then 1 else 0) ∧
        PowerSeries.constantCoeff
          (selectedMinor
            (coefficientwiseTangentMatrix
              (fun a ↦ retainedToCompletedPowerSeries W (q a)) D) rows).det = 1 := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let κ := ResidueField V
  letI : Algebra k κ := retainedResidueGroundAlgebra P i W
  dsimp only
  intro q halg
  let qhat : Fin (m + 1) → PowerSeries κ :=
    fun a ↦ retainedToCompletedPowerSeries W (q a)
  let qbar : Fin m → κ := fun j ↦ residue V (q (Fin.succ j))
  have hcoeff : ∀ j, PowerSeries.constantCoeff (qhat (Fin.succ j)) = qbar j := by
    intro j
    exact constantCoeff_retainedToCompleted_eq_residue W (q (Fin.succ j))
  simpa [qhat] using
    (exists_projective_derivation_frame_of_residue_coordinates
      qhat qbar hcoeff (by simpa [qbar] using halg))

/-- Component equations remain zero after a field map, once its ground map and
its image of the generic coordinate point are identified. -/
theorem component_equations_vanish_after_point_transport
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {L : Type u} [CommSemiring L] [Algebra k L]
    (lift : ComponentFractionField P →+* L)
    (hground : lift.comp (algebraMap k (ComponentFractionField P)) =
      algebraMap k L)
    (point : Fin m → L)
    (hpoint : lift ∘ componentCoordinate P = point)
    {f : MvPolynomial (Fin m) k} (hf : f ∈ P.asIdeal) :
    MvPolynomial.eval₂ (algebraMap k L) point f = 0 := by
  have hgeneric : MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
      (componentCoordinate P) f = 0 := by
    rw [← componentAffineGenericPointMap_eq_eval₂]
    exact componentAffineGenericPointMap_eq_zero_of_mem P hf
  have hmap := MvPolynomial.eval₂_comp_left lift
    (algebraMap k (ComponentFractionField P)) (componentCoordinate P) f
  rw [hgeneric, map_zero] at hmap
  have htransport :
      MvPolynomial.eval₂ (lift.comp (algebraMap k (ComponentFractionField P)))
        (lift ∘ componentCoordinate P) f = 0 := hmap.symm
  rw [← hground, ← hpoint]
  exact htransport

/-- Evaluation at the transported generic point has exactly the component
prime as its kernel when the field map is injective. -/
theorem component_generic_kernel_after_point_transport
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {L : Type u} [Field L] [Algebra k L]
    (lift : ComponentFractionField P →+* L)
    (hinjective : Function.Injective lift)
    (hground : lift.comp (algebraMap k (ComponentFractionField P)) =
      algebraMap k L)
    (point : Fin m → L)
    (hpoint : lift ∘ componentCoordinate P = point) :
    ∀ f : MvPolynomial (Fin m) k,
      MvPolynomial.eval point (MvPolynomial.map (algebraMap k L) f) = 0 ↔
        f ∈ P.asIdeal := by
  intro f
  have heval : MvPolynomial.eval point (MvPolynomial.map (algebraMap k L) f) =
      lift (componentAffineGenericPointMap P f) := by
    rw [← hpoint, ← hground, MvPolynomial.eval_map,
      ← MvPolynomial.eval₂_comp_left,
      ← componentAffineGenericPointMap_eq_eval₂]
  rw [heval, map_eq_zero_iff lift hinjective]
  have hker : RingHom.ker (componentAffineGenericPointMap P) = P.asIdeal :=
    componentAffineGenericPointMap_ker P
  constructor
  · intro hf
    have hmem : f ∈ RingHom.ker (componentAffineGenericPointMap P) :=
      RingHom.mem_ker.mpr hf
    rw [hker] at hmem
    exact hmem
  · intro hf
    have hmem : f ∈ RingHom.ker (componentAffineGenericPointMap P) := by
      rw [hker]
      exact hf
    exact RingHom.mem_ker.mp hmem

end Stafford38.Geometry.PaperRetainedChartAssembly
