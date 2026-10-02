import Stafford38.Geometry.CorrectedNormalizedTangentLattice

namespace Stafford38.Geometry.CorrectedNormalizedTangentLattice.ConcreteOracle

open Stafford38.GeometryFormalDivisorTangent

noncomputable section

set_option autoImplicit false

abbrev PS := PowerSeries ℚ
abbrev L := LaurentSeries ℚ

def q (i : Fin 4) : PS :=
  if i = 0 then PowerSeries.X ^ 2
  else if i = 1 then PowerSeries.X ^ 3
  else if i = 2 then PowerSeries.C 1 + PowerSeries.C 2 * (PowerSeries.X : PS)
  else PowerSeries.C 1

def Z : Matrix (Fin 4) Unit PS := fun i _ => if i = 2 then 1 else 0

def lambda : Unit → PS := fun _ => PowerSeries.C 2

def tau (i : Fin 4) : PS :=
  if i = 0 then PowerSeries.C 2
  else if i = 1 then PowerSeries.C 3 * (PowerSeries.X : PS)
  else 0

def A : PS →+* L := algebraMap PS L

def xL : L := A PowerSeries.X

def zL : Fin 4 → L := fun i => A (Z i ())

def tauL : Fin 4 → L := fun i => A (tau i)

def rawL : Fin 4 → L := fun i => A (PowerSeries.derivative ℚ (q i))

def fixed : Option Unit → (Fin 4 → L)
  | none => fun i => A (q i)
  | some _ => zL

theorem powerSeriesX_not_unit : ¬ IsUnit (PowerSeries.X : PS) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

theorem hfactor : ∀ i,
    PowerSeries.derivative ℚ (q i) - Z.mulVec lambda i =
      (PowerSeries.X : PS) ^ 1 * tau i := by
  have hC2 : PowerSeries.C (2 : ℚ) = (2 : PS) := by
    rw [PowerSeries.C_eq_algebraMap]
    exact map_ofNat (algebraMap ℚ PS) 2
  have hC3 : PowerSeries.C (3 : ℚ) = (3 : PS) := by
    rw [PowerSeries.C_eq_algebraMap]
    exact map_ofNat (algebraMap ℚ PS) 3
  have hD2 : PowerSeries.derivative ℚ (q 2) = PowerSeries.C (2 : ℚ) := by
    simp [q, Derivation.map_add, Derivation.leibniz]
  have hZ2 : Z.mulVec lambda 2 = PowerSeries.C (2 : ℚ) := by
    simp [Z, lambda, Matrix.mulVec, dotProduct]
  intro i
  fin_cases i
  · simp [q, tau, Z, lambda, hC2, Matrix.mulVec, dotProduct,
      PowerSeries.derivative_pow, PowerSeries.derivative_X] <;> ring
  · simp [q, tau, Z, lambda, hC3, Matrix.mulVec, dotProduct,
      PowerSeries.derivative_pow, PowerSeries.derivative_X] <;> ring
  · change PowerSeries.derivative ℚ (q 2) - Z.mulVec lambda 2 =
      (PowerSeries.X : PS) ^ 1 * tau 2
    rw [hD2, hZ2]
    simp [tau]
  · simp [q, tau, Z, lambda, Matrix.mulVec, dotProduct,
      PowerSeries.derivative_C]

theorem raw_decomposition : rawL = xL • tauL + 2 • zL := by
  have h : rawL - 2 • zL = xL • tauL := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hi := congrArg A (hfactor i)
    rw [map_sub, map_mul] at hi
    have hmul : A (Z.mulVec lambda i) = 2 * A (Z i ()) := by
      by_cases hi : i = 2
      · subst i
        simp [Matrix.mulVec, dotProduct, lambda, Z, A]
      · simp [Matrix.mulVec, dotProduct, lambda, Z, A, hi]
    rw [hmul] at hi
    simpa [rawL, tauL, zL, xL, A] using hi
  calc
    rawL = (rawL - 2 • zL) + 2 • zL := (sub_add_cancel _ _).symm
    _ = xL • tauL + 2 • zL := by rw [h]

theorem tau_explicit_laurent_decomposition :
    tauL = xL⁻¹ • rawL + (-2 * xL⁻¹) • zL := by
  have hx : xL ≠ 0 := by
    simpa [xL, A] using
      (IsFractionRing.injective PS L).ne (PowerSeries.X_ne_zero (R := ℚ))
  have hrel : rawL - 2 • zL = xL • tauL := by
    calc
      rawL - 2 • zL = (xL • tauL + 2 • zL) - 2 • zL := by
        rw [raw_decomposition]
      _ = xL • tauL := add_sub_cancel_right _ _
  have hscale : xL⁻¹ • rawL - (2 * xL⁻¹) • zL = tauL := by
    have hh := congrArg (fun v : Fin 4 → L => xL⁻¹ • v) hrel
    have hleft : xL⁻¹ • (rawL - 2 • zL) =
        xL⁻¹ • rawL - (2 * xL⁻¹) • zL := by
      ext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [hleft] at hh
    simpa [smul_smul, inv_mul_cancel₀ hx] using hh
  have hdecomp : tauL = xL⁻¹ • rawL + (-2 * xL⁻¹) • zL := by
    calc
      tauL = xL⁻¹ • rawL - (2 * xL⁻¹) • zL := hscale.symm
      _ = xL⁻¹ • rawL + (-2 * xL⁻¹) • zL := by
        rw [sub_eq_add_neg, ← neg_smul]
        congr 1
        ring
  exact hdecomp

theorem tau_has_explicit_raw_span_coefficients :
    tauL ∈ Submodule.span L (Set.range fixed ∪ {rawL}) := by
  let S : Submodule L (Fin 4 → L) := Submodule.span L (Set.range fixed ∪ {rawL})
  have hz : zL ∈ S := by
    apply Submodule.subset_span
    exact Set.mem_union_left _ ⟨some (), rfl⟩
  have hraw : rawL ∈ S :=
    Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _))
  rw [tau_explicit_laurent_decomposition]
  exact S.add_mem (S.smul_mem _ hraw) (S.smul_mem _ hz)

theorem example_generic_fibre_identity :
    Stafford38.Geometry.GeneralTangentLimitCriterion.genericFibre
        (Stafford38.Geometry.PaperDivisorTangent.normalizedTangentLattice q Z tau) =
      Submodule.span L (Set.range (fun j : FormalTangentColumn Unit =>
        fun i => A (formalTangentMatrix q Z
          (fun i => PowerSeries.derivative ℚ (q i)) i j))) := by
  simpa [A] using
    Stafford38.Geometry.CorrectedNormalizedTangentLattice.genericFibre_normalizedTangentLattice_eq_span_derivative
      (k := ℚ) (n := 3) (κ := Unit) q Z tau lambda 1 hfactor

end

end Stafford38.Geometry.CorrectedNormalizedTangentLattice.ConcreteOracle

#print axioms Stafford38.Geometry.CorrectedNormalizedTangentLattice.ConcreteOracle.powerSeriesX_not_unit
#print axioms Stafford38.Geometry.CorrectedNormalizedTangentLattice.ConcreteOracle.tau_has_explicit_raw_span_coefficients
#print axioms Stafford38.Geometry.CorrectedNormalizedTangentLattice.ConcreteOracle.example_generic_fibre_identity
