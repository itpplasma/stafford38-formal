import Stafford38.Geometry.ValuationCenterDominatesLocalPrime
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ProjectiveChartNormalizationCenter

open IsLocalRing

universe u

/-- An integral closure inside the ambient field is contained in every
valuation subring that contains the original domain. -/
theorem integralClosure_subring_le_valuationSubring
    {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) :
    (integralClosure R K).toSubring ≤ V.toSubring := by
  letI : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  exact Subring.integralClosure_subring_le_iff.mpr hRV

/-- The center on the integral closure is the contraction of the retained
valuation ring's maximal ideal along the canonical inclusion of the closure. -/
def integralClosureCenter
    {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) :
    Ideal (integralClosure R K).toSubring := by
  let hBV : (integralClosure R K).toSubring ≤ V.toSubring :=
    integralClosure_subring_le_valuationSubring R V hRV
  exact (maximalIdeal V.toLocalSubring.toSubring).comap
    (Subring.inclusion hBV)

/-- The contracted ideal is literally the kernel of the map to the residue
field of the valuation ring. -/
theorem integralClosureCenter_eq_residueKernel
    {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) :
    integralClosureCenter R V hRV =
      RingHom.ker
        ((Ideal.Quotient.mk (maximalIdeal V.toLocalSubring.toSubring)).comp
          (Subring.inclusion
            (integralClosure_subring_le_valuationSubring R V hRV))) := by
  rw [integralClosureCenter, ← RingHom.comap_ker, Ideal.mk_ker]
  rfl

theorem integralClosureCenter_isPrime
    {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) :
    (integralClosureCenter R V hRV).IsPrime := by
  let hBV : (integralClosure R K).toSubring ≤ V.toSubring :=
    integralClosure_subring_le_valuationSubring R V hRV
  have hmax : (maximalIdeal V.toLocalSubring.toSubring).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal _
  change (maximalIdeal V.toLocalSubring.toSubring).comap
      (Subring.inclusion hBV) |>.IsPrime
  exact hmax.isPrime.comap _

/-- Any nonzero chart element vanishing at the valuation center makes the
normalization center nonzero. -/
theorem integralClosureCenter_ne_bot_of_nonzero_maximal
    {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring) (r : R)
    (hr0 : (r : K) ≠ 0)
    (hrmax : (Subring.inclusion hRV r) ∈
      maximalIdeal V.toLocalSubring.toSubring) :
    integralClosureCenter R V hRV ≠ ⊥ := by
  let hBV : (integralClosure R K).toSubring ≤ V.toSubring :=
    integralClosure_subring_le_valuationSubring R V hRV
  let b : (integralClosure R K).toSubring :=
    ⟨(r : K), by
      change IsIntegral R (algebraMap R K r)
      exact isIntegral_algebraMap⟩
  have hmap : Subring.inclusion hBV b = Subring.inclusion hRV r := by
    apply Subtype.ext
    rfl
  have hbcenter : b ∈ integralClosureCenter R V hRV := by
    change Subring.inclusion hBV b ∈ maximalIdeal V.toLocalSubring.toSubring
    rw [hmap]
    exact hrmax
  intro hbot
  have hb0 : b = 0 := by
    apply Ideal.mem_bot.mp
    simpa [hbot] using hbcenter
  apply hr0
  have hv := congrArg Subtype.val hb0
  exact hv

/-- The center above is precisely the prime required by the standard
local-domination lemma. No codimension or height assertion is included. -/
theorem localRing_at_integralClosureCenter_le_valuationSubring
    {K : Type u} [Field K] (R : Subring K) (V : ValuationSubring K)
    (hRV : R ≤ V.toSubring)
    (hp : (integralClosureCenter R V hRV).IsPrime) :
    LocalSubring.ofPrime (integralClosure R K).toSubring
        (integralClosureCenter R V hRV) ≤ V.toLocalSubring := by
  let hBV : (integralClosure R K).toSubring ≤ V.toSubring :=
    integralClosure_subring_le_valuationSubring R V hRV
  letI : (integralClosureCenter R V hRV).IsPrime := hp
  exact Stafford38.Geometry.localRing_at_contracted_maximalIdeal_le_valuationSubring
    (integralClosure R K).toSubring V hBV
    (integralClosureCenter R V hRV) rfl

#print axioms integralClosureCenter_isPrime
#print axioms integralClosureCenter_eq_residueKernel
#print axioms integralClosureCenter_ne_bot_of_nonzero_maximal
#print axioms localRing_at_integralClosureCenter_le_valuationSubring
#print axioms integralClosure_subring_le_valuationSubring

end Stafford38.Geometry.ProjectiveChartNormalizationCenter
