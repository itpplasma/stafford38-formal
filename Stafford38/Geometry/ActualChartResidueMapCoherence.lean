module
public import Mathlib.RingTheory.Localization.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.ActualChartResidueMapCoherence

universe u v w x y z a b c

/-- The actual residue map on the selected coefficient localization agrees
with the residue map induced by the chosen coefficient-field embedding. The
proof checks equality on the original polynomial ring, using the recorded
generator identities at each stage of the same chart/normalization diagram. -/
theorem residue_map_coherence
    {k : Type u} {P : Type v} {E : Type w} {R : Type x} {Q : Type y}
    {B : Type z} {L : Type a} {V : Type b} {κ : Type c}
    [CommSemiring k] [CommSemiring P] [IsDomain P]
    [CommSemiring E] [Algebra P E] [IsLocalization (nonZeroDivisors P) E]
    [Algebra k P] [Algebra k E] [IsScalarTower k P E]
    [CommSemiring R] [Algebra k R]
    [CommSemiring Q] [Algebra k Q]
    [CommSemiring B] [Algebra R B]
    [CommSemiring L] [Algebra k L]
    [CommSemiring V] [Algebra k V]
    [CommSemiring κ] [Algebra k κ]
    (eA : P ≃ₐ[k] R)
    (iA : R →ₐ[k] E) (fEV : E →ₐ[k] V) (fA : R →ₐ[k] V)
    (g : E →ₐ[k] κ) (fEL : E →ₐ[k] L)
    (inclBL : B →+* L) (fLoc : L →+* V) (fB : B →+* V)
    (j : R →+* B) (r0Q : R →ₐ[k] Q) (qV : Q →ₐ[k] V)
    (rhoV : V →+* κ) (rhoL : L →+* κ)
    (hELgen : ∀ p : P,
      fEL (algebraMap P E p) = inclBL (j (eA p)))
    (hLoc : fLoc.comp inclBL = fB)
    (hRhoL : rhoL = rhoV.comp fLoc)
    (hcomp : fB.comp j = (qV.comp r0Q).toRingHom)
    (hAchart : fA.comp eA.toAlgHom = qV.comp (r0Q.comp eA.toAlgHom))
    (hfE : (fEV.comp iA).toRingHom = fA.toRingHom)
    (hiA : ∀ p : P, iA (eA p) = algebraMap P E p)
    (hresE : rhoV.comp fEV.toRingHom = g.toRingHom) :
    rhoL.comp fEL.toRingHom = g.toRingHom := by
  apply IsLocalization.ringHom_ext (M := nonZeroDivisors P)
  apply RingHom.ext
  intro p
  change rhoL (fEL (algebraMap P E p)) = g (algebraMap P E p)
  calc
    rhoL (fEL (algebraMap P E p)) =
        rhoV (fLoc (fEL (algebraMap P E p))) := by
      rw [hRhoL]
      rfl
    _ = rhoV (fLoc (inclBL (j (eA p)))) :=
      congrArg (fun z : L => rhoV (fLoc z)) (hELgen p)
    _ = rhoV (fB (j (eA p))) := by
      exact congrArg rhoV (RingHom.congr_fun hLoc (j (eA p)))
    _ = rhoV (qV (r0Q (eA p))) := by
      exact congrArg rhoV (RingHom.congr_fun hcomp (eA p))
    _ = rhoV (fA (eA p)) := by
      exact congrArg rhoV (AlgHom.congr_fun hAchart p).symm
    _ = rhoV (fEV (iA (eA p))) := by
      exact congrArg rhoV (RingHom.congr_fun hfE (eA p)).symm
    _ = rhoV (fEV (algebraMap P E p)) := by
      exact congrArg (fun z : E => rhoV (fEV z)) (hiA p)
    _ = g (algebraMap P E p) := by
      exact RingHom.congr_fun hresE (algebraMap P E p)

end Stafford38.Geometry.ActualChartResidueMapCoherence
