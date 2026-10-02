module
public import Stafford38.Geometry.ActualChartCenterHeight
public import Stafford38.Geometry.ActualChartCenterContraction
public import Stafford38.Geometry.ResidueBasisLocalization

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.ActualResidueCenterHeight

universe u v w x y z

/-- A residue map from a localization identifies its contraction with a given
normalization center. If the residue extension is algebraic and the ambient
function field has relative transcendence degree one, the center has height
one. All maps and center identities are explicit inputs, so this lemma does
not choose a different valuation or normalization model. -/
theorem height_one_of_localized_algebraic_residue
    {E : Type u} {B : Type v} {A : Type w} {F : Type x}
    {κ : Type y} {C : Type z}
    [Field E] [CommRing B] [IsDomain B] {S : Submonoid B}
    [CommRing A] [IsDomain A] [Algebra B A] [IsLocalization S A]
    [Algebra E A] [Algebra.FiniteType E A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra E F] [IsScalarTower E A F]
    [Field κ] [Algebra E κ] [Algebra.IsAlgebraic E κ]
    [CommRing C]
    (rhoA : A →+* κ) (rhoE : A →ₐ[E] κ)
    (hρ : (rhoE : A →+* κ) = rhoA)
    (rhoB : B →+* κ)
    (hrestrict : rhoA.comp (algebraMap B A) = rhoB)
    (e : B ≃+* C) (J : Ideal C)
    (hcenter : RingHom.ker rhoB = J.comap e.toRingHom)
    (hJ0 : J ≠ ⊥)
    (htrdeg : Algebra.trdeg E F = 1) : J.height = 1 := by
  have hmax' : (RingHom.ker (rhoE : A →+* κ)).IsMaximal :=
    Stafford38.Geometry.ResidueBasisLocalization.ker_isMaximal_of_algebraic_residue
      (E := E) (A := A) (K := κ) rhoE
  have hmax : (RingHom.ker rhoA).IsMaximal := by
    rw [← hρ]
    exact hmax'
  let p : PrimeSpectrum A := ⟨RingHom.ker rhoA, hmax.isPrime⟩
  letI : p.asIdeal.IsMaximal := hmax
  have hcontract :=
    Stafford38.Geometry.ActualChartCenterContraction.under_ker_eq_ker_of_restriction
      (B := B) (A := A) (K := κ) (ρA := rhoA) (ρB := rhoB) hrestrict
  have hcontractCenter : Ideal.under B p.asIdeal = J.comap e.toRingHom := by
    change Ideal.under B (RingHom.ker rhoA) = J.comap e.toRingHom
    exact hcontract.trans hcenter
  have hcontract0 : Ideal.under B p.asIdeal ≠ ⊥ := by
    rw [hcontractCenter]
    intro hbot
    apply hJ0
    apply le_antisymm
    · intro c hc
      obtain ⟨b, rfl⟩ := e.surjective c
      have hb : b ∈ J.comap e.toRingHom := hc
      rw [hbot] at hb
      simpa using hb
    · exact bot_le
  have hcomap0 : J.comap e.toRingHom ≠ ⊥ := by
    rw [← hcontractCenter]
    exact hcontract0
  exact Stafford38.Geometry.ActualChartCenterHeight.normalized_center_height_one_of_localized_curve
    (E := E) (R := B) (A := A) (F := F) (C := C) (S := S)
    e p J hcontractCenter.symm hcomap0 htrdeg

end Stafford38.Geometry.ActualResidueCenterHeight
