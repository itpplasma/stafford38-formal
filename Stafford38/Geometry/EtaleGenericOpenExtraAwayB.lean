module
public import Stafford38.Geometry.EtaleGenericOpenLocalAwayB

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Stafford38.Geometry.EtaleGenericOpenTransport
universe u v

/-- Localize the common generic open at the image of a chart denominator.
The denominator is mapped through the actual `B`-algebra structure. -/
abbrev genericOpenExtraAwayB
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (g : Q) : Type u :=
  Localization.Away
    (genericOpenBMap M f e (algebraMap Q B g))

abbrev pointLocalExtraAwayB
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q) (g : Q) : Type v :=
  Localization.Away
    (algebraMap B (pointLocalAwayOpen M f) (algebraMap Q B g))

noncomputable def genericOpenExtraAwayBMap
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (g : Q) :
    B →+* genericOpenExtraAwayB M f e g :=
  (algebraMap (genericOpenRing M f e) (genericOpenExtraAwayB M f e g)).comp
    (genericOpenBMap M f e)

noncomputable instance instGenericOpenExtraAwayBAlgebra
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (g : Q) :
    Algebra B (genericOpenExtraAwayB M f e g) :=
  Algebra.compHom (genericOpenExtraAwayB M f e g) (genericOpenBMap M f e)

/-- Formal étaleness is transported first from the actual local ring `B_M`
to the common open, then through the extra localization. -/
theorem formallyEtale_genericOpenExtraAway_of_pointLocal
    {R : Type*} [CommRing R]
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    [Algebra R B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (g : Q)
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    let Cq := genericOpenRing M f e
    let C := Localization.Away (genericOpenBMap M f e (algebraMap Q B g))
    letI : Algebra R Cq :=
      ((algebraMap B (genericOpenRing M f e)).comp (algebraMap R B)).toAlgebra
    letI : Algebra R C := Algebra.compHom C (algebraMap R Cq)
    Algebra.FormallyEtale R C := by
  dsimp
  let Cq := genericOpenRing M f e
  let C := Localization.Away (genericOpenBMap M f e (algebraMap Q B g))
  letI : Algebra R Cq :=
    ((algebraMap B Cq).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B Cq := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra R C := Algebra.compHom C (algebraMap R Cq)
  letI : Algebra Cq C := inferInstance
  letI : SMul Cq C := (inferInstance : Algebra Cq C).toSMul
  letI : SMul R C := (Algebra.compHom C (algebraMap R Cq)).toSMul
  letI : IsScalarTower R Cq C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra.FormallyEtale Cq C :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (genericOpenBMap M f e (algebraMap Q B g)))
  letI : Algebra.FormallyEtale R Cq :=
    formallyEtale_genericOpenRing_of_pointLocal M f e
  exact Algebra.FormallyEtale.comp R Cq C

def genericArcToGenericOpenExtraAwayB
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    {L : Type*} [Field L]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f))
    (ρ : B →+* L)
    (hf : IsUnit (ρ (algebraMap Q B f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b)) (g : Q)
    (hg : IsUnit (ρ (algebraMap Q B g))) :
    genericOpenExtraAwayB M f e g →+* L := by
  let ψ := genericArcToGenericOpen M f e ρ hf hunitM
  have hval : ψ (genericOpenBMap M f e (algebraMap Q B g)) =
      ρ (algebraMap Q B g) := by
    exact genericArcToGenericOpen_apply M f e ρ hf hunitM (algebraMap Q B g)
  have hψ : IsUnit
      (ψ (genericOpenBMap M f e (algebraMap Q B g))) := by
    rw [hval]
    exact hg
  exact Localization.awayLift ψ
    (genericOpenBMap M f e (algebraMap Q B g)) hψ

/-- The chart-denominator localization of the common open agrees, as a
`B`-algebra, with the same localization of the point-local presentation. -/
noncomputable def genericOpenExtraAwayEquiv_pointLocalAwayB
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (g : Q) :
    genericOpenExtraAwayB M f e g ≃ₐ[B] pointLocalExtraAwayB M f g := by
  let Cq := genericOpenRing M f e
  let Cl := pointLocalAwayOpen M f
  let b := algebraMap Q B g
  let eB : Cq ≃ₐ[B] Cl := genericOpenEquiv_pointLocalAway_overB M f e
  let N : Submonoid Cq := Submonoid.powers (genericOpenBMap M f e b)
  let T : Submonoid Cl := Submonoid.powers (algebraMap B Cl b)
  let C : Type u := Localization.Away
    (genericOpenBMap M f e (algebraMap Q B g))
  letI : SMul B C := (Algebra.compHom C (genericOpenBMap M f e)).toSMul
  have hTower : IsScalarTower B Cq (genericOpenExtraAwayB M f e g) := by
    change IsScalarTower B Cq C
    exact ⟨fun b' c x => by
      change (b' • c) • x = genericOpenBMap M f e b' • (c • x)
      rw [Algebra.smul_def]
      exact mul_smul _ _ _⟩
  letI : IsScalarTower B Cq (genericOpenExtraAwayB M f e g) := hTower
  have hmap : Submonoid.map eB.toMonoidHom N = T := by
    rw [Submonoid.map_powers]
    change Submonoid.powers (eB (algebraMap B Cq b)) = _
    rw [eB.commutes b]
  exact IsLocalization.algEquivOfAlgEquiv
    (A := B) (R := Cq) (M := N) (genericOpenExtraAwayB M f e g)
    (P := Cl) (T := T) (pointLocalExtraAwayB M f g) eB hmap

end Stafford38.Geometry.EtaleGenericOpenTransport
end
