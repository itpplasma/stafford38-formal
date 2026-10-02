import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Stafford38.Geometry.ResidueBasisLocalization

set_option autoImplicit false

namespace Stafford38.Geometry.FieldEquivFiniteType

/-- Finite generation is unchanged when the coefficient algebra is transported
along an isomorphism of coefficient rings. -/
theorem finiteType_of_equiv_base
    {k E₀ E A : Type*} [CommSemiring k] [CommSemiring E₀] [CommSemiring E]
    [CommSemiring A] [Algebra k E₀] [Algebra k E]
    [Algebra E₀ A] [Algebra E A]
    (e : E₀ ≃ₐ[k] E)
    (hcompat : ∀ x : E₀,
      algebraMap E₀ A x = algebraMap E A (e x))
    (hfinite : Algebra.FiniteType E₀ A) : Algebra.FiniteType E A := by
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at hfinite ⊢
  obtain ⟨n, f, hf⟩ := hfinite
  let g : MvPolynomial (Fin n) E →ₐ[E] A := {
    toRingHom := f.toRingHom.comp (MvPolynomial.map e.symm.toRingHom)
    commutes' := by
      intro x
      change f (MvPolynomial.map e.symm.toRingHom
        (algebraMap E (MvPolynomial (Fin n) E) x)) = algebraMap E A x
      rw [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
      change f (algebraMap E₀ (MvPolynomial (Fin n) E₀) (e.symm x)) =
        algebraMap E A x
      rw [f.commutes]
      simpa using hcompat (e.symm x)
  }
  refine ⟨n, g, ?_⟩
  intro a
  obtain ⟨p, hp⟩ := hf a
  obtain ⟨q, hq⟩ := MvPolynomial.map_surjective e.symm.toRingHom e.symm.surjective p
  refine ⟨q, ?_⟩
  change f (MvPolynomial.map e.symm.toRingHom q) = a
  rw [hq, hp]

end Stafford38.Geometry.FieldEquivFiniteType

namespace Stafford38.Geometry.FieldEquivFiniteType

/-- An algebra isomorphic to a domain has the same fraction field after
transporting the canonical map into the fraction field. -/
theorem fractionField_of_equiv_domain
    {k P R : Type*} [CommSemiring k] [CommRing P] [IsDomain P]
    [CommRing R] [IsDomain R] [Algebra k P] [Algebra k R]
    (e : P ≃ₐ[k] R) :
    let E := FractionRing P
    let f : R →+* E := (algebraMap P E).comp e.symm.toRingHom
    letI : Algebra R E := f.toAlgebra
    IsFractionRing R E := by
  let E := FractionRing P
  letI : Field E := FractionRing.field P
  let f : R →+* E := (algebraMap P E).comp e.symm.toRingHom
  letI : Algebra R E := f.toAlgebra
  have hinj : Function.Injective f := by
    intro a b hab
    apply e.symm.injective
    exact IsFractionRing.injective P E (by simpa [f] using hab)
  letI : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).mpr hinj
  apply IsFractionRing.of_field R E
  intro z
  obtain ⟨p, q, hq, hz⟩ := IsFractionRing.div_surjective P z
  refine ⟨e p, e q, ?_⟩
  change z = algebraMap P E (e.symm (e p)) /
    algebraMap P E (e.symm (e q))
  rw [e.symm_apply_apply, e.symm_apply_apply]
  exact hz.symm

end Stafford38.Geometry.FieldEquivFiniteType

namespace Stafford38.Geometry.FieldEquivFiniteType

/-- Transfer the coefficient-localization finite-type theorem to an isomorphic
fraction field, provided both coefficient actions agree along the isomorphism. -/
theorem finiteType_localization_transport
    {k R B E : Type*} [Field k] [CommRing R] [IsDomain R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Algebra.FiniteType k B]
    [CommSemiring E] [Algebra k E] [Algebra E (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)))]
    (e : FractionRing R ≃ₐ[k] E)
    (hcompat : ∀ x : FractionRing R,
      algebraMap (FractionRing R)
        (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) x =
      algebraMap E (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) (e x)) :
    Algebra.FiniteType E
      (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) := by
  letI : Algebra.FiniteType (FractionRing R)
      (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) :=
    Stafford38.Geometry.ResidueBasisLocalization.finiteType_fractionField_localization
      (k := k) (R := R) (A := B)
  exact finiteType_of_equiv_base e hcompat inferInstance

/-- The canonical localization of a domain embeds in its fraction field. -/
theorem localized_domain_isDomain
    {k R B : Type*} [Field k] [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    (hinj : Function.Injective (algebraMap R B)) :
    IsDomain (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) :=
  Stafford38.Geometry.ResidueBasisLocalization.fractionField_localization_isDomain
    (k := k) (R := R) (A := B) hinj

/-- A further localization of a domain with the same fraction field does not
change that fraction field. The returned map is the canonical extension of
`B → F`; every inverted coefficient is nonzero because `R → B` is injective. -/
theorem exists_localized_fractionField_map
    {R B F : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Field F] [Algebra R B] [Algebra B F] [Algebra R F] [IsScalarTower R B F]
    [IsFractionRing B F]
    (hinj : Function.Injective (algebraMap R B)) :
    ∃ f : Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) →+* F,
      letI : Algebra (Localization
        (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) F := f.toAlgebra
      (∀ b : B, f (algebraMap B
        (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) b) =
        algebraMap B F b) ∧
      IsFractionRing (Localization
        (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) F := by
  let S := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  let L := Localization S
  have hS : S ≤ nonZeroDivisors B := by
    change (nonZeroDivisors R).map (algebraMap R B) ≤ nonZeroDivisors B
    rw [Submonoid.map_le_iff_le_comap]
    intro r hr
    apply mem_nonZeroDivisors_of_ne_zero
    intro hzero
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) (hinj (by simpa using hzero))
  have hunit : ∀ s : S, IsUnit (algebraMap B F s.1) := by
    intro s
    have hsB : s.1 ∈ nonZeroDivisors B := hS s.property
    have hsne : s.1 ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero.mp hsB)
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    exact hsne (IsFractionRing.injective B F (by simpa using hzero))
  let f : L →+* F := IsLocalization.lift hunit
  refine ⟨f, ?_⟩
  letI : Algebra L F := f.toAlgebra
  letI : IsScalarTower B L F := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap B F b = f (algebraMap B L b)
    change algebraMap B F b = IsLocalization.lift hunit (algebraMap B L b)
    exact (IsLocalization.lift_eq hunit b).symm
  constructor
  · intro b
    change IsLocalization.lift hunit (algebraMap B L b) = algebraMap B F b
    exact IsLocalization.lift_eq hunit b
  · exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S L F

end Stafford38.Geometry.FieldEquivFiniteType

namespace Stafford38.Geometry.FieldEquivFiniteType

/-- The selected coefficient polynomial fraction field maps canonically to
its normalization localization. The map extends the actual inclusion of each
selected polynomial generator, transported through the chosen algebra
isomorphism `eA`. -/
theorem exists_fractionField_map_to_localization
    {k P R B : Type*} [Field k] [CommRing P] [IsDomain P]
    [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra k P] [Algebra k R] [Algebra k B]
    [Algebra R B] [IsScalarTower k R B]
    (eA : P ≃ₐ[k] R) :
    ∃ fR : FractionRing R →ₐ[R]
      Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)),
    ∃ fE : FractionRing P →ₐ[k]
      Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)),
      (∀ r : R, fR (algebraMap R (FractionRing R) r) =
        algebraMap B (Localization (Algebra.algebraMapSubmonoid B
          (nonZeroDivisors R))) (algebraMap R B r)) ∧
      (∀ p : P, fE (algebraMap P (FractionRing P) p) =
        algebraMap B (Localization (Algebra.algebraMapSubmonoid B
          (nonZeroDivisors R))) (algebraMap R B (eA p))) ∧
      fE = (AlgHom.restrictScalars k fR).comp
        (IsFractionRing.algEquivOfAlgEquiv eA).toAlgHom := by
  let L := Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
  let S := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  let idR : R →ₐ[R] L := IsScalarTower.toAlgHom R R L
  have hunitR : ∀ s : nonZeroDivisors R, IsUnit (idR s.1) := by
    intro s
    let sB : S := ⟨algebraMap R B s.1,
      Submonoid.mem_map.mpr ⟨s.1, s.property, rfl⟩⟩
    have hu : IsUnit (algebraMap B L sB.1) := IsLocalization.map_units L sB
    change IsUnit (algebraMap R L s.1)
    rw [IsScalarTower.algebraMap_apply R B L]
    exact hu
  let fR : FractionRing R →ₐ[R] L :=
    IsLocalization.liftAlgHom (A := R) (M := nonZeroDivisors R)
      (f := idR) hunitR
  let eFrac : FractionRing P ≃ₐ[k] FractionRing R :=
    IsFractionRing.algEquivOfAlgEquiv eA
  let fE : FractionRing P →ₐ[k] L :=
    (AlgHom.restrictScalars k fR).comp eFrac.toAlgHom
  refine ⟨fR, fE, ?_, ?_, rfl⟩
  · intro r
    rw [IsLocalization.liftAlgHom_apply (f := idR) hunitR]
    rw [IsLocalization.lift_eq (g := idR.toRingHom) hunitR r]
    change algebraMap R L r = _
    rw [IsScalarTower.algebraMap_apply R B L]
  · intro p
    change fR (eFrac (algebraMap P (FractionRing P) p)) = _
    rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    rw [IsLocalization.liftAlgHom_apply (f := idR) hunitR]
    rw [IsLocalization.lift_eq (g := idR.toRingHom) hunitR (eA p)]
    change algebraMap R L (eA p) = _
    rw [IsScalarTower.algebraMap_apply R B L]

end Stafford38.Geometry.FieldEquivFiniteType

namespace Stafford38.Geometry.FieldEquivFiniteType

/-- Finite generation of the normalized chart localization over the selected
residue-coordinate fraction field. The returned algebra map is the canonical
extension from the selected polynomial coordinates. -/
theorem exists_finiteType_selected_localization
    {k P R B : Type*} [Field k] [CommRing P] [IsDomain P]
    [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra k P] [Algebra k R] [Algebra k B]
    [Algebra R B] [IsScalarTower k R B]
    [Algebra.FiniteType k B]
    (eA : P ≃ₐ[k] R) :
    ∃ fE : FractionRing P →ₐ[k]
      Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)),
      letI : Algebra (FractionRing P)
        (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) :=
          fE.toRingHom.toAlgebra
      (∀ p : P, fE (algebraMap P (FractionRing P) p) =
        algebraMap B (Localization (Algebra.algebraMapSubmonoid B
          (nonZeroDivisors R))) (algebraMap R B (eA p))) ∧
      Algebra.FiniteType (FractionRing P)
        (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))):= by
  let L := Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
  let eFrac : FractionRing P ≃ₐ[k] FractionRing R :=
    IsFractionRing.algEquivOfAlgEquiv eA
  obtain ⟨fR, fE, hRvar, hvar, hfcomp⟩ :=
    exists_fractionField_map_to_localization (k := k) (P := P) (R := R) (B := B) eA
  letI : Algebra (FractionRing P) L := fE.toRingHom.toAlgebra
  have hRbase (r : R) :
      algebraMap R L r = algebraMap B L (algebraMap R B r) := by
    rw [← fR.commutes]
    exact hRvar r
  have hfRcanon : fR.toRingHom = algebraMap (FractionRing R) L := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors R)
    apply RingHom.ext
    intro r
    change fR (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R) L (algebraMap R (FractionRing R) r)
    calc
      fR (algebraMap R (FractionRing R) r) =
          algebraMap B L (algebraMap R B r) := hRvar r
      _ = algebraMap R L r := (hRbase r).symm
      _ = algebraMap (FractionRing R) L (algebraMap R (FractionRing R) r) :=
        IsScalarTower.algebraMap_apply R (FractionRing R) L r
  have hcompat : ∀ x : FractionRing R,
      algebraMap (FractionRing R) L x =
        algebraMap (FractionRing P) L (eFrac.symm x) := by
    intro x
    change algebraMap (FractionRing R) L x = fE (eFrac.symm x)
    calc
      algebraMap (FractionRing R) L x = fR x := by
        have h := congrArg (fun g : FractionRing R →+* L => g x) hfRcanon
        exact h.symm
      _ = fE (eFrac.symm x) := by
        rw [hfcomp]
        change fR x = fR (eFrac (eFrac.symm x))
        rw [eFrac.apply_symm_apply]
  have hfinite : Algebra.FiniteType (FractionRing P) L :=
    finiteType_localization_transport (k := k) (R := R) (B := B)
      (E := FractionRing P) eFrac.symm hcompat
  exact ⟨fE, hvar, hfinite⟩

/-- Simultaneously package the selected-coordinate algebra structure, finite
generation, domain structure, and unchanged fraction field on the coefficient
localization. The map `fE` is the same canonical map produced above. -/
theorem exists_finiteType_domain_fractionField_localization
    {k P R B F : Type*} [Field k] [CommRing P] [IsDomain P]
    [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Field F]
    [Algebra k P] [Algebra k R] [Algebra k B]
    [Algebra R B] [IsScalarTower k R B]
    [Algebra B F] [Algebra R F] [IsScalarTower R B F]
    [IsFractionRing B F] [Algebra.FiniteType k B]
    (eA : P ≃ₐ[k] R)
    (hinj : Function.Injective (algebraMap R B)) :
    ∃ fE : FractionRing P →ₐ[k]
      Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)),
      letI : Algebra (FractionRing P)
        (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) :=
          fE.toRingHom.toAlgebra
      (∀ p : P, fE (algebraMap P (FractionRing P) p) =
        algebraMap B (Localization (Algebra.algebraMapSubmonoid B
          (nonZeroDivisors R))) (algebraMap R B (eA p))) ∧
      Algebra.FiniteType (FractionRing P)
        (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) ∧
      IsDomain (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) ∧
      (∃ fF : Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) →+* F,
        letI : Algebra (Localization (Algebra.algebraMapSubmonoid B
          (nonZeroDivisors R))) F := fF.toAlgebra
        (∀ b : B, fF (algebraMap B
          (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) b) =
          algebraMap B F b) ∧
        IsFractionRing (Localization (Algebra.algebraMapSubmonoid B
          (nonZeroDivisors R))) F) := by
  obtain ⟨fE, hvar, hfinite⟩ :=
    exists_finiteType_selected_localization (k := k) (P := P) (R := R)
      (B := B) eA
  letI : Algebra (FractionRing P)
      (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))) :=
        fE.toRingHom.toAlgebra
  refine ⟨fE, hvar, hfinite,
    localized_domain_isDomain (k := k) (R := R) (B := B) hinj, ?_⟩
  exact exists_localized_fractionField_map (R := R) (B := B) (F := F) hinj

/-- If a path from the selected fraction field through a coefficient
localization agrees with another field map on the original coefficient
ring, localization uniqueness identifies the field maps and supplies the
corresponding scalar tower. -/
theorem fractionField_map_coherence
    {k P L F : Type*} [Field k] [CommRing P] [IsDomain P]
    [CommRing L] [CommRing F] [Algebra k P]
    [Algebra k (FractionRing P)] [Algebra k L] [Algebra k F]
    (fEA : FractionRing P →ₐ[k] L)
    (fAF : L →+* F)
    (fEF : FractionRing P →ₐ[k] F)
    (hgen : ∀ p : P,
      fAF (fEA (algebraMap P (FractionRing P) p)) =
        fEF (algebraMap P (FractionRing P) p)) :
    letI : Algebra (FractionRing P) L := fEA.toRingHom.toAlgebra
    letI : Algebra L F := fAF.toAlgebra
    letI : Algebra (FractionRing P) F := fEF.toRingHom.toAlgebra
    (fAF.comp fEA.toRingHom = fEF.toRingHom) ∧
      IsScalarTower (FractionRing P) L F := by
  letI : Algebra (FractionRing P) L := fEA.toRingHom.toAlgebra
  letI : Algebra L F := fAF.toAlgebra
  letI : Algebra (FractionRing P) F := fEF.toRingHom.toAlgebra
  have hcomp : fAF.comp fEA.toRingHom = fEF.toRingHom := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors P)
    apply RingHom.ext
    intro p
    exact hgen p
  refine ⟨hcomp, ?_⟩
  exact IsScalarTower.of_algebraMap_eq fun x => by
    change fEF.toRingHom x = fAF (fEA.toRingHom x)
    have hx := congrArg (fun g : FractionRing P →+* F => g x) hcomp
    simpa only [RingHom.comp_apply] using hx.symm

end Stafford38.Geometry.FieldEquivFiniteType
