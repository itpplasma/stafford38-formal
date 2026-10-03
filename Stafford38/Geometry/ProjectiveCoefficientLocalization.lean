module
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Etale.Basic

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Stafford38.Geometry.ProjectiveCoefficientLocalization

universe u v w

variable {k : Type u} [CommRing k]

/-- Generic coefficient-to-polynomial localization with an arbitrary set of coefficient
variables. The `none` coordinate is the distinguished polynomial variable; `some i` are the
coefficient variables. -/
abbrev OptionSource (σ : Type w) := MvPolynomial (Option σ) k

abbrev OptionCoeff (σ : Type w) := MvPolynomial σ k

variable {E : Type v} [CommRing E] {σ : Type w}
  [Algebra (OptionCoeff (k := k) σ) E] [Algebra k E]
  [IsScalarTower k (OptionCoeff (k := k) σ) E]

/-- The coordinate-preserving map `k[a,zᵢ] → E[a]`, with the distinguished parameter indexed by
`none` and the selected coefficient variables indexed by `some i`. -/
def optionCoordinateMap : OptionSource (k := k) σ →ₐ[k] Polynomial E :=
  (Polynomial.mapAlgHom (IsScalarTower.toAlgHom k (OptionCoeff (k := k) σ) E)).comp
    (MvPolynomial.optionEquivLeft k σ).toAlgHom

@[simp] theorem optionCoordinateMap_X_none :
    optionCoordinateMap (k := k) (E := E) (σ := σ) (MvPolynomial.X none) =
      (Polynomial.X : Polynomial E) := by
  simp [optionCoordinateMap]

@[simp] theorem optionCoordinateMap_X_some (i : σ) :
    optionCoordinateMap (k := k) (E := E) (σ := σ) (MvPolynomial.X (some i)) =
      Polynomial.C (algebraMap (OptionCoeff (k := k) σ) E (MvPolynomial.X i)) := by
  simp [optionCoordinateMap]

/-- Invert exactly the non-zero-divisor coefficient polynomials, and no power of the distinguished
variable. -/
def optionCoordinateDenominators : Submonoid (OptionSource (k := k) σ) :=
  Submonoid.comap (MvPolynomial.optionEquivLeft k σ).toRingHom
    (Submonoid.map Polynomial.C (nonZeroDivisors (OptionCoeff (k := k) σ)))

variable [IsLocalization (nonZeroDivisors (OptionCoeff (k := k) σ)) E]

/-- The generic option-indexed coordinate map is localization at the coefficient polynomials. -/
theorem optionCoordinateMap_isLocalization :
    letI : Algebra (OptionSource (k := k) σ) (Polynomial E) :=
      (optionCoordinateMap (k := k) (E := E) (σ := σ)).toRingHom.toAlgebra
    IsLocalization (optionCoordinateDenominators (k := k) (σ := σ)) (Polynomial E) := by
  letI : Algebra (OptionSource (k := k) σ) (Polynomial E) :=
    (optionCoordinateMap (k := k) (E := E) (σ := σ)).toRingHom.toAlgebra
  let A := OptionCoeff (k := k) σ
  let M₀ : Submonoid A := nonZeroDivisors A
  let M₁ : Submonoid (Polynomial A) := Submonoid.map Polynomial.C M₀
  let e : OptionSource (k := k) σ ≃ₐ[k] Polynomial A := MvPolynomial.optionEquivLeft k σ
  let N : Submonoid (OptionSource (k := k) σ) := Submonoid.comap e.toRingHom M₁
  have hN : N = optionCoordinateDenominators (k := k) (σ := σ) := rfl
  letI : Algebra (Polynomial A) (Polynomial E) := Polynomial.algebra A E
  have hcoord (x : OptionSource (k := k) σ) :
      optionCoordinateMap (k := k) (E := E) (σ := σ) x =
        algebraMap (Polynomial A) (Polynomial E) (e x) := rfl
  have hloc : IsLocalization M₁ (Polynomial E) := by
    dsimp [M₁, M₀]
    exact Polynomial.isLocalization (nonZeroDivisors A) E
  rw [← hN, isLocalization_iff]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx⟩
    change IsUnit ((optionCoordinateMap (k := k) (E := E) (σ := σ)).toRingHom x)
    have hx' : e x ∈ M₁ := hx
    change IsUnit (algebraMap (Polynomial A) (Polynomial E) (e x))
    exact IsLocalization.map_units (Polynomial E) ⟨e x, hx'⟩
  · intro z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (M := M₁) z
    refine ⟨⟨e.symm a, ⟨e.symm b, ?_⟩⟩, ?_⟩
    · change e (e.symm b) ∈ M₁
      simpa only [e.apply_symm_apply] using b.property
    · change z * optionCoordinateMap (k := k) (E := E) (σ := σ) (e.symm b) =
        optionCoordinateMap (k := k) (E := E) (σ := σ) (e.symm a)
      rw [hcoord, e.apply_symm_apply, hcoord, e.apply_symm_apply]
      exact hab
  · intro x y hxy
    have hxy' : algebraMap (Polynomial A) (Polynomial E) (e x) =
        algebraMap (Polynomial A) (Polynomial E) (e y) := hxy
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M₁) hxy'
    refine ⟨⟨e.symm c, ?_⟩, ?_⟩
    · change e (e.symm c) ∈ M₁
      simpa only [e.apply_symm_apply] using c.property
    · apply e.injective
      simpa using hc

/-- The generic option-indexed map is formally étale because it is a localization. -/
theorem optionCoordinateMap_formallyEtale :
    letI : Algebra (OptionSource (k := k) σ) (Polynomial E) :=
      (optionCoordinateMap (k := k) (E := E) (σ := σ)).toRingHom.toAlgebra
    Algebra.FormallyEtale (OptionSource (k := k) σ) (Polynomial E) := by
  letI : Algebra (OptionSource (k := k) σ) (Polynomial E) :=
    (optionCoordinateMap (k := k) (E := E) (σ := σ)).toRingHom.toAlgebra
  letI : IsLocalization (optionCoordinateDenominators (k := k) (σ := σ)) (Polynomial E) :=
    optionCoordinateMap_isLocalization (k := k) (E := E) (σ := σ)
  exact Algebra.FormallyEtale.of_isLocalization (optionCoordinateDenominators (k := k) (σ := σ))

abbrev Coeff (k : Type u) [CommRing k] (d : ℕ) := MvPolynomial (Fin d) k

abbrev Source (k : Type u) [CommRing k] (d : ℕ) := MvPolynomial (Fin (d + 1)) k

variable (d : ℕ)

variable {E : Type v} [CommRing E] [Algebra (Coeff (k := k) d) E] [Algebra k E]
  [IsScalarTower k (Coeff (k := k) d) E]

/-- Reindex the legacy `Fin (d+1)` presentation as `Option (Fin d)`, with zero sent to `none`. -/
def finToOptionEquiv : Source (k := k) d ≃ₐ[k] OptionSource (k := k) (Fin d) :=
  MvPolynomial.renameEquiv k (_root_.finSuccEquiv d)

/-- The original finite-coordinate map is the generic option-indexed map transported along
`Fin (d+1) ≃ Option (Fin d)`. -/
def coordinateMap : Source (k := k) d →ₐ[k] Polynomial E :=
  (optionCoordinateMap (k := k) (E := E) (σ := Fin d)).comp
    (finToOptionEquiv (k := k) d).toAlgHom

@[simp] theorem coordinateMap_zero :
    coordinateMap (k := k) d (MvPolynomial.X (0 : Fin (d + 1))) =
      (Polynomial.X : Polynomial E) := by
  simp [coordinateMap, finToOptionEquiv]

@[simp] theorem coordinateMap_succ (i : Fin d) :
    coordinateMap (k := k) d (MvPolynomial.X i.succ) =
      Polynomial.C (algebraMap (Coeff k d) E (MvPolynomial.X i)) := by
  simp [coordinateMap, finToOptionEquiv]

/-- The legacy denominator set is the pullback of the canonical option-indexed denominator set.
Thus it still inverts exactly coefficient polynomials and never the distinguished variable. -/
def coordinateDenominators : Submonoid (Source (k := k) d) :=
  Submonoid.comap (finToOptionEquiv (k := k) d).toRingHom
    (optionCoordinateDenominators (k := k) (σ := Fin d))

theorem coordinateDenominators_eq_finSucc :
    coordinateDenominators (k := k) d =
      Submonoid.comap (MvPolynomial.finSuccEquiv k d).toRingHom
        (Submonoid.map Polynomial.C (nonZeroDivisors (Coeff k d))) := by
  ext p
  rfl

variable [IsLocalization (nonZeroDivisors (Coeff k d)) E]

/-- The legacy finite-index localization theorem is transported from the single generic producer. -/
theorem coordinateMap_isLocalization :
    letI : Algebra (Source k d) (Polynomial E) :=
      (coordinateMap (k := k) d).toRingHom.toAlgebra
    IsLocalization (coordinateDenominators (k := k) d) (Polynomial E) := by
  letI : Algebra (Source k d) (Polynomial E) :=
    (coordinateMap (k := k) d).toRingHom.toAlgebra
  let e := finToOptionEquiv (k := k) d
  letI : Algebra (OptionSource (k := k) (Fin d)) (Polynomial E) :=
    (optionCoordinateMap (k := k) (E := E) (σ := Fin d)).toRingHom.toAlgebra
  have hden :
      (coordinateDenominators (k := k) d).map e.toRingEquiv =
        optionCoordinateDenominators (k := k) (σ := Fin d) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e y ∈ optionCoordinateDenominators (k := k) (σ := Fin d) at hy
      exact hy
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change e (e.symm x) ∈ optionCoordinateDenominators (k := k) (σ := Fin d)
      simpa using hx
  have hlocOption :
      IsLocalization (optionCoordinateDenominators (k := k) (σ := Fin d)) (Polynomial E) := by
    exact optionCoordinateMap_isLocalization (k := k) (E := E) (σ := Fin d)
  exact IsLocalization.of_ringEquiv_left e.toRingEquiv hden (by
    intro x
    change coordinateMap (k := k) d x =
      optionCoordinateMap (k := k) (E := E) (σ := Fin d) (e x)
    rfl)

/-- The legacy finite-index formally-etale result is now just a consequence of its localization
wrapper. -/
theorem coordinateMap_formallyEtale :
    letI : Algebra (Source k d) (Polynomial E) :=
      (coordinateMap (k := k) d).toRingHom.toAlgebra
    Algebra.FormallyEtale (Source k d) (Polynomial E) := by
  letI : Algebra (Source k d) (Polynomial E) :=
    (coordinateMap (k := k) d).toRingHom.toAlgebra
  letI : IsLocalization (coordinateDenominators (k := k) d) (Polynomial E) :=
    coordinateMap_isLocalization (k := k) d
  exact Algebra.FormallyEtale.of_isLocalization (coordinateDenominators (k := k) d)

section FractionField

variable {k : Type u} [Field k] (d : ℕ)

/-- The distinguished-variable chart over the canonical coefficient fraction field is a
localization at the coefficient polynomials. -/
theorem fractionCoordinateMap_isLocalization :
    letI : Algebra (Source k d)
      (Polynomial (FractionRing (Coeff k d))) :=
      (coordinateMap (k := k) d).toRingHom.toAlgebra
    IsLocalization (coordinateDenominators (k := k) d)
      (Polynomial (FractionRing (Coeff k d))) := by
  exact coordinateMap_isLocalization (k := k) d

/-- Consequently the canonical finite-index coefficient chart is formally étale. -/
theorem fractionCoordinateMap_formallyEtale :
    letI : Algebra (Source k d)
      (Polynomial (FractionRing (Coeff k d))) :=
      (coordinateMap (k := k) d).toRingHom.toAlgebra
    Algebra.FormallyEtale (Source k d)
      (Polynomial (FractionRing (Coeff k d))) := by
  exact coordinateMap_formallyEtale (k := k) d

end FractionField

end Stafford38.Geometry.ProjectiveCoefficientLocalization
