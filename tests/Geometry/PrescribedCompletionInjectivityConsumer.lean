module
public import Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

@[expose] public section

set_option autoImplicit false

namespace PrescribedCompletionInjectivityConsumer
open Stafford38.Geometry.PrescribedGroundPointUnitPowerChart

variable {k B : Type*} {d : ℕ} [Field k] [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial (Option (Fin d)) k) B]
  [IsScalarTower k (MvPolynomial (Option (Fin d)) k) B]
  [Algebra.EssFiniteType (MvPolynomial (Option (Fin d)) k) B]

/-- A domain's nonzero element stays nonzero even when its residue vanishes. -/
theorem source_nonzero
    [IsDomain B] (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) (Localization.AtPrime M)]
    (b : B) (hb : b ≠ 0) :
    localToFinSuccPowerSeries (k := k) (d := d) M eM
      (algebraMap B (Localization.AtPrime M) b) ≠ 0 :=
  localToFinSuccPowerSeries_algebraMap_ne_zero M eM b hb

/-- Independent coordinate oracle: the actual parameter image has coefficient
one in its linear coordinate, regardless of its closed-point constant. -/
theorem parameter_linear_coefficient
    (M : Ideal B) [M.IsMaximal] (eM : (B ⧸ M) ≃ₐ[k] k)
    [Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) (Localization.AtPrime M)] :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin (d + 1)) 1)
      (localToFinSuccPowerSeries (k := k) (d := d) M eM
        (algebraMap B (Localization.AtPrime M)
          (algebraMap (MvPolynomial (Option (Fin d)) k) B (MvPolynomial.X none)))) = 1 := by
  classical
  have hdegree : Finsupp.single (0 : Fin (d + 1)) (1 : ℕ) ≠ 0 := by
    intro hz
    have h := congrArg (fun f : Fin (d + 1) →₀ ℕ => f 0) hz
    simpa using h
  rw [localToFinSuccPowerSeries_none]
  simp [MvPowerSeries.coeff_C, hdegree]

#print axioms source_nonzero
#print axioms parameter_linear_coefficient
end PrescribedCompletionInjectivityConsumer
