module
public import Stafford38.Geometry.TiltedArcAvoidance

@[expose] public section

set_option autoImplicit false

open MvPolynomial

namespace Stafford38.Geometry.TiltedArcAvoidanceConsumer

open Stafford38.Geometry.TiltedArcAvoidance

-- A literal two-variable oracle: for f(t,z) = t + z, the zero tilt z = 0
-- returns t, whose t-coefficient is 1.
theorem zero_tilt_coefficient_one_oracle :
    MvPowerSeries.subst
      (fun i : Fin 2 =>
        MvPowerSeries.C ((Fin.cons (1 : ℚ) (fun _ : Fin 1 => (0 : ℚ)) : Fin 2 → ℚ) i) *
          MvPowerSeries.X (PUnit.unit : PUnit))
      ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) :
          MvPowerSeries (Fin 2) ℚ)) ≠ 0 := by
  let a : Fin 2 → MvPowerSeries PUnit ℚ := fun i =>
    MvPowerSeries.C ((Fin.cons (1 : ℚ) (fun _ : Fin 1 => (0 : ℚ)) : Fin 2 → ℚ) i) *
      MvPowerSeries.X (PUnit.unit : PUnit)
  have ha : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; simp [a])
  have hval : MvPowerSeries.subst a
      (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) :
        MvPowerSeries (Fin 2) ℚ) =
      MvPowerSeries.X (PUnit.unit : PUnit) := by
    rw [MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]
    simp [a]
  rw [hval]
  intro hzero
  have hc := congrArg (fun g : MvPowerSeries PUnit ℚ =>
    MvPowerSeries.coeff (Finsupp.single PUnit.unit 1) g) hzero
  norm_num [MvPowerSeries.coeff_X] at hc

#print axioms zero_tilt_coefficient_one_oracle
#print axioms Stafford38.Geometry.TiltedArcAvoidance.exists_eval_ne_zero
#print axioms Stafford38.Geometry.TiltedArcAvoidance.exists_eval_ne_zero_first_one
#print axioms Stafford38.Geometry.TiltedArcAvoidance.exists_tilt_subst_ne_zero

end Stafford38.Geometry.TiltedArcAvoidanceConsumer
