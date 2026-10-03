module
public import Stafford38.Geometry.GeneralConormalAxis

@[expose] public section
set_option autoImplicit false
universe u
open Stafford38.Geometry.GeneralConormalAxis
#check exists_groundConormalAxis_of_minimalPrime_unit_transcendental
#print axioms exists_groundConormalAxis_of_minimalPrime_unit_transcendental
theorem paper_actual_axis_literal_consumer {k : Type u} [Field k] [CharZero k] {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hP : P.asIdeal ∈ I.minimalPrimes)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k (Stafford38.Geometry.AffineComponentCoordinateSplit.componentCoordinate P ⟨0, hm⟩)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (y : Fin m → LaurentSeries K) (xi : Fin m → PowerSeries K),
      Sum.elim y (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        Stafford38.Geometry.LaurentConormalResidueExtension.groundEquationConormalLocus
          (k := k) (K := K) I ∧
      Stafford38.GeometryRetractionSpecialization.residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  exact exists_groundConormalAxis_of_minimalPrime_unit_transcendental hm I hI P hP hunit htrans

#print axioms paper_actual_axis_literal_consumer
