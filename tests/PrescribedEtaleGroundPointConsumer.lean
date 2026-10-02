import Stafford38.Geometry.PrescribedEtaleGroundPoint

set_option autoImplicit false

namespace Stafford38.Geometry.PrescribedEtaleGroundPointConsumer

/-- On the identity polynomial chart, point selection over the maximal zero
point returns that same point: X vanishes there and X-1 does not. -/
theorem polynomial_zero_point_oracle
    {k : Type*} [Field k] [IsAlgClosed k] :
    ∃ (M : Ideal (Polynomial k)) (hM : M.IsMaximal),
      (letI : M.IsMaximal := hM
       Algebra.FormallyEtale (Polynomial k) (Localization.AtPrime M)) ∧
      Polynomial.X ∈ M ∧ Polynomial.X - (1 : Polynomial k) ∉ M := by
  let ρ : Polynomial k →ₐ[k] k := Polynomial.aeval (0 : k)
  let p : Ideal (Polynomial k) := RingHom.ker ρ
  have hp : p.IsMaximal := RingHom.ker_isMaximal_of_surjective ρ.toRingHom (by
    intro c
    exact ⟨Polynomial.C c, by simp [ρ]⟩)
  let : p.IsMaximal := hp
  have hEt : Algebra.FormallyEtale (Polynomial k) (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have hgp : Polynomial.X - (1 : Polynomial k) ∉ p := by
    intro hm
    have hz := RingHom.mem_ker.mp hm
    change ρ (Polynomial.X - 1) = 0 at hz
    simp [ρ] at hz
  obtain ⟨f, M, hM, _, hpM, _, hgM, _, _, hlocal⟩ :=
    PrescribedEtaleGroundPoint.exists_standardEtale_neighborhood_and_formallyEtale_ground_point_avoiding
      (k := k) (R := Polynomial k) (B := Polynomial k) p
      (Polynomial.X - 1) hgp hEt
  have hMp : M = p := (hp.eq_of_le hM.ne_top hpM).symm
  refine ⟨M, hM, hlocal, ?_, ?_⟩
  · rw [hMp]
    change ρ Polynomial.X = 0
    simp [ρ]
  · exact hgM

end Stafford38.Geometry.PrescribedEtaleGroundPointConsumer

#print axioms Stafford38.Geometry.PrescribedEtaleGroundPointConsumer.polynomial_zero_point_oracle

#print axioms Stafford38.Geometry.PrescribedEtaleGroundPoint.formallyEtale_atPrime_of_away
#print axioms Stafford38.Geometry.PrescribedEtaleGroundPoint.exists_standardEtale_neighborhood_and_formallyEtale_ground_point

#print axioms Stafford38.Geometry.PrescribedEtaleGroundPoint.exists_standardEtale_neighborhood_and_formallyEtale_ground_point_avoiding
