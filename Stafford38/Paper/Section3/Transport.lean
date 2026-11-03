module

public import Stafford38.Paper.Section3.Monic
public import Stafford38.Weyl.EulerResidue
public import Stafford38.Quotient.EulerSurjectivity

@[expose] public section

/-!
# Remark 3.3 and the ideal `𝓘` and module `Q` of (3.2)

Remark 3.3 transports a solution `1 = d̃R + x₁^N d̃S` for the normal form
`d̃ = c⁻¹Φ_g(d)` back to `d`.  Equation (3.2) defines
`𝓘 = d̃A + x₁^N d̃A` and `Q = A/𝓘`; `Q = 0` is exactly such a solution.
`section_3_reduction` packages the opening paragraph, Proposition 3.2 and
Remark 3.3 for the final assembly.
-/

namespace Stafford38.Paper.Section3

open Stafford
open Stafford38.EulerSurjectivity
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylSymplectic
open Stafford38.Paper.Section2

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- **Equation (3.2), the ideal.** `𝓘 = d̃A_n + x₁^N d̃A_n`, a right ideal. -/
abbrev idealI {n : ℕ} (N : ℕ) (dt : PresentedWeyl k (n + 1)) :
    RightIdeal (PresentedWeyl k (n + 1)) :=
  canonicalRightIdeal (x₁ k n) dt N

/-- **Equation (3.2), the module.** `Q = A_n/𝓘`, a right `A_n`-module. -/
abbrev Q {n : ℕ} (N : ℕ) (dt : PresentedWeyl k (n + 1)) :=
  RightQuotient (idealI k N dt)

/-- `Q = 0` gives `1 ∈ 𝓘`, i.e. `1 = d̃R + x₁^N d̃S` for some `R, S`. -/
theorem exists_eq_of_Q_eq_zero {n N : ℕ} {dt : PresentedWeyl k (n + 1)}
    (hQ : Subsingleton (Q k N dt)) :
    ∃ R S : PresentedWeyl k (n + 1), (1 : PresentedWeyl k (n + 1)) =
      dt * R + x₁ k n ^ N * dt * S := by
  have hmem : (1 : PresentedWeyl k (n + 1)) ∈ idealI k N dt := by
    apply (Submodule.Quotient.mk_eq_zero (idealI k N dt)).mp
    exact Subsingleton.elim _ _
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  refine ⟨a.unop, b.unop, ?_⟩
  rw [← hab]
  rfl

/-- `Φ_g^{-1}(x₁) = Φ_{g^{-1}}(x₁) = ∑_j (g^{-1})_{1j} u_j` is a linear
symplectic coordinate. -/
theorem phiG_symm_x₁_isLinearWeylCoordinate {n : ℕ}
    (g : Matrix.symplecticGroup (Fin (n + 1)) k) :
    Stafford38FixedSourceChallenge.IsLinearWeylCoordinate k n ((phiG k g).symm (x₁ k n)) := by
  obtain ⟨-, -, hsymm⟩ := step_phi_g k g
  obtain ⟨hgen, -, -⟩ := step_phi_g k g⁻¹
  refine ⟨g.1, (g⁻¹).1, SymplecticGroup.mem_iff.mp g.2, SymplecticGroup.mem_iff.mp (g⁻¹).2,
    ?_, ?_, ?_⟩
  · calc g.1 * (g⁻¹).1 = ((g * g⁻¹ : Matrix.symplecticGroup (Fin (n + 1)) k) :
          Matrix _ _ k) := rfl
      _ = 1 := by rw [mul_inv_cancel]; rfl
  · calc (g⁻¹).1 * g.1 = ((g⁻¹ * g : Matrix.symplecticGroup (Fin (n + 1)) k) :
          Matrix _ _ k) := rfl
      _ = 1 := by rw [inv_mul_cancel]; rfl
  · rw [hsymm]
    exact hgen (.inl 0)

/-- **Remark 3.3.** Since `Φ_g` is a ring automorphism and `c` a central unit,
`1 = d̃R + x₁^N d̃S` for `d̃ = c⁻¹Φ_g(d)` transports back to
`1 = d (c⁻¹Φ_g^{-1}(R)) + F d (c⁻¹Φ_g^{-1}(S))` with `F = Φ_g^{-1}(x₁)^N`. -/
theorem remark_3_3 {n N : ℕ} (g : Matrix.symplecticGroup (Fin (n + 1)) k) (c : k)
    (d R S : PresentedWeyl k (n + 1))
    (h : (1 : PresentedWeyl k (n + 1)) =
      (c⁻¹ • phiG k g d) * R + x₁ k n ^ N * (c⁻¹ • phiG k g d) * S) :
    (1 : PresentedWeyl k (n + 1)) =
      d * (c⁻¹ • (phiG k g).symm R) +
        (phiG k g).symm (x₁ k n) ^ N * d * (c⁻¹ • (phiG k g).symm S) := by
  have ht := congrArg (phiG k g).symm h
  rw [map_one] at ht
  rw [ht, map_add, map_mul, map_mul, map_mul, map_pow, map_smul, AlgEquiv.symm_apply_apply,
    smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_mul_assoc, mul_smul_comm]

/-- **Remark 3.3 with (3.2).** If `Q = A/𝓘 = 0` for `d̃ = c⁻¹Φ_g(d)`, then
`1 = dR' + F d S'` with `F = ℓ^N` for the linear symplectic coordinate
`ℓ = Φ_g^{-1}(x₁)`. -/
theorem remark_3_3_of_Q_eq_zero {n N : ℕ} (g : Matrix.symplecticGroup (Fin (n + 1)) k)
    (c : k) (d : PresentedWeyl k (n + 1)) (hQ : Subsingleton (Q k N (c⁻¹ • phiG k g d))) :
    ∃ ell R S : PresentedWeyl k (n + 1),
      Stafford38FixedSourceChallenge.IsLinearWeylCoordinate k n ell ∧
        (1 : PresentedWeyl k (n + 1)) = d * R + ell ^ N * d * S := by
  obtain ⟨R, S, hRS⟩ := exists_eq_of_Q_eq_zero k hQ
  exact ⟨_, _, _, phiG_symm_x₁_isLinearWeylCoordinate k g, remark_3_3 k g c d R S hRS⟩

/-- **Section 3 for the final assembly.**  For `0 ≠ d ∈ A_n(k)`, either
`deg_B d = 0` and `d` is a unit with `1 = dR + FdS` (opening paragraph), or
`N = deg_B d ≥ 1` and Proposition 3.2 gives the normal form `d̃ = c⁻¹Φ_g(d)`
of (3.1) with `deg_B d̃ = N`, for which `Q = A/𝓘 = 0` yields
`1 = dR + ℓ^N dS` with a linear symplectic coordinate `ℓ` (Remark 3.3). -/
theorem section_3_reduction [CharZero k] {n : ℕ} {d : PresentedWeyl k (n + 1)} (hd : d ≠ 0) :
    (bernsteinDegree k d = 0 ∧ Stafford.Reduction.Stafford38 d) ∨
      (1 ≤ bernsteinDegree k d ∧
        ∃ (g : Matrix.symplecticGroup (Fin (n + 1)) k) (c : k), c ≠ 0 ∧
          IsMonicNormalForm k (bernsteinDegree k d) (c⁻¹ • phiG k g d) ∧
          bernsteinDegree k (c⁻¹ • phiG k g d) = bernsteinDegree k d ∧
          (Subsingleton (Q k (bernsteinDegree k d) (c⁻¹ • phiG k g d)) →
            ∃ ell R S : PresentedWeyl k (n + 1),
              Stafford38FixedSourceChallenge.IsLinearWeylCoordinate k n ell ∧
                (1 : PresentedWeyl k (n + 1)) = d * R + ell ^ bernsteinDegree k d * d * S)) := by
  by_cases hN : bernsteinDegree k d = 0
  · obtain ⟨c, -, -, hcert⟩ := step_scalar_case k hd hN
    exact Or.inl ⟨hN, 1, _, 0, hcert⟩
  · obtain ⟨g, c, hc, hform, hdeg⟩ := proposition_3_2 k hd (Nat.one_le_iff_ne_zero.mpr hN)
    exact Or.inr ⟨Nat.one_le_iff_ne_zero.mpr hN, g, c, hc, hform, hdeg,
      remark_3_3_of_Q_eq_zero k g c d⟩

#print axioms remark_3_3
#print axioms remark_3_3_of_Q_eq_zero
#print axioms section_3_reduction

end

end Stafford38.Paper.Section3
