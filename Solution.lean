module
public import Stafford38.ChallengeDefinitions
public import Stafford38.PaperClaimDefinitions
public import Stafford38.ChallengeBridge
public import Stafford38.Paper.Main
public import Stafford38.Paper.Section7

@[expose] public section

/-!
# Solution: the proof along the paper

The compared theorems are proved by the paper-route declarations
`Stafford38.Paper.theorem_1_1`, `Stafford38.Paper.theorem_1_1_fixedSource`,
`Stafford38.Paper.corollary_6_3` and `Stafford38.Paper.corollary_6_3_stablyCyclic`
(Sections 3–6, `Stafford38/Paper/Main.lean`), and by the Section 7
consequences in `Stafford38/Paper/Section7.lean`, which use
`Stafford38.Paper.theorem_1_1` wherever they need Theorem 1.1.
`Stafford38.ChallengeBridge` turns the identity and fixed-source forms into the
printed statement of Theorem 1.1 (`A_n = dA_n + FdA_n`, `F = Φ_g^{-1}(x₁)^{deg_B d}`).
-/

namespace Stafford38Challenge

universe u

theorem universalStatement : UniversalStatement :=
  Stafford38.Paper.theorem_1_1

theorem theorem_1_1 : PaperTheorem_1_1 :=
  paperTheorem_1_1_of Stafford38.Paper.theorem_1_1 Stafford38.Paper.theorem_1_1_fixedSource

theorem corollary_6_3 : PaperCorollary_6_3 := by
  intro k _ _ n M _ _ _ hM
  exact Stafford38.Paper.corollary_6_3 k n M hM

theorem corollary_6_3_stablyCyclic : PaperCorollary_6_3_stablyCyclic := by
  intro k _ _ n M _ _ _ hM
  exact Stafford38.Paper.corollary_6_3_stablyCyclic k n M hM

theorem leftHandedIdentity : LeftHandedIdentity :=
  Stafford38.Paper.Section7.leftHandedIdentity

theorem corollary_6_3_left : LeftCorollary_6_3 :=
  Stafford38.Paper.Section7.corollary_6_3_left

theorem localizedDifferentialIdentity : LocalizedDifferentialIdentity :=
  Stafford38.Paper.Section7.localizedDifferentialIdentity

theorem principalOpenDifferentialIdentity :
    ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (f : MvPolynomial (Fin n) k),
      HasDifferentialIdentity k (Localization.Away f) := by
  intro k _ _ n f
  exact localizedDifferentialIdentity k n (Submonoid.powers f) (Localization.Away f)

theorem laurentDifferentialIdentity :
    ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ),
      HasDifferentialIdentity k
        (Localization.Away (∏ i, MvPolynomial.X i : MvPolynomial (Fin n) k)) := by
  intro k _ _ n
  exact principalOpenDifferentialIdentity k n _

theorem fractionFieldDifferentialIdentity :
    ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ),
      HasDifferentialIdentity k (FractionRing (MvPolynomial (Fin n) k)) := by
  intro k _ _ n
  exact localizedDifferentialIdentity k n (nonZeroDivisors _) (FractionRing _)

theorem evolutionaryIdentity : EvolutionaryIdentity :=
  Stafford38.Paper.Section7.evolutionaryIdentity

end Stafford38Challenge

#print axioms Stafford38Challenge.universalStatement
#print axioms Stafford38Challenge.theorem_1_1
#print axioms Stafford38Challenge.corollary_6_3
#print axioms Stafford38Challenge.corollary_6_3_stablyCyclic
#print axioms Stafford38Challenge.leftHandedIdentity
#print axioms Stafford38Challenge.corollary_6_3_left
#print axioms Stafford38Challenge.localizedDifferentialIdentity
#print axioms Stafford38Challenge.principalOpenDifferentialIdentity
#print axioms Stafford38Challenge.laurentDifferentialIdentity
#print axioms Stafford38Challenge.fractionFieldDifferentialIdentity
#print axioms Stafford38Challenge.evolutionaryIdentity
