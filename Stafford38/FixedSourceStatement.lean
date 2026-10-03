import Stafford38.MathlibCompat.MvPolynomialCoeff
import Stafford38.UniversalAssembly
import Stafford38.ChallengeDefinitions

namespace Stafford38.FixedSource

open Stafford38
open Stafford38.WeylFiltration
open Stafford38.Characteristic
open Stafford38.WeylPBW
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylSymplectic
open Stafford38.WeylLeadingSymbol
open Stafford

noncomputable section
universe u

/-! The (actual) Bernstein degree, read directly from checked PBW normal form. -/
def bernsteinDegree (k : Type u) [Field k] {n : ℕ}
    (d : PresentedWeyl k n) : ℕ :=
  MvPolynomial.weightedTotalDegree (@bernsteinWeight n)
    (presentedNormalFormLinearEquiv k n d)

abbrev IsLinearWeylCoordinate (k : Type u) [Field k] (n : ℕ)
    (ell : PresentedWeyl k (n + 1)) : Prop :=
  Stafford38FixedSourceChallenge.IsLinearWeylCoordinate k n ell

/-- The exact fixed-source strengthening: the source exponent is the actual
Bernstein degree of the input operator, and the source coordinate is obtained
from an invertible linear symplectic change of Weyl generators. -/
abbrev UniversalFixedSourceStatement : Prop :=
  Stafford38FixedSourceChallenge.UniversalFixedSourceStatementWithDegree
    (fun (k : Type u) [Field k] {n : ℕ} (d : PresentedWeyl k n) =>
      bernsteinDegree k d)

theorem bernsteinDegree_eq_of_piece_of_principal_ne_zero
    (k : Type u) [Field k] {n N : ℕ} {d : PresentedWeyl k n}
    (hp : d ∈ bernsteinPiece k n N)
    (hP : presentedPrincipalComponent k (@bernsteinWeight n) N d ≠ 0) :
    bernsteinDegree k d = N := by
  let f := presentedNormalFormLinearEquiv k n d
  have hle : bernsteinDegree k d ≤ N := by
    apply Finset.sup_le
    intro m hm
    exact (hp m (MvPolynomial.mem_support_iff.mp hm))
  rcases MvPolynomial.support_nonempty.mpr hP with ⟨m, hm⟩
  have hm : MvPolynomial.coeff m
      (presentedPrincipalComponent k (@bernsteinWeight n) N d) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  change AddMonoidAlgebra.coeff
    (presentedPrincipalComponent k (@bernsteinWeight n) N d) m ≠ 0 at hm
  have hcoeff := hm
  change AddMonoidAlgebra.coeff
    (presentedPrincipalComponent k (@bernsteinWeight n) N d) m ≠ 0 at hcoeff
  rw [coeff_presentedPrincipalComponent] at hcoeff
  have hweight : monomialWeight (@bernsteinWeight n) m = N := by
    by_contra hne
    have hz : AddMonoidAlgebra.coeff
        (presentedPrincipalComponent k (@bernsteinWeight n) N d) m = 0 := by
      rw [coeff_presentedPrincipalComponent]
      simp [hne]
    exact hm hz
  have hfd : MvPolynomial.coeff m f ≠ 0 := by
    rw [if_pos hweight] at hcoeff
    simpa [f] using hcoeff
  have hge : N ≤ bernsteinDegree k d := by
    calc
      N = monomialWeight (@bernsteinWeight n) m := hweight.symm
      _ ≤ bernsteinDegree k d :=
        MvPolynomial.le_weightedTotalDegree _ (MvPolynomial.mem_support_iff.mpr hfd)
  exact Nat.le_antisymm hle hge

end
end Stafford38.FixedSource
