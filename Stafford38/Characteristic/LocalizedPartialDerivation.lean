module
public import Stafford38.Characteristic.PostScalarExtensionPoisson
public import Stafford38.Characteristic.LocalizedDerivationQuotient

@[expose] public section

/-!
# Polynomial partial derivatives on a prime localization

The partial derivative on the symbol ring is extended by the generic
localization operation from AlgebraicAnalysis.  The quotient-rule formula
used by the localization argument is recorded below as a proved
specialization of the generic Leibniz/inverse formula.
-/

namespace Stafford38.Characteristic.LocalizedPartialDerivation

open Stafford38.Characteristic
open Stafford38.Characteristic.PostScalarExtensionPoisson
open AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

abbrev R := SymbolRing k n

abbrev AtPrime (P : Ideal (R (k := k) (n := n))) [P.IsPrime] :=
  Localization P.primeCompl

/-- The `i`th polynomial partial derivative, extended through the localization
at `P`.  This is the generic AlgebraicAnalysis extension specialized to the
phase-space partial derivative. -/
noncomputable def localizedPDeriv
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime] (i : PhaseVar n) :
    Derivation k (AtPrime (k := k) (n := n) P) (AtPrime P) :=
  extendDerivation k (R (k := k) (n := n)) (AtPrime P) P.primeCompl
    ((Algebra.linearMap (R (k := k) (n := n)) (AtPrime P)).compDer
      (MvPolynomial.pderiv i))

theorem localizedPDeriv_compAlgebraMap
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime] (i : PhaseVar n) :
    (localizedPDeriv (k := k) (n := n) P i).compAlgebraMap (R (k := k) (n := n)) =
      (Algebra.linearMap (R (k := k) (n := n)) (AtPrime P)).compDer
        (MvPolynomial.pderiv i) := by
  change (extendDerivation k (R (k := k) (n := n)) (AtPrime P)
    P.primeCompl ((Algebra.linearMap (R (k := k) (n := n)) (AtPrime P)).compDer
      (MvPolynomial.pderiv i))).compAlgebraMap (R (k := k) (n := n)) = _
  exact extendDerivation_compAlgebraMap k (R (k := k) (n := n)) (AtPrime P)
    P.primeCompl ((Algebra.linearMap (R (k := k) (n := n)) (AtPrime P)).compDer
      (MvPolynomial.pderiv i))

/-- Exact quotient-rule formula for the canonical localization extension.
The denominator square is a localization unit, and the formula follows by
specializing the generic cross-multiplied Leibniz rule. -/
theorem localizedPDeriv_mk
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (i : PhaseVar n) (a : R) (s : P.primeCompl) :
    extendDerivation k (R (k := k) (n := n)) (AtPrime P) P.primeCompl
      ((Algebra.linearMap (R (k := k) (n := n)) (AtPrime P)).compDer
        (MvPolynomial.pderiv i))
      (IsLocalization.mk' (AtPrime P) a s) =
      IsLocalization.mk' (AtPrime P)
        (s.1 * MvPolynomial.pderiv i a - a * MvPolynomial.pderiv i s.1)
        ⟨s.1 ^ 2, P.primeCompl.pow_mem s.2 2⟩ := by
  let B := AtPrime (k := k) (n := n) P
  let N : R := s.1 * MvPolynomial.pderiv i a - a * MvPolynomial.pderiv i s.1
  have hnum : algebraMap R B N =
      algebraMap R B s.1 * algebraMap R B (MvPolynomial.pderiv i a) -
        algebraMap R B a * algebraMap R B (MvPolynomial.pderiv i s.1) := by
    simp [N, map_sub, map_mul]
  have h := Stafford38.Characteristic.LocalizedDerivationQuotient.extendDerivation_apply_mk'_cross
    (k := k) (A := R (k := k) (n := n)) (B := B) (S := P.primeCompl)
    ((Algebra.linearMap (R (k := k) (n := n)) B).compDer (MvPolynomial.pderiv i)) a s
  apply (IsLocalization.map_units B
    ⟨s.1 ^ 2, P.primeCompl.pow_mem s.2 2⟩).mul_right_inj.mp
  calc
    algebraMap R B (s.1 ^ 2) *
        extendDerivation k R B P.primeCompl
          ((Algebra.linearMap R B).compDer (MvPolynomial.pderiv i))
          (IsLocalization.mk' B a s) = algebraMap R B N := by
        rw [map_pow, mul_comm]
        exact h.trans hnum.symm
    _ = algebraMap R B (s.1 ^ 2) *
        IsLocalization.mk' B N ⟨s.1 ^ 2, P.primeCompl.pow_mem s.2 2⟩ := by
          rw [mul_comm]
          exact (IsLocalization.mk'_spec B N
            ⟨s.1 ^ 2, P.primeCompl.pow_mem s.2 2⟩).symm

theorem localizedPDeriv_apply_mk
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (i : PhaseVar n) (a : R (k := k) (n := n)) (s : P.primeCompl) :
    localizedPDeriv P i (IsLocalization.mk' (AtPrime P) a s) =
      IsLocalization.mk' (AtPrime P)
        (s.1 * MvPolynomial.pderiv i a - a * MvPolynomial.pderiv i s.1)
        ⟨s.1 ^ 2, P.primeCompl.pow_mem s.2 2⟩ := by
  change extendDerivation k (R (k := k) (n := n)) (AtPrime P) P.primeCompl
      ((Algebra.linearMap (R (k := k) (n := n)) (AtPrime P)).compDer
        (MvPolynomial.pderiv i))
      (IsLocalization.mk' (AtPrime P) a s) = _
  exact localizedPDeriv_mk P i a s

theorem localizedPDeriv_add
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (i : PhaseVar n) (f g : AtPrime P) :
    localizedPDeriv P i (f + g) = localizedPDeriv P i f + localizedPDeriv P i g :=
  Derivation.map_add (localizedPDeriv P i) f g

theorem localizedPDeriv_mul
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (i : PhaseVar n) (f g : AtPrime P) :
    localizedPDeriv P i (f * g) =
      localizedPDeriv P i f * g + f * localizedPDeriv P i g := by
  rw [Derivation.leibniz]
  ring

theorem localizedPDeriv_algebraMap
    (P : Ideal (R (k := k) (n := n))) [P.IsPrime]
    (i : PhaseVar n) (a : R (k := k) (n := n)) :
    localizedPDeriv P i
        (algebraMap (R (k := k) (n := n)) (AtPrime P) a) =
      algebraMap (R (k := k) (n := n)) (AtPrime P) (MvPolynomial.pderiv i a) := by
  have h := Derivation.congr_fun (localizedPDeriv_compAlgebraMap P i) a
  change localizedPDeriv P i
      (algebraMap (R (k := k) (n := n)) (AtPrime P) a) =
    algebraMap (R (k := k) (n := n)) (AtPrime P) (MvPolynomial.pderiv i a) at h
  exact h

end
end Stafford38.Characteristic.LocalizedPartialDerivation
