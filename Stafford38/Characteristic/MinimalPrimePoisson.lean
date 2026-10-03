module
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Stafford38.Characteristic.BaseRelativePoisson
public import Stafford38.Characteristic.PostScalarExtensionPoisson

@[expose] public section

/-!
# Minimal-prime assembly for base-relative Poisson closure

This file gives the commutative-algebra assembly step from bracket membership
in every minimal prime to base-relative Poisson closure of a radical. It is a
reusable conditional lemma; the current canonical-support proof obtains its
involutivity input through `PaperLocalizedInvolutivity` and
`GabberGlobalAssembly`.
-/

namespace Stafford38.Characteristic.MinimalPrimePoisson

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.Geometry.CoisotropicTranslation

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- Componentwise membership in every minimal prime assembles to the exact
base-relative Poisson condition on the radical.  This is the final elementary
commutative-algebra step after the genuine Gabber integrability input. -/
theorem radical_isBaseRelativePoisson_of_minimalPrimes
    (J : Ideal (SymbolRing k n))
    (h : ∀ P ∈ J.minimalPrimes,
      ∀ f : MvPolynomial (Fin n) k, baseLift f ∈ J.radical →
        ∀ g ∈ J.radical, poissonBracket (baseLift f) g ∈ P) :
    IsBaseRelativePoisson J.radical := by
  intro f hf g hg
  rw [← J.sInf_minimalPrimes]
  exact Ideal.mem_sInf.mpr fun P hP => h P hP f hf g hg

/-- Componentwise involutivity is the natural sufficient hypothesis for the
minimal-prime assembly above.  The only commutative-algebra input is that the
radical is contained in every prime over the original ideal. -/
theorem radical_isBaseRelativePoisson_of_minimalPrimes_isInvolutive
    (J : Ideal (SymbolRing k n))
    (h : ∀ P ∈ J.minimalPrimes, IsInvolutive P) :
    IsBaseRelativePoisson J.radical := by
  apply radical_isBaseRelativePoisson_of_minimalPrimes J
  intro P hP f hf g hg
  have hprime : P.IsPrime := hP.1.1
  have hradical : J.radical ≤ P := hprime.radical_le_iff.mpr hP.1.2
  exact h P hP (baseLift f) (hradical hf) g (hradical hg)

#print axioms radical_isBaseRelativePoisson_of_minimalPrimes
#print axioms radical_isBaseRelativePoisson_of_minimalPrimes_isInvolutive

end

end Stafford38.Characteristic.MinimalPrimePoisson
