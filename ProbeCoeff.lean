module
public import Stafford38.MathlibCompat.MvPolynomialCoeff
public import Stafford38.Characteristic.Polynomial
@[expose] public section
open Stafford38.Characteristic
example {k : Type} [CommRing k] (n : ℕ) (t : Fin n) (P : SymbolRing k n)
    (hP : MvPolynomial.coeff (Finsupp.single (.inr t : PhaseVar n) 1) P = 1) :
    MvPolynomial.coeff (Finsupp.single (.inr t : PhaseVar n) 1)
      (P - MvPolynomial.X (.inr t : PhaseVar n)) = 0 := by
  have hP' : AddMonoidAlgebra.coeff P (Finsupp.single (.inr t : PhaseVar n) 1) = 1 := by
    change MvPolynomial.coeff (Finsupp.single (.inr t : PhaseVar n) 1) P = 1
    exact hP
  have hX' : AddMonoidAlgebra.coeff
      (MvPolynomial.X (.inr t : PhaseVar n) : SymbolRing k n)
      (Finsupp.single (.inr t : PhaseVar n) 1) = 1 := by
    change MvPolynomial.coeff (Finsupp.single (.inr t : PhaseVar n) 1)
      (MvPolynomial.X (.inr t : PhaseVar n)) = 1
    simp [MvPolynomial.coeff, MvPolynomial.X]
  change AddMonoidAlgebra.coeff
    (P - MvPolynomial.X (.inr t : PhaseVar n))
    (Finsupp.single (.inr t : PhaseVar n) 1) = 0
  rw [AddMonoidAlgebra.coeff_sub]
  change AddMonoidAlgebra.coeff P (Finsupp.single (.inr t : PhaseVar n) 1) -
    AddMonoidAlgebra.coeff (MvPolynomial.X (.inr t : PhaseVar n) : SymbolRing k n)
      (Finsupp.single (.inr t : PhaseVar n) 1) = 0
  rw [hP', hX', sub_self]
