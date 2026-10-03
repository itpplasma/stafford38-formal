module
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.CommonOpenEvaluation

/-- Polynomial evaluation follows the same common-open map and the same arc.
This transports the nonvanishing numerator used to select the smooth locus. -/
theorem eval_map_eq_arc_eval₂
    {k Q E L σ : Type*} [CommSemiring k] [CommSemiring Q]
    [CommSemiring E] [CommSemiring L] [Algebra k Q] [Algebra k L]
    (g : Q →+* E) (rho : E →+* L)
    (hground : (rho.comp g).comp (algebraMap k Q) = algebraMap k L)
    (qQ : σ → Q) (qC : σ → E) (qL : σ → L)
    (hcoords : ∀ i, qC i = g (qQ i))
    (hposition : ∀ i, rho (qC i) = qL i)
    (p : MvPolynomial σ k) :
    MvPolynomial.eval qL (MvPolynomial.map (algebraMap k L) p) =
      rho (g (MvPolynomial.eval₂ (algebraMap k Q) qQ p)) := by
  rw [MvPolynomial.eval_map]
  have hcolumns : (rho.comp g) ∘ qQ = qL := by
    funext i
    change rho (g (qQ i)) = qL i
    rw [← hcoords i]
    exact hposition i
  have h := MvPolynomial.eval₂_comp_left (rho.comp g) (algebraMap k Q) qQ p
  rw [hground, hcolumns] at h
  exact h.symm

end Stafford38.Geometry.CommonOpenEvaluation
