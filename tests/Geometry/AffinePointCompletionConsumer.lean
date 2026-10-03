module
public import Stafford38.Geometry.AffinePointCompletion

@[expose] public section

open MvPolynomial

namespace Stafford38.Geometry.AffinePointCompletionConsumer

open Stafford38.Geometry.AffinePointCompletion

-- An independent literal chart-point check: the translated coordinate vanishes
-- at the selected rational point, with the expected sign.
example :
    (X (0 : Fin 1) - C (3 : ℚ)) ∈ pointIdeal (fun _ : Fin 1 => (3 : ℚ)) := by
  change MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℚ))
    (X (0 : Fin 1) - C (3 : ℚ)) = 0
  simp

-- The public chart translation sends the coordinate to X - p_i.
example (p : Fin 1 → ℚ) :
    translate p (X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) =
      X (0 : Fin 1) - C (p 0) := by
  simp [translate]

#print axioms powerSeriesCompletionAtPoint

end Stafford38.Geometry.AffinePointCompletionConsumer
