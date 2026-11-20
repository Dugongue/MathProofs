import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

/-! Finite arithmetic in the two examples of the binary pencil proof.
The exponents in the cyclic group of order six parameterize the two determinants
in the opposite singular block example over the field of seven elements. -/

namespace MasulloGrochowExamples

/-- The joint image has precisely the pairs whose exponents sum to zero modulo three. -/
theorem oppositeSingularBlockImage :
    ∀ a b : Fin 6,
      (∃ x y : Fin 6, x + 2 * y = a ∧ 2 * x + y = b) ↔
        (a.val + b.val) % 3 = 0 := by
  decide

/-- Twice the determinant form of the regular example cannot be a single square. -/
theorem twoNonsquareModFive : ∀ x : Fin 5, x * x ≠ 2 := by
  decide

#print axioms oppositeSingularBlockImage
#print axioms twoNonsquareModFive

end MasulloGrochowExamples
