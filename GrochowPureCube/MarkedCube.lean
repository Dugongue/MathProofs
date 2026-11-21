import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.LinearCombination

namespace PureCube

/-- Subtracting cubes of the marks turns the graph constraint into equality. -/
theorem adjusted_mark_eq {R : Type*} [CommRing R] [CharP R 3]
    (f g a b : R) :
    f - a ^ 3 = g - b ^ 3 ↔ f - g = (a - b) ^ 3 := by
  rw [sub_pow_char (p := 3) a b]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

end PureCube
