import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace SliceSimilarityFour

theorem three_units_product {R : Type*} [CommRing R] (x y z : R)
    (h : x * y * z = 0) :
    (1 + x) * (1 + y) * (1 + z) = 1 + x + y + z + x * y + x * z + y * z := by
  linear_combination h

end SliceSimilarityFour
