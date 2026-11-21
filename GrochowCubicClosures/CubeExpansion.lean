import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring

namespace PureCubeBoundary

/-- The coefficient identity behind the affine conductor chart. -/
theorem translated_cubic_chart {R : Type*} [CommRing R] [CharP R 3]
    (a q l b z t : R) :
    a + (z + t) * q + (z + t) ^ 2 * l + b * (z + t) ^ 3 =
      (a + z * q + z ^ 2 * l + b * z ^ 3) +
        (q + 2 * z * l) * t + l * t ^ 2 + b * t ^ 3 := by
  rw [add_pow_char (p := 3) z t]
  ring

end PureCubeBoundary
