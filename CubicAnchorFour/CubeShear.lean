import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CubicAnchor

theorem cube_shear {R : Type*} [CommRing R] (h : (3 : R) = 0)
    (x a y b z : R) :
    (x + a * y + b * z)^3 = x^3 + a^3 * y^3 + b^3 * z^3 := by
  linear_combination
    (a * x^2 * y + b * x^2 * z + a^2 * x * y^2 + 2 * a * b * x * y * z +
      b^2 * x * z^2 + a^2 * b * y^2 * z + a * b^2 * y * z^2) * h

end CubicAnchor
