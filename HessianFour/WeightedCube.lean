import Mathlib.Tactic.Ring

namespace HessianFour

theorem weighted_cube_remainder {R : Type*} [CommRing R] (w r e u : R) :
    w * (r + e * u)^3 - w * r^3 - 3 * w * r^2 * e * u =
      e^2 * (3 * w * r * u^2 + e * w * u^3) := by
  ring

end HessianFour
