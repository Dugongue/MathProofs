import Mathlib.Tactic.Ring

namespace TISLUnusual

theorem theta_character_twice (a b d : ℤ) :
    a * b * ((d * (a + b)) * (d * (a + b) + 1) - 2)
      - b * (a + b) * ((d * a) * (d * a + 1) - 2)
      - a * (a + b) * ((d * b) * (d * b + 1) - 2) =
    2 * (a^2 + a*b + b^2) - d*a*b*(a+b) := by
  ring

end TISLUnusual
