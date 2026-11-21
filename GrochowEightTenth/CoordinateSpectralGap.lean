import Mathlib.Tactic

namespace CoordinateSpectralGap

theorem adjacentWeightLoss (j a b : ℝ) :
    2 * (j * a + (j + 1) * b) - (2 * j + 1) * (a + b) = b - a := by
  ring

theorem symmetricOuterSpread (a b c d : ℝ) :
    (a * c - b * d) ^ 2 + 4 * ((a * d + b * c) / 2) ^ 2 =
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  ring

#print axioms adjacentWeightLoss
#print axioms symmetricOuterSpread

end CoordinateSpectralGap
