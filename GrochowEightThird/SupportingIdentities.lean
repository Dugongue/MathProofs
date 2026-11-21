import Mathlib.Tactic

theorem signCubicNormalEquations {a b : ℚ}
    (h₁ : (7 / 24) * a + (31 / 160) * b = 3 / 8)
    (h₂ : (31 / 160) * a + (127 / 896) * b = 15 / 64) :
    a = 8325 / 4088 ∧ b = -(165 / 146) := by
  constructor <;> linarith

theorem signCubicCriticalBounds :
    (1 / 2 : ℚ)^2 < 185 / 308 ∧ (185 / 308 : ℚ) < (4 / 5)^2 ∧
    (2 / 3 : ℚ) * (8325 / 4088) * (4 / 5) - 1 = 352 / 4088 := by
  norm_num

theorem nystromContrastIdentity (a b c X Y z : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hdet : a * b - c^2 ≠ 0) :
    X / a + Y / b - (b * X + a * Y - 2 * c * z) / (a * b - c^2) =
      (2 * c * z - c^2 * (X / a + Y / b)) / (a * b - c^2) := by
  field_simp
  <;> ring

#print axioms signCubicNormalEquations
#print axioms signCubicCriticalBounds
#print axioms nystromContrastIdentity
