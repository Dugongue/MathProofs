import Mathlib.Tactic

namespace SketchConfidence

theorem quarterBound (alpha h s t : ℝ) (positive : 0 < s)
    (cauchy : (alpha * h + s)^2 ≤ s * t) :
    4 * alpha * h ≤ t := by
  have amgm : (4 * alpha * h) * s ≤ (alpha * h + s)^2 := by
    nlinarith only [sq_nonneg (alpha * h - s)]
  apply (mul_le_mul_iff_left₀ positive).mp
  simpa only [mul_comm s] using amgm.trans cauchy

theorem sharpExcess (alpha b : ℝ) (nonzero : alpha ≠ 0) :
    (alpha * b) / (2 * alpha)^2 = b / (4 * alpha) := by
  field_simp
  ring

#print axioms quarterBound
#print axioms sharpExcess

end SketchConfidence
