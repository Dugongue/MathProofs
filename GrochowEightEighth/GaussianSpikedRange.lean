import Mathlib.Tactic

namespace GaussianSpikedRange

theorem excessLower (m k z a : ℝ) (hm : 0 < m) (hk : 0 < k)
    (size : 128 * k * k ≤ m) (mixing : m ≤ 8 * k * z)
    (ha : 0 < a) (ha₂ : a ≤ 2) :
    m / (32 * k) + k ≤ (1 + z) / a := by
  have width : k ≤ m / (128 * k) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith only [size]
  have tilt : m / (8 * k) ≤ z := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [mixing]
  have hz : 0 ≤ z := le_trans (by positivity) tilt
  have quotient : z / 2 ≤ (1 + z) / a := by
    apply (le_div_iff₀ ha).2
    have scaled := mul_le_mul_of_nonneg_left ha₂ (show 0 ≤ z / 2 by positivity)
    linarith
  have scale₄ : m / (32 * k) = 4 * (m / (128 * k)) := by
    field_simp
    ring
  have scale₁₆ : m / (8 * k) = 16 * (m / (128 * k)) := by
    field_simp
    ring
  linarith

#print axioms excessLower

end GaussianSpikedRange
