import Mathlib.Tactic

namespace InjectionDeficit

theorem linearEnvelope (x e d : ℝ) (he : 0 ≤ e) (hd : 0 ≤ d)
    (cubic : x ^ 3 ≤ 64 * d ^ 2 * (2 * x + 2 * e + d)) :
    x ≤ 14 * (e + d) := by
  by_contra! counterexample
  have hx : 0 < x := by linarith
  have budget : 2 * x + 2 * e + d ≤ 3 * x := by linarith
  have weighted := mul_le_mul_of_nonneg_left budget (show 0 ≤ 64 * d ^ 2 by positivity)
  have product_bound : x ^ 2 * x ≤ (192 * d ^ 2) * x := by
    calc
      x ^ 2 * x = x ^ 3 := by ring
      _ ≤ 64 * d ^ 2 * (2 * x + 2 * e + d) := cubic
      _ ≤ (192 * d ^ 2) * x := by nlinarith only [weighted]
  have square_bound := (mul_le_mul_iff_left₀ hx).mp product_bound
  have strict : 0 < (x - 14 * d) * (x + 14 * d) := by
    apply mul_pos
    · linarith
    · positivity
  nlinarith only [square_bound, strict, sq_nonneg d]

#print axioms linearEnvelope

end InjectionDeficit
