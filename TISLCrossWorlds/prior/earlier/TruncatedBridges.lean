import Mathlib.Tactic.LinearCombination

namespace TISLAtlasClosure

theorem truncated_exp_add {R : Type*} [CommRing R] (a x y : R)
    (ha : 2 * a = 1) (hxxy : x ^ 2 * y = 0) (hxyy : x * y ^ 2 = 0) :
    (1 + x + a * x ^ 2) * (1 + y + a * y ^ 2) =
      1 + (x + y) + a * (x + y) ^ 2 := by
  linear_combination -(x * y) * ha + (a + a ^ 2 * y) * hxxy + a * hxyy

theorem truncated_log_exp {R : Type*} [CommRing R] (a x : R)
    (hx : x ^ 3 = 0) :
    (x + a * x ^ 2) - a * (x + a * x ^ 2) ^ 2 = x := by
  linear_combination -(2 * a ^ 2 + a ^ 3 * x) * hx

theorem truncated_exp_log {R : Type*} [CommRing R] (a x : R)
    (hx : x ^ 3 = 0) :
    (x - a * x ^ 2) + a * (x - a * x ^ 2) ^ 2 = x := by
  linear_combination (-2 * a ^ 2 + a ^ 3 * x) * hx

end TISLAtlasClosure
