import Mathlib.Algebra.Field.Basic

namespace QPFAverage

theorem overlap_cancel {K : Type*} [Field K]
    (a b c g h x y : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : (c * g * a) * b * y = (c * h * b) * a * x) :
    g * y = h * x := by
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc ha) hb)
  calc
    c * a * b * (g * y) = (c * g * a) * b * y := by ac_rfl
    _ = (c * h * b) * a * x := he
    _ = c * a * b * (h * x) := by ac_rfl

end QPFAverage
