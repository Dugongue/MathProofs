import Mathlib.Tactic.Ring

theorem cubicCorrectsSquareZeroIdempotentError {R : Type*} [CommRing R] (x : R)
    (h : (x ^ 2 - x) ^ 2 = 0) :
    (3 * x ^ 2 - 2 * x ^ 3) ^ 2 = 3 * x ^ 2 - 2 * x ^ 3 := by
  apply sub_eq_zero.mp
  calc
    (3 * x ^ 2 - 2 * x ^ 3) ^ 2 - (3 * x ^ 2 - 2 * x ^ 3) =
        (x ^ 2 - x) ^ 2 * (4 * x ^ 2 - 4 * x - 3) := by ring
    _ = 0 := by rw [h, zero_mul]
