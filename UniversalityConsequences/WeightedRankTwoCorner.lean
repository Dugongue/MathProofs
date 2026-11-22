import Mathlib.Algebra.Ring.Basic

theorem weightedRankTwoCorner {R : Type*} [CommRing R] (t a b c d : R)
    (detZero : a * d - b * c = 0) (left : t * a = t)
    (right : t * d = t) (offDiagonal : t * b = 0) : t = 0 := by
  calc
    t = (t * a) * d - (t * b) * c := by
      rw [left, right, offDiagonal, zero_mul, sub_zero]
    _ = t * (a * d - b * c) := by
      rw [mul_sub, mul_assoc, mul_assoc]
    _ = 0 := by rw [detZero, mul_zero]
