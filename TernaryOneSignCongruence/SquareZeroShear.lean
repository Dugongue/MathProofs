import Mathlib.Algebra.Ring.Basic

namespace AlternatingSignQueries

/-- The normalized form shift is a cube of a square-zero unipotent in
characteristic three. The ring may be a matrix ring. -/
theorem squareZeroShear_cancels {R : Type*} [Ring R] (t : R)
    (squareZero : t * t = 0) (threeZero : t + t + t = 0) :
    (1 + t) * (1 + t) * (1 + t) = 1 := by
  calc
    _ = 1 + (t + t + t) := by
      simp only [add_mul, mul_add, one_mul, mul_one, squareZero, add_zero, add_assoc]
    _ = 1 := by rw [threeZero, add_zero]

/-- A shear in a square-zero ideal fixes the other radical elements. -/
theorem squareZeroShear_fixes {R : Type*} [Ring R] (t j : R)
    (leftZero : t * j = 0) (rightZero : j * t = 0) :
    (1 + t) * j * (1 + t) = j := by
  simp [add_mul, mul_add, leftZero, rightZero]

end AlternatingSignQueries
