import Mathlib.Tactic.NoncommRing

namespace CubicInverse

/-- The finite inverse used in the degree-one transporter calculation. -/
theorem geometric_inverse_four {R : Type*} [Ring R] (e : R) (h : e ^ 4 = 0) :
    (1 - e + e ^ 2 - e ^ 3) * (1 + e) = 1 := by
  calc
    _ = 1 - e ^ 4 := by noncomm_ring
    _ = 1 := by rw [h, sub_zero]

end CubicInverse
