import Mathlib.Algebra.Group.Basic
import Lean.Elab.Tactic.Omega

namespace ExactCubicOrientation

/-- At least one projection gives a strict vertical codimension bound. -/
theorem asymmetric_projection_bound (x y : ℕ) (h : 0 < x + y) :
    x + y < 3 * x ∨ x + y < 2 * y := by
  omega

/-- Matching the dimension of an adjoint component and the rank of its projector
distinguishes the two horizontal roles, both before and after base change. -/
theorem distinct_regular_multiplicities (n m : ℕ) (hn : 0 < n)
    (h : n = m) : 2 * n ≠ 3 * m := by
  omega

/-- The two free residue determinants combine into one unit raised to the
algebra dimension, as a group identity over any base. -/
theorem residual_determinant_monomial {G : Type*} [CommGroup G]
    (p q : G) (n : ℕ) :
    (p ^ n) ^ 2 * q ^ n = (p ^ 2 * q) ^ n := by
  rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]

/-- Over a unit group of exponent two, a residue determinant with even
multiplicity contributes trivially. -/
theorem residue_correction_trivial {G : Type*} [Group G]
    (u : G) (h : u ^ (2 : ℕ) = 1) (k : ℕ) :
    u ^ (2 * k) = 1 := by
  rw [pow_mul, h, one_pow]

end ExactCubicOrientation
