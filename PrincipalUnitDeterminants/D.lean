import Mathlib

namespace PrincipalUnitFour.Uniform

/-- Frobenius kills the principal part once its power exceeds the nilpotence index. -/
theorem principal_unit_frobenius {R : Type*} [CommRing R] [CharP R 2]
    (a : R) (n : ℕ) :
    (1 + a) ^ (2 ^ n) = 1 + a ^ (2 ^ n) := by
  have square (x : R) : (1 + x)^2 = 1 + x^2 := by
    have h : (2 : R) = 0 := CharP.cast_eq_zero R 2
    calc
      (1 + x)^2 = 1 + (2 : R)*x + x^2 := by ring
      _ = 1 + x^2 := by rw [h, zero_mul, add_zero]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, pow_mul, ih, square]

/-- A principal unit with residue 1 modulo 2 cannot square to -1 modulo 4. -/
theorem unramified_square_ne_neg_one {R : Type*} [CommRing R]
    (h₂ : (2 : R) ≠ 0) (h₄ : (4 : R) = 0) (c : R) :
    (1 + 2*c)^2 ≠ -1 := by
  have h : (1 + 2*c)^2 = 1 := by
    calc
      (1 + 2*c)^2 = 1 + (4 : R)*(c + c^2) := by ring
      _ = 1 := by rw [h₄, zero_mul, add_zero]
  rw [h]
  intro hneg
  apply h₂
  linear_combination hneg

end PrincipalUnitFour.Uniform
