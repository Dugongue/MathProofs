import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

theorem integer_nonnegative_product (y : ℤ) : 0 ≤ y * (y - 1) := by
  by_cases hy : y ≤ 0
  · exact mul_nonneg_of_nonpos_of_nonpos hy (by omega)
  · exact mul_nonneg (by omega) (by omega)

theorem positive_sum_preserves_integer_zero
    (c f y s : ℤ) (hc : 0 < c) (hs : 0 ≤ s)
    (equation : y * (y - 1) + c * (f ^ 2 + s) = 0) :
    f = 0 := by
  have hy := integer_nonnegative_product y
  by_contra hf
  have hsq : 0 < f ^ 2 := sq_pos_of_ne_zero hf
  have hterm : 0 < c * (f ^ 2 + s) := mul_pos hc (by omega)
  omega

theorem integer_square_product_preserves_zero
    (c f y z s : ℤ) (hc : 0 < c) (hs : 0 ≤ s)
    (equation : (y * (y - 1)) * (z * (z - 1)) + c * (f ^ 2 + s) = 0) :
    f = 0 := by
  have hprod : 0 ≤ (y * (y - 1)) * (z * (z - 1)) :=
    mul_nonneg (integer_nonnegative_product y) (integer_nonnegative_product z)
  by_contra hf
  have hsq : 0 < f ^ 2 := sq_pos_of_ne_zero hf
  have hterm : 0 < c * (f ^ 2 + s) := mul_pos hc (by omega)
  omega

theorem cubic_simple_root_mod_23 :
    (3 : ZMod 23) ^ 3 - 3 - 1 = 0 ∧
    3 * (3 : ZMod 23) ^ 2 - 1 ≠ 0 := by
  decide

theorem cubic_has_no_root_mod_two :
    ∀ a : ZMod 2, a ^ 3 - a - 1 ≠ 0 := by
  decide
