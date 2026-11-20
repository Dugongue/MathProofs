import EvenP6Install
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

namespace EvenTI.CellPreparation

theorem modeWidths_le_dense (n d : ℕ) (hn : 2 ≤ n) :
    d * n ≤ n ^ d := by
  cases d with
  | zero => simp
  | succ d =>
    rw [pow_succ]
    exact Nat.mul_le_mul_right n
      ((Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := d))).trans
        (Nat.pow_le_pow_left hn d))

theorem enlargedGrid_le (n a b : ℕ) (ha : a ≤ 2 * n) (hb : b ≤ 2 * n) :
    a ^ 2 * b ^ 2 ≤ 16 * n ^ 4 := by
  calc
    _ ≤ (2 * n) ^ 2 * (2 * n) ^ 2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left ha _) (Nat.pow_le_pow_left hb _)
    _ = _ := by ring

theorem orderWord_bound (q width bits N : ℕ) (hq : 1 ≤ q) (hb : q ≤ 2 ^ bits)
    (hWidth : width ≤ N) : q ^ width - 1 < 2 ^ (bits * N) := by
  have h₁ : q ^ width ≤ (2 ^ bits) ^ N :=
    (Nat.pow_le_pow_left hb width).trans
      (Nat.pow_le_pow_right (Nat.two_pow_pos bits) hWidth)
  have h₀ := Nat.one_le_pow width q hq
  rw [pow_mul]
  omega

#print axioms modeWidths_le_dense
#print axioms enlargedGrid_le
#print axioms orderWord_bound

end EvenTI.CellPreparation
