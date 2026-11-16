import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Ring
import Mathproof.MinimumGenerationRankBerkowitzBitEvaluation

/-!
Digit-column binary multiplication with a one-bit input interface.
The nested tail folds retain a column, a row, a running count, and a bounded
carry. Partial counts and carries are bounded at every operand query.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.ColumnProduct

open Finset

def partialCount (left right : Nat → Bool) (column rows : Nat) : Nat :=
  Nat.fold rows (fun i _ acc => acc + (left i && right (column - i)).toNat) 0

def columnCount (left right : Nat → Bool) (column : Nat) : Nat :=
  partialCount left right column (column + 1)

def carry (left right : Nat → Bool) (columns : Nat) : Nat :=
  Nat.fold columns (fun i _ acc => (acc + columnCount left right i) / 2) 0

def outputBit (left right : Nat → Bool) (index : Nat) : Bool :=
  decide ((carry left right index + columnCount left right index) % 2 = 1)

@[simp] theorem partialCount_zero (left right : Nat → Bool) (column : Nat) :
    partialCount left right column 0 = 0 := by simp [partialCount]

theorem partialCount_succ (left right : Nat → Bool) (column rows : Nat) :
    partialCount left right column (rows + 1) =
      partialCount left right column rows + (left rows && right (column - rows)).toNat := by
  simp [partialCount, Nat.fold_succ]

@[simp] theorem carry_zero (left right : Nat → Bool) : carry left right 0 = 0 := by
  simp [carry]

theorem carry_succ (left right : Nat → Bool) (columns : Nat) :
    carry left right (columns + 1) =
      (carry left right columns + columnCount left right columns) / 2 := by
  simp [carry, Nat.fold_succ]

theorem partialCount_le (left right : Nat → Bool) (column rows : Nat) :
    partialCount left right column rows ≤ rows := by
  induction rows with
  | zero => simp
  | succ rows ih =>
    rw [partialCount_succ]
    have hOne := Bool.toNat_le (left rows && right (column - rows))
    omega

theorem carry_le (left right : Nat → Bool) (columns : Nat) :
    carry left right columns ≤ columns := by
  induction columns with
  | zero => simp
  | succ columns ih =>
    rw [carry_succ]
    have hCount := partialCount_le left right columns (columns + 1)
    change columnCount left right columns ≤ columns + 1 at hCount
    omega

private theorem bit_and_toNat (x y : Bool) : (x && y).toNat = x.toNat * y.toNat := by
  cases x <;> cases y <;> rfl

private theorem partialCount_eq_sum (left right : Nat → Bool) (column rows : Nat) :
    partialCount left right column rows =
      ∑ i ∈ range rows, (left i).toNat * (right (column - i)).toNat := by
  induction rows with
  | zero => simp
  | succ rows ih =>
    rw [partialCount_succ, Finset.sum_range_succ, ih, bit_and_toNat]

private theorem lowBits_succ (x i : Nat) :
    x % 2^(i+1) = 2^i * (x.testBit i).toNat + x % (2^i) := by
  rw [Nat.mod_pow_succ, Nat.add_comm, Nat.toNat_testBit]

private theorem weightedBits (x n : Nat) :
    (∑ i ∈ range n, (x.testBit i).toNat * 2^i) = x % (2^n) := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, lowBits_succ]
    ac_rfl

/-- The triangular truncation of the product, retaining only terms in lower
columns. It is used in the specification and never appears in the cursor. -/
private def truncatedProduct (x y n : Nat) : Nat :=
  ∑ i ∈ range n, (x.testBit i).toNat * (2^i * (y % 2^(n-i)))

private theorem prefix_modEq (x y n : Nat) : truncatedProduct x y n ≡ x*y [MOD 2^n] := by
  have hRewrite : (x % 2^n) * y =
      ∑ i ∈ range n, (x.testBit i).toNat * (2^i * y) := by
    rw [← weightedBits, Finset.sum_mul]
    simp only [Nat.mul_assoc]
  refine Nat.ModEq.trans ?_ ((Nat.mod_modEq x (2^n)).mul_right y)
  rw [hRewrite]
  apply Nat.ModEq.sum
  intro i hi
  have hLt := Finset.mem_range.mp hi
  have hPow : 2^i * 2^(n-i) = 2^n := by
    rw [← pow_add, Nat.add_sub_of_le hLt.le]
  rw [← hPow]
  exact ((Nat.mod_modEq y (2^(n-i))).mul_left' (2^i)).mul_left (x.testBit i).toNat

private theorem prefix_succ (x y n : Nat) :
    truncatedProduct x y (n+1) = truncatedProduct x y n +
      columnCount x.testBit y.testBit n * 2^n := by
  unfold truncatedProduct columnCount
  rw [partialCount_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ]
  have hStep (i : Nat) (hi : i ∈ range n) :
      (x.testBit i).toNat * (2^i * (y % 2^(n+1-i))) =
        (x.testBit i).toNat * (2^i * (y % 2^(n-i))) +
          ((x.testBit i).toNat * (y.testBit (n-i)).toNat) * 2^n := by
    have hLt := Finset.mem_range.mp hi
    have hIdx : n+1-i = n-i+1 := by omega
    have hPow : 2^i * 2^(n-i) = 2^n := by
      rw [← pow_add, Nat.add_sub_of_le hLt.le]
    rw [hIdx, lowBits_succ, ← hPow]
    ring
  rw [Finset.sum_congr rfl hStep, Finset.sum_add_distrib, Nat.add_mul, Finset.sum_mul]
  have hLast : n + 1 - n = 1 := by omega
  rw [hLast, Nat.sub_self, pow_one]
  rw [Nat.toNat_testBit y 0]
  simp
  ring

private theorem carry_eq_prefix_div (x y n : Nat) :
    carry x.testBit y.testBit n = truncatedProduct x y n / 2^n := by
  induction n with
  | zero => simp [truncatedProduct]
  | succ n ih =>
    rw [carry_succ, ih, prefix_succ, pow_succ, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]

/-- Exact arbitrary-input multiplication using only the two bit streams. -/
theorem outputBit_eq (x y index : Nat) :
    outputBit x.testBit y.testBit index = (x*y).testBit index := by
  have hPrefix : (truncatedProduct x y (index+1)).testBit index = (x*y).testBit index := by
    have hEq : truncatedProduct x y (index+1) % 2^(index+1) = (x*y) % 2^(index+1) :=
      prefix_modEq x y (index+1)
    have hBit := congrArg (fun n : Nat => n.testBit index) hEq
    simpa [Nat.testBit_mod_two_pow] using hBit
  rw [← hPrefix, Nat.testBit_eq_decide_div_mod_eq, prefix_succ, outputBit,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), carry_eq_prefix_div]

open BitEvaluation

/-- The bits retained when an operand callback is active. The extra two bits
store which operand is queried and the saved bit of a completed left query. -/
def suspended (target column row runningCarry runningCount : Nat)
    (requestRight savedLeft : Bool) : List Bool :=
  let w := (target+1).size
  bits w target ++ bits w column ++ bits w row ++ bits w runningCarry ++
    bits w runningCount ++ [requestRight, savedLeft]

theorem suspended_length (target column row runningCarry runningCount : Nat)
    (requestRight savedLeft : Bool) :
    (suspended target column row runningCarry runningCount requestRight savedLeft).length =
      5 * (target+1).size + 2 := by
  simp [suspended]
  omega

/-- Every natural register stored at a live callback fits its encoded width. -/
theorem suspended_registers_fit (left right : Nat → Bool) (target column row : Nat)
    (hc : column ≤ target) (hr : row ≤ column + 1) :
    let w := (target + 1).size
    target < 2^w ∧ column < 2^w ∧ row < 2^w ∧
      carry left right column < 2^w ∧ partialCount left right column row < 2^w := by
  dsimp only
  have hWidth := Nat.lt_size_self (target+1)
  have hCarry := carry_le left right column
  have hCount := partialCount_le left right column row
  omega

end Mathproof.MinimumGeneration.RankBerkowitz.ColumnProduct
