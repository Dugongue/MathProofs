import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Init.Data.Nat.Fold
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace Mathproof.MinimumGeneration.RankBerkowitz.StreamedSum

/-- Sum one bit column of a family of word callbacks. The fold carries one
counter, and its only queries are for bits of the current column. -/
def column {terms : Nat} (read : Fin terms → Nat → Bool) (k : Nat) : Nat :=
  Fin.foldl terms (fun count i => count + (read i k).toNat) 0

def carry {terms : Nat} (read : Fin terms → Nat → Bool) (k : Nat) : Nat :=
  Nat.fold k (fun columnIndex _ incoming => (incoming + column read columnIndex) / 2) 0

@[simp] theorem carry_zero {terms : Nat} (read : Fin terms → Nat → Bool) :
    carry read 0 = 0 := rfl

theorem carry_succ {terms : Nat} (read : Fin terms → Nat → Bool) (k : Nat) :
    carry read (k+1) = (carry read k + column read k) / 2 := by
  simp only [carry, Nat.fold_succ]

/-- Compute a bit of the exact sum by scanning columns. -/
def bit {terms : Nat} (read : Fin terms → Nat → Bool) (k : Nat) : Bool :=
  decide ((carry read k + column read k) % 2 = 1)

private theorem foldl_eq_sum {d : Nat} (f : Fin d → Nat) :
    Fin.foldl d (fun acc i => acc + f i) 0 = ∑ i, f i := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
      exact congrArg (fun x => x + f (Fin.last d)) (ih (fun i => f i.castSucc))

theorem column_eq_sum {terms : Nat} (read : Fin terms → Nat → Bool) (k : Nat) :
    column read k = ∑ i, (read i k).toNat :=
  foldl_eq_sum _

theorem column_le {terms : Nat} (read : Fin terms → Nat → Bool) (k : Nat) :
    column read k ≤ terms := by
  rw [column_eq_sum]
  calc
    _ ≤ ∑ _ : Fin terms, (1 : Nat) :=
      Finset.sum_le_sum fun i _ => by cases read i k <;> decide
    _ = _ := by simp

theorem carry_le {terms : Nat} (read : Fin terms → Nat → Bool) (k : Nat) :
    carry read k ≤ terms := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc := column_le read k
    rw [carry_succ]
    omega

private theorem shift_decompose (x k : Nat) :
    x >>> k = (x.testBit k).toNat + 2 * (x >>> (k + 1)) := by
  have hp : (x.testBit k).toNat = (x >>> k) % 2 := by
    rw [← Nat.decide_shiftRight_mod_two_eq_one]
    rcases Nat.mod_two_eq_zero_or_one (x >>> k) with hz | ho
    · simp [hz]
    · simp [ho]
  rw [hp, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow _ 1]
  exact (Nat.mod_add_div (x >>> k) 2).symm

private theorem shifted_sum_columns {terms : Nat} (word : Fin terms → Nat) (k : Nat) :
    (∑ j, word j >>> k) =
      column (fun i a => (word i).testBit a) k + 2 * ∑ j, word j >>> (k + 1) := by
  rw [column_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => shift_decompose (word i) k

theorem shift_sum_eq_carry {terms : Nat} (word : Fin terms → Nat) (k : Nat) :
    (∑ i, word i) >>> k =
      carry (fun i a => (word i).testBit a) k + ∑ i, word i >>> k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.shiftRight_add, Nat.shiftRight_eq_div_pow _ 1, ih, shifted_sum_columns word k,
      ← Nat.add_assoc, Nat.add_mul_div_left _ _ (by decide : 0 < 2), carry_succ]

theorem bit_eq_testBit_sum {terms : Nat} (word : Fin terms → Nat) (k : Nat) :
    bit (fun i a => (word i).testBit a) k = (∑ i, word i).testBit k := by
  rw [← Nat.decide_shiftRight_mod_two_eq_one, shift_sum_eq_carry, shifted_sum_columns word k]
  unfold bit
  have h : (carry (fun i a => (word i).testBit a) k +
      (column (fun i a => (word i).testBit a) k + 2 * ∑ j, word j >>> (k + 1))) % 2 =
      (carry (fun i a => (word i).testBit a) k + column (fun i a => (word i).testBit a) k) % 2 := by
    omega
  rw [h]

theorem counters_binary_width {terms : Nat} (read : Fin terms → Nat → Bool) (k : Nat) :
    (carry read k).size + (column read k).size ≤ 2 * terms.size := by
  have h := Nat.size_le_size (carry_le read k)
  have h' := Nat.size_le_size (column_le read k)
  omega

end Mathproof.MinimumGeneration.RankBerkowitz.StreamedSum
