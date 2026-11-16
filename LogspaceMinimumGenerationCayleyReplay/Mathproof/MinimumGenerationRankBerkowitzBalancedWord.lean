import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Init.Data.BitVec.Bitblast

/-!
Balanced bit procedures for addition, order, and multiplication. An operand is a
function answering bit queries. The multiplication contains no complete live word
at a pending addition. Algebraic proofs reuse the standard BitVec carry and
schoolbook-row semantics.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.BalancedWord

structure Transfer where
  generate : Bool
  propagate : Bool

namespace Transfer

def apply (t : Transfer) (carry : Bool) : Bool :=
  t.generate || (t.propagate && carry)

def identity : Transfer := ⟨false, true⟩

def single (x y : Bool) : Transfer := ⟨x && y, x || y⟩

/-- Join two consecutive bit blocks, with the low block applied first. -/
def merge (low high : Transfer) : Transfer :=
  ⟨high.generate || (high.propagate && low.generate),
    high.propagate && low.propagate⟩

@[simp] theorem identity_apply (carry : Bool) : identity.apply carry = carry := rfl

theorem single_apply (x y carry : Bool) :
    (single x y).apply carry = Bool.atLeastTwo x y carry := by
  cases x <;> cases y <;> cases carry <;> rfl

theorem merge_apply (low high : Transfer) (carry : Bool) :
    (merge low high).apply carry = high.apply (low.apply carry) := by
  rcases low with ⟨a, b⟩
  rcases high with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases carry <;> rfl

end Transfer

/-- A complete binary reduction of a block of bit-position transfers. -/
def transferTree (leaf : Nat → Transfer) : Nat → Nat → Transfer
  | 0, start => leaf start
  | h + 1, start =>
    Transfer.merge (transferTree leaf h start) (transferTree leaf h (start + 2 ^ h))

private def sequentialApply (leaf : Nat → Transfer) (start : Nat) :
    Nat → Bool → Bool
  | 0, carry => carry
  | n + 1, carry => (leaf (start + n)).apply (sequentialApply leaf start n carry)

private theorem sequentialApply_add (leaf : Nat → Transfer) (start m n : Nat) (carry : Bool) :
    sequentialApply leaf start (m + n) carry =
      sequentialApply leaf (start + m) n (sequentialApply leaf start m carry) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (leaf (start + (m + n))).apply (sequentialApply leaf start (m + n) carry) =
      (leaf ((start + m) + n)).apply
        (sequentialApply leaf (start + m) n (sequentialApply leaf start m carry))
    rw [ih, Nat.add_assoc]

private theorem tree_apply (leaf : Nat → Transfer) (height start : Nat) (carry : Bool) :
    (transferTree leaf height start).apply carry = sequentialApply leaf start (2 ^ height) carry := by
  induction height generalizing start carry with
  | zero => simp [transferTree, sequentialApply]
  | succ height ih =>
    rw [transferTree, Transfer.merge_apply, ih, ih, ← sequentialApply_add, pow_succ, Nat.mul_two]

def carryBit (height cutoff : Nat) (left right : Nat → Bool) (initial : Bool) : Bool :=
  (transferTree (fun j => if j < cutoff then Transfer.single (left j) (right j)
    else Transfer.identity) height 0).apply initial

private theorem clipped_sequential {w : Nat} (x y : BitVec w) (cutoff len : Nat)
    (initial : Bool) :
    sequentialApply (fun j => if j < cutoff then Transfer.single (x.getLsbD j) (y.getLsbD j)
      else Transfer.identity) 0 len initial = BitVec.carry (min len cutoff) x y initial := by
  induction len with
  | zero => simp [sequentialApply]
  | succ len ih =>
    rw [sequentialApply, ih]
    simp only [Nat.zero_add]
    by_cases h : len < cutoff
    · rw [if_pos h, min_eq_left h.le, min_eq_left (by omega), Transfer.single_apply]
      exact (BitVec.carry_succ len x y initial).symm
    · have hle : cutoff ≤ len := by omega
      rw [if_neg h, Transfer.identity_apply, min_eq_right hle, min_eq_right (by omega)]

theorem carryBit_eq {w : Nat} (x y : BitVec w) (height cutoff : Nat) (initial : Bool)
    (hCutoff : cutoff ≤ 2 ^ height) :
    carryBit height cutoff x.getLsbD y.getLsbD initial = BitVec.carry cutoff x y initial := by
  rw [carryBit, tree_apply, clipped_sequential, min_eq_right hCutoff]

def addBit (height index : Nat) (left right : Nat → Bool) (initial : Bool) : Bool :=
  left index ^^ (right index ^^ carryBit height index left right initial)

theorem addBit_eq {w : Nat} (x y : BitVec w) (height index : Nat) (initial : Bool)
    (hIndex : index < w) (hHeight : index ≤ 2 ^ height) :
    addBit height index x.getLsbD y.getLsbD initial =
      (x + y + (BitVec.ofBool initial).setWidth w).getLsbD index := by
  rw [addBit, carryBit_eq _ _ _ _ _ hHeight, BitVec.getLsbD_add_add_bool hIndex]

theorem compareBit_eq {w : Nat} (x y : BitVec w) (height : Nat) (hWidth : w ≤ 2 ^ height) :
    (!(carryBit height w x.getLsbD (~~~y).getLsbD true)) = x.ult y := by
  rw [carryBit_eq _ _ _ _ _ hWidth, BitVec.ult_eq_not_carry]

private def sequentialSum {w : Nat} (row : Nat → BitVec w) (start : Nat) :
    Nat → BitVec w
  | 0 => 0
  | n + 1 => sequentialSum row start n + row (start + n)

private theorem sequentialSum_add {w : Nat} (row : Nat → BitVec w) (start m n : Nat) :
    sequentialSum row start (m + n) =
      sequentialSum row start m + sequentialSum row (start + m) n := by
  induction n with
  | zero => simp [sequentialSum]
  | succ n ih =>
    change sequentialSum row start (m + n) + row (start + (m + n)) =
      sequentialSum row start m + (sequentialSum row (start + m) n + row ((start + m) + n))
    rw [ih, Nat.add_assoc, BitVec.add_assoc]

private def sumTree {w : Nat} (row : Nat → BitVec w) : Nat → Nat → BitVec w
  | 0, start => row start
  | h + 1, start => sumTree row h start + sumTree row h (start + 2 ^ h)

private theorem sumTree_eq {w : Nat} (row : Nat → BitVec w) (height start : Nat) :
    sumTree row height start = sequentialSum row start (2 ^ height) := by
  induction height generalizing start with
  | zero => simp [sumTree, sequentialSum]
  | succ height ih => rw [sumTree, ih, ih, ← sequentialSum_add, pow_succ, Nat.mul_two]

private def partialRow {w : Nat} (x y : BitVec w) (row : Nat) : BitVec w :=
  if y.getLsbD row then x <<< row else 0

private theorem sequentialSum_partialRow {w : Nat} (x y : BitVec w) (n : Nat) :
    sequentialSum (partialRow x y) 0 (n + 1) = BitVec.mulRec x y n := by
  induction n with
  | zero => simp [sequentialSum, partialRow, BitVec.mulRec_zero_eq]
  | succ n ih =>
    rw [sequentialSum, ih, BitVec.mulRec_succ_eq]
    simp [partialRow]

private theorem sumTree_partialRow {w : Nat} (x y : BitVec w) (height : Nat)
    (hWidth : w ≤ 2 ^ height) :
    sumTree (partialRow x y) height 0 = x * y := by
  rw [sumTree_eq]
  have hPos : 0 < 2 ^ height := Nat.two_pow_pos height
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hPos.ne'
  rw [hn, sequentialSum_partialRow, BitVec.mulRec_eq_mul_signExtend_setWidth,
    BitVec.setWidth_setWidth_of_le y (by omega)]
  simp

/-- Compute one bit of the sum of a dyadic block of schoolbook rows. Recursion
through either child asks only for the requested bit, including during carry
generation for their sum. No child operand is assembled as a word. -/
def mulBit (width : Nat) (left right : Nat → Bool) : Nat → Nat → Nat → Bool
  | 0, start, index =>
    if index < width then
      right start && (decide (start ≤ index) && left (index - start))
    else false
  | h + 1, start, index =>
    if index < width then
      addBit width.size index (mulBit width left right h start)
        (mulBit width left right h (start + 2 ^ h)) false
    else false

private theorem mulBit_tree_eq {w : Nat} (x y : BitVec w) (height start : Nat) :
    mulBit w x.getLsbD y.getLsbD height start = (sumTree (partialRow x y) height start).getLsbD := by
  funext index
  induction height generalizing start index with
  | zero =>
    by_cases h : index < w
    · cases hy : y.getLsbD start with
      | false => simp [mulBit, sumTree, partialRow, h, hy]
      | true =>
        simp only [mulBit, if_pos h, sumTree, partialRow, hy, if_true, Bool.true_and,
          BitVec.getLsbD_shiftLeft]
        by_cases hs : start ≤ index
        · simp [h, hs, Nat.not_lt_of_ge hs]
        · simp [hs, Nat.lt_of_not_ge hs]
    · rw [mulBit, if_neg h, BitVec.getLsbD_of_ge _ _ (by omega)]
  | succ height ih =>
    by_cases h : index < w
    · rw [mulBit, if_pos h, sumTree]
      have hLeft : mulBit w x.getLsbD y.getLsbD height start =
          (sumTree (partialRow x y) height start).getLsbD := funext (ih start)
      have hRight : mulBit w x.getLsbD y.getLsbD height (start + 2 ^ height) =
          (sumTree (partialRow x y) height (start + 2 ^ height)).getLsbD :=
        funext (ih (start + 2 ^ height))
      rw [hLeft, hRight, addBit_eq _ _ _ _ _ h (h.le.trans (Nat.lt_size_self w).le)]
      simp
    · rw [mulBit, if_neg h, BitVec.getLsbD_of_ge _ _ (by omega)]

theorem mulBit_eq {w : Nat} (x y : BitVec w) :
    mulBit w x.getLsbD y.getLsbD w.size 0 = (x * y).getLsbD := by
  rw [mulBit_tree_eq, sumTree_partialRow _ _ _ (Nat.lt_size_self w).le]

end Mathproof.MinimumGeneration.RankBerkowitz.BalancedWord
