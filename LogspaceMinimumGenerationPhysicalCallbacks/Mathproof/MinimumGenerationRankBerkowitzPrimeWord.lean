import Mathlib.Data.ZMod.Basic
import Mathproof.MinimumGenerationRankBerkowitzBalancedWord
import Mathproof.MinimumGenerationRankBerkowitzColumnProduct
import Mathproof.MinimumGenerationRankBerkowitzModular

/-!
Bit-stream Barrett reduction. The modulus and reciprocal are read-only inputs.
Each arithmetic stage asks for a bit of the preceding stage as needed.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.PrimeWord

open BalancedWord

def wordBits (width : Nat) (source : Nat → Bool) (index : Nat) : Bool :=
  decide (index < width) && source index

private theorem wordBits_eq (width x : Nat) :
    wordBits width x.testBit = (BitVec.ofNat width x).getLsbD := by
  funext index
  rw [BitVec.getLsbD_ofNat]
  rfl

private theorem wordBits_not_eq (width x : Nat) :
    wordBits width (fun i => !x.testBit i) = (~~~(BitVec.ofNat width x)).getLsbD := by
  funext index
  rw [BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
  by_cases h : index < width <;> simp [wordBits, h]

def subtractBit (width : Nat) (left right : Nat → Bool) (index : Nat) : Bool :=
  if index < width then
    addBit width.size index (wordBits width left) (wordBits width fun i => !right i) true
  else false

theorem subtractBit_eq {width x y index : Nat} (hx : x < 2^width) (hxy : y ≤ x) :
    subtractBit width x.testBit y.testBit index = (x-y).testBit index := by
  have hy : y < 2^width := hxy.trans_lt hx
  have hX : (BitVec.ofNat width x).toNat = x := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  have hY : (BitVec.ofNat width y).toNat = y := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy]
  have hLe : BitVec.ofNat width y ≤ BitVec.ofNat width x := by
    rwa [BitVec.le_def, hY, hX]
  by_cases h : index < width
  · rw [subtractBit, if_pos h, wordBits_eq, wordBits_not_eq,
      addBit_eq _ _ _ _ _ h (h.le.trans (Nat.lt_size_self width).le)]
    have hOne : (BitVec.ofBool true).setWidth width = BitVec.ofNat width 1 := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth]
    rw [hOne, BitVec.add_assoc, ← BitVec.neg_eq_not_add, ← BitVec.sub_eq_add_neg]
    change ((BitVec.ofNat width x - BitVec.ofNat width y).toNat).testBit index =
      (x-y).testBit index
    rw [BitVec.toNat_sub_of_le hLe, hX, hY]
  · have hBound : x-y < 2^index :=
      (Nat.sub_le x y).trans_lt (hx.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [subtractBit, if_neg h, Nat.testBit_eq_false_of_lt hBound]

def lessThan (width : Nat) (left right : Nat → Bool) : Bool :=
  !(carryBit width.size width (wordBits width left) (wordBits width fun i => !right i) true)

theorem lessThan_eq {width x y : Nat} (hx : x < 2^width) (hy : y < 2^width) :
    lessThan width x.testBit y.testBit = decide (x < y) := by
  rw [lessThan, wordBits_eq, wordBits_not_eq, compareBit_eq _ _ _ (Nat.lt_size_self width).le]
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

private def shiftedProduct (width : Nat) (left right : Nat → Bool) (index : Nat) : Bool :=
  ColumnProduct.outputBit left right (width + index)

private theorem shiftedProduct_eq (width x y : Nat) :
    shiftedProduct width x.testBit y.testBit = ((x*y) >>> width).testBit := by
  funext index
  rw [shiftedProduct, ColumnProduct.outputBit_eq, Nat.testBit_shiftRight]

/-- Reduce a value below 2^width. Reciprocal encodes floor(2^width/modulus). -/
def reduceBit (width : Nat) (modulus reciprocal input : Nat → Bool) (index : Nat) : Bool :=
  let estimate := shiftedProduct width input reciprocal
  let penalty := ColumnProduct.outputBit estimate modulus
  let residual := subtractBit (width+1) input penalty
  if lessThan (width+1) residual modulus then residual index
  else subtractBit (width+1) residual modulus index

private theorem estimate_mul_le (width modulus value : Nat) :
    ((value * (2^width / modulus)) >>> width) * modulus ≤ value := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos width)
  calc
    _ = ((value * (2^width / modulus)) / 2^width * 2^width) * modulus := by ac_rfl
    _ ≤ (value * (2^width / modulus)) * modulus :=
      Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ = value * ((2^width / modulus) * modulus) := Nat.mul_assoc _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)

theorem reduceBit_eq {width modulus value index : Nat} (hm : 0 < modulus)
    (hModulus : modulus < 2^(width+1)) (hValue : value < 2^width) :
    reduceBit width modulus.testBit (2^width / modulus).testBit value.testBit index =
      (value % modulus).testBit index := by
  let estimate := (value * (2^width / modulus)) >>> width
  let residual := value - estimate * modulus
  have hBound : value < 2^(width+1) := hValue.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hEstimate : estimate * modulus ≤ value := estimate_mul_le _ _ _
  have hResidualBound : residual < 2^(width+1) := (Nat.sub_le _ _).trans_lt hBound
  have hPenalty : ColumnProduct.outputBit estimate.testBit modulus.testBit =
      (estimate * modulus).testBit := funext (ColumnProduct.outputBit_eq _ _)
  have hResidual : subtractBit (width+1) value.testBit (estimate * modulus).testBit =
      residual.testBit := funext fun _ => subtractBit_eq hBound hEstimate
  have hReduce := Modular.reduce_eq_mod hm hValue
  change (if modulus ≤ residual then residual - modulus else residual) = value % modulus
    at hReduce
  unfold reduceBit
  dsimp only
  rw [shiftedProduct_eq, show ((value*(2^width/modulus)) >>> width) = estimate from rfl,
    hPenalty, hResidual, lessThan_eq hResidualBound hModulus]
  by_cases hLess : residual < modulus
  · have hNot := Nat.not_le_of_gt hLess
    rw [if_neg hNot] at hReduce
    simp only [hLess, decide_true, if_true]
    rw [hReduce]
  · have hLe := Nat.le_of_not_gt hLess
    rw [if_pos hLe] at hReduce
    simp only [hLess, decide_false, Bool.false_eq_true, if_false]
    rw [subtractBit_eq hResidualBound hLe, hReduce]

def multiplyModBit (width : Nat) (modulus reciprocal left right : Nat → Bool) (index : Nat) : Bool :=
  reduceBit (width+width) modulus reciprocal (ColumnProduct.outputBit left right) index

theorem multiplyModBit_eq {width modulus x y index : Nat} (hm : 0 < modulus)
    (hWidth : modulus ≤ 2^width) (hx : x < modulus) (hy : y < modulus) :
    multiplyModBit width modulus.testBit (2^(width+width)/modulus).testBit x.testBit y.testBit index =
      (x*y % modulus).testBit index := by
  unfold multiplyModBit
  rw [show ColumnProduct.outputBit x.testBit y.testBit = (x*y).testBit from
    funext (ColumnProduct.outputBit_eq x y)]
  apply reduceBit_eq hm
  · have hWide : 2^width ≤ 2^(width+width) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ]
    have hPos := Nat.two_pow_pos (width+width)
    omega
  · rw [pow_add]
    exact (Nat.mul_le_mul_left _ (hy.le.trans hWidth)).trans_lt
      (Nat.mul_lt_mul_of_pos_right (hx.trans_le hWidth) (Nat.two_pow_pos width))

def addBits (width : Nat) (left right : Nat → Bool) (index : Nat) : Bool :=
  if index < width then
    addBit width.size index (wordBits width left) (wordBits width right) false
  else false

theorem addBits_eq {width x y index : Nat} (hSum : x+y < 2^width) :
    addBits width x.testBit y.testBit index = (x+y).testBit index := by
  have hx : x < 2^width := by omega
  have hy : y < 2^width := by omega
  have hValue : (BitVec.ofNat width x + BitVec.ofNat width y).toNat = x+y := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
      Nat.mod_eq_of_lt hSum]
  by_cases h : index < width
  · rw [addBits, if_pos h, wordBits_eq, wordBits_eq,
      addBit_eq _ _ _ _ _ h (h.le.trans (Nat.lt_size_self width).le)]
    simp [BitVec.getLsbD, hValue]
  · have hBound : x+y < 2^index :=
      hSum.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    rw [addBits, if_neg h, Nat.testBit_eq_false_of_lt hBound]

def addModBit (width : Nat) (modulus left right : Nat → Bool) (index : Nat) : Bool :=
  let total := addBits (width+1) left right
  if lessThan (width+1) total modulus then total index
  else subtractBit (width+1) total modulus index

theorem addModBit_eq {width modulus x y index : Nat} (hWidth : modulus ≤ 2^width)
    (hx : x < modulus) (hy : y ≤ modulus) :
    addModBit width modulus.testBit x.testBit y.testBit index = ((x+y)%modulus).testBit index := by
  have hSum : x+y < 2^(width+1) := by rw [pow_succ]; omega
  have hp : modulus < 2^(width+1) := by
    rw [pow_succ]
    have hPow := Nat.two_pow_pos width
    omega
  unfold addModBit
  dsimp only
  rw [show addBits (width+1) x.testBit y.testBit = (x+y).testBit from
    funext fun _ => addBits_eq hSum, lessThan_eq hSum hp]
  by_cases h : x+y < modulus
  · simp only [h, decide_true, if_true, Nat.mod_eq_of_lt h]
  · have hLe : modulus ≤ x+y := by omega
    have hSub : x+y-modulus < modulus := by omega
    simp only [h, decide_false, Bool.false_eq_true, if_false]
    rw [subtractBit_eq hSum hLe, Nat.mod_eq_sub_mod hLe, Nat.mod_eq_of_lt hSub]

def subtractModBit (width : Nat) (modulus left right : Nat → Bool) (index : Nat) : Bool :=
  addModBit width modulus left (subtractBit (width+1) modulus right) index

theorem subtractModBit_eq {width modulus x y index : Nat} (hWidth : modulus ≤ 2^width)
    (hx : x < modulus) (hy : y ≤ modulus) :
    subtractModBit width modulus.testBit x.testBit y.testBit index =
      ((x+(modulus-y))%modulus).testBit index := by
  have hp : modulus < 2^(width+1) := by
    rw [pow_succ]
    have hPow := Nat.two_pow_pos width
    omega
  rw [subtractModBit, show subtractBit (width+1) modulus.testBit y.testBit = (modulus-y).testBit
    from funext fun _ => subtractBit_eq hp hy]
  exact addModBit_eq hWidth hx (Nat.sub_le _ _)

theorem multiplyModBit_zmod {width p index : Nat} [NeZero p] (hWidth : p ≤ 2^width)
    (x y : ZMod p) :
    multiplyModBit width p.testBit (2^(width+width)/p).testBit x.val.testBit y.val.testBit index =
      (x*y).val.testBit index := by
  rw [ZMod.val_mul]
  exact multiplyModBit_eq (Nat.pos_of_ne_zero (NeZero.ne p)) hWidth x.val_lt y.val_lt

theorem addModBit_zmod {width p index : Nat} [NeZero p] (hWidth : p ≤ 2^width)
    (x y : ZMod p) :
    addModBit width p.testBit x.val.testBit y.val.testBit index = (x+y).val.testBit index := by
  rw [ZMod.val_add]
  exact addModBit_eq hWidth x.val_lt y.val_lt.le


end Mathproof.MinimumGeneration.RankBerkowitz.PrimeWord
