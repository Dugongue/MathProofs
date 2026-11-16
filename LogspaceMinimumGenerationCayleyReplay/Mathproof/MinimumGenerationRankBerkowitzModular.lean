import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise

/-!
Modular multiplication using a prepared reciprocal and a fixed-width shift.
Preparing the reciprocal is independent of the two live operands.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.Modular

def reduce (modulus width reciprocal value : Nat) : Nat :=
  let estimate := (value * reciprocal) >>> width
  let residual := value - estimate * modulus
  if modulus ≤ residual then residual - modulus else residual

private theorem estimate_bounds {modulus base value : Nat} (hm : 0 < modulus)
    (hx : value < base) :
    let estimate := (value * (base / modulus)) / base
    estimate ≤ value / modulus ∧ value / modulus ≤ estimate + 1 := by
  let reciprocal := base / modulus
  let estimate := (value * reciprocal) / base
  change estimate ≤ value / modulus ∧ value / modulus ≤ estimate + 1
  have hb : 0 < base := by omega
  have hReciprocal : reciprocal * modulus ≤ base := Nat.div_mul_le_self _ _
  have hLower : estimate * modulus * base ≤ value * base := calc
    _ = estimate * base * modulus := by ac_rfl
    _ ≤ (value * reciprocal) * modulus :=
      Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ = value * (reciprocal * modulus) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ hReciprocal
  refine ⟨(Nat.le_div_iff_mul_le hm).mpr (Nat.le_of_mul_le_mul_right hLower hb), ?_⟩
  have hEstimate : value * reciprocal < (estimate + 1) * base := calc
    _ < base * (estimate + 1) := Nat.lt_mul_div_succ _ hb
    _ = _ := Nat.mul_comm _ _
  have hSmallRemainder : value * (base % modulus) < base * modulus :=
    (Nat.mul_le_mul_left _ (Nat.mod_lt _ hm).le).trans_lt
      (Nat.mul_lt_mul_of_pos_right hx hm)
  have hSplit : value * base = value * (modulus * reciprocal + base % modulus) :=
    congrArg (value * ·) (Nat.div_add_mod base modulus).symm
  have hUpper : value * base < ((estimate + 2) * modulus) * base := calc
    _ = value * reciprocal * modulus + value * (base % modulus) := by
      rw [hSplit]
      ring
    _ < ((estimate + 1) * base) * modulus + base * modulus :=
      Nat.add_lt_add (Nat.mul_lt_mul_of_pos_right hEstimate hm) hSmallRemainder
    _ = _ := by ring
  have hDiv := (Nat.div_lt_iff_lt_mul hm).mpr (Nat.lt_of_mul_lt_mul_right hUpper)
  omega

theorem reduce_eq_mod {modulus width value : Nat} (hm : 0 < modulus)
    (hx : value < 2 ^ width) :
    reduce modulus width (2 ^ width / modulus) value = value % modulus := by
  let estimate := (value * (2 ^ width / modulus)) / 2 ^ width
  obtain ⟨hLower, hUpper⟩ := estimate_bounds hm hx
  change estimate ≤ value / modulus at hLower
  change value / modulus ≤ estimate + 1 at hUpper
  simp only [reduce, Nat.shiftRight_eq_div_pow]
  change (if modulus ≤ value - estimate * modulus then value - estimate * modulus - modulus
    else value - estimate * modulus) = value % modulus
  have hSplit := Nat.div_add_mod' value modulus
  have hMul := Nat.mul_le_mul_right modulus hLower
  have hResidual : value - estimate * modulus =
      (value / modulus - estimate) * modulus + value % modulus := by
    rw [Nat.sub_mul]
    omega
  rw [hResidual]
  have hDifference : value / modulus - estimate = 0 ∨ value / modulus - estimate = 1 := by
    omega
  rcases hDifference with h | h <;> rw [h]
  · simp [Nat.not_le_of_gt (Nat.mod_lt _ hm)]
  · simp

theorem mul_reduce_eq_mod {modulus width x y : Nat} (hm : 0 < modulus)
    (hw : modulus ≤ 2 ^ width) (hx : x < modulus) (hy : y < modulus) :
    reduce modulus (width + width) (2 ^ (width + width) / modulus) (x * y) =
      (x * y) % modulus := by
  apply reduce_eq_mod hm
  rw [pow_add]
  exact (Nat.mul_le_mul_left _ (hy.le.trans hw)).trans_lt
    (Nat.mul_lt_mul_of_pos_right (hx.trans_le hw) (Nat.two_pow_pos width))

end Mathproof.MinimumGeneration.RankBerkowitz.Modular
