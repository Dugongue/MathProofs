import Mathproof.MinimumGenerationRankBerkowitzBitEvaluation
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring

namespace Mathproof.MinimumGeneration.RankBerkowitz.BitEvaluation

def rawCap (inputLength : Nat) : Nat :=
  (inputLength + 1).log2 + 1

def innerCap (inputLength : Nat) : Nat :=
  (rawCap inputLength).size + 1

private theorem pow_le_factorial_mul_two_pow (n degree : Nat) :
    n ^ degree ≤ degree.factorial * 2 ^ degree * 2 ^ n := by
  have h : n ≤ n + degree + 1 - degree := by omega
  calc
    n ^ degree ≤ (n + degree + 1 - degree) ^ degree := Nat.pow_le_pow_left h _
    _ ≤ (n + degree).descFactorial degree := Nat.pow_sub_le_descFactorial _ _
    _ = degree.factorial * (n + degree).choose degree :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    _ ≤ degree.factorial * 2 ^ (n + degree) :=
      Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = degree.factorial * 2 ^ degree * 2 ^ n := by
      rw [Nat.pow_add]
      ac_rfl

private theorem two_pow_innerCap_le (inputLength : Nat) :
    2 ^ innerCap inputLength ≤ 4 * rawCap inputLength := by
  let cap := rawCap inputLength
  have hcap : 0 < cap := Nat.succ_pos _
  have hs : 0 < cap.size := Nat.size_pos.mpr hcap
  have hp : 2 ^ (cap.size - 1) ≤ cap := Nat.lt_size.mp (by omega)
  change 2 ^ (cap.size + 1) ≤ 4 * cap
  rw [show cap.size + 1 = cap.size - 1 + 2 by omega, Nat.pow_add, Nat.mul_comm]
  exact Nat.mul_le_mul_left 4 hp

/-- A bound uniform in the input length, with an explicit constant for each
fixed polynomial in the logarithm of the raw-input workspace allowance. -/
theorem innerCap_pow_le (inputLength degree : Nat) :
    innerCap inputLength ^ degree ≤
      (4 * (degree.factorial * 2 ^ degree)) * rawCap inputLength := by
  calc
    _ ≤ degree.factorial * 2 ^ degree * 2 ^ innerCap inputLength :=
      pow_le_factorial_mul_two_pow _ _
    _ ≤ degree.factorial * 2 ^ degree * (4 * rawCap inputLength) :=
      Nat.mul_le_mul_left _ (two_pow_innerCap_le inputLength)
    _ = _ := by ac_rfl

def stackCoefficient (C degree : Nat) : Nat :=
  (2 * C * C) * (4 * ((degree + degree).factorial * 2 ^ (degree + degree)))

theorem stack_le_rawCap {inputLength depth addressWidth C degree : Nat}
    (hDepth : depth + 1 ≤ C * innerCap inputLength ^ degree)
    (hAddr : addressWidth + 1 ≤ C * innerCap inputLength ^ degree) :
    (depth + 1) * (2 + depth.size + addressWidth) ≤
      stackCoefficient C degree * rawCap inputLength := by
  have hSize : depth.size ≤ depth := Nat.size_le.mpr (show depth < 2 ^ depth from Nat.lt_two_pow_self)
  have hFrame : 2 + depth.size + addressWidth ≤
      2 * (C * innerCap inputLength ^ degree) := by omega
  calc
    _ ≤ (C * innerCap inputLength ^ degree) * (2 * (C * innerCap inputLength ^ degree)) :=
      Nat.mul_le_mul hDepth hFrame
    _ = (2 * C * C) * innerCap inputLength ^ (degree + degree) := by rw [Nat.pow_add]; ring
    _ ≤ (2 * C * C) * ((4 * ((degree + degree).factorial * 2 ^ (degree + degree))) *
        rawCap inputLength) := Nat.mul_le_mul_left _ (innerCap_pow_le _ _)
    _ = _ := by simp only [stackCoefficient, Nat.mul_assoc]

/-- Account for a bounded evaluator state and one independently bounded live
callback at every prefix. The callback is charged once while the entire
Boolean evaluation stack is parked. -/
theorem execute_total_with_callback_budget
    {inputLength addressWidth C degree callbackC : Nat}
    (circuit : Fin (2 ^ addressWidth) → Gate (Fin (2 ^ addressWidth)))
    (input : Fin (2 ^ addressWidth) → Bool) (level : Fin (2 ^ addressWidth) → Nat)
    (hLevel : ∀ addr left right, circuit addr = .nand left right →
      level left < level addr ∧ level right < level addr)
    (depth : Nat) (address : Fin (2 ^ addressWidth)) (hLevelDepth : level address ≤ depth)
    (hDepth : depth + 1 ≤ C * innerCap inputLength ^ degree)
    (hAddr : addressWidth + 1 ≤ C * innerCap inputLength ^ degree) :
    ∃ value, eval circuit input depth address = some value ∧
      Runs (step circuit input)
        (fun state => state.bounded depth depth ∧
          (state.encode (depth.size + 1)).length + callbackC * rawCap inputLength ≤
            (stackCoefficient C degree + callbackC) * rawCap inputLength)
        ⟨.query depth address, []⟩ ⟨.result value, []⟩ ∧
      step circuit input ⟨.result value, []⟩ = none := by
  obtain ⟨b, hb, hRun, hStop⟩ :=
    execute_total_encoded circuit input level hLevel depth address hLevelDepth
  refine ⟨b, hb, hRun.mono ?_, hStop⟩
  intro st hs
  refine ⟨hs.1, ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add_right (hs.2.trans (stack_le_rawCap hDepth hAddr)) _

end Mathproof.MinimumGeneration.RankBerkowitz.BitEvaluation
