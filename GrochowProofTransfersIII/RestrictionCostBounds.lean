import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

namespace ClassTwoIsomorphism

/-- The integer inequalities that bound the three costs at the chosen restriction scale.
The fourth power clears the quarter-powers in the tuple term. The squares clear the
half-powers in the generator and retained group restriction terms. -/
theorem restrictionCostBounds (n δ τ b : ℕ) (hδ : 1 ≤ δ) (hb : 1 ≤ b)
    (hScale : δ ^ 20 * b ^ 2 ≤ n) (hLength : τ ≤ 3 * δ ^ 2) :
    δ ^ 4 * (n * δ ^ 2) ^ 7 * τ * b ≤ 3 * n ^ 8 ∧
      δ ^ 2 * τ ^ 2 * (n * δ ^ 2) ^ 3 ≤ 9 * n ^ 4 ∧
      δ ^ 2 * τ ^ 2 * n ^ 3 * δ ^ 14 * b ^ 2 ≤ 9 * n ^ 4 := by
  have hbSquare : b ≤ b ^ 2 := by
    calc
      b = b * 1 := (Nat.mul_one b).symm
      _ ≤ b * b := Nat.mul_le_mul_left b hb
      _ = b ^ 2 := by ring
  have hbTwo : 1 ≤ b ^ 2 := le_trans hb hbSquare
  have hδPow : 1 ≤ δ ^ 8 := by
    calc
      1 = (1 : ℕ) ^ 8 := by decide
      _ ≤ δ ^ 8 := Nat.pow_le_pow_left hδ 8
  have hLengthSquare : τ ^ 2 ≤ (3 * δ ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hLength 2
  have hMiddle : δ ^ 12 ≤ n := by
    calc
      δ ^ 12 = δ ^ 12 * 1 := (Nat.mul_one _).symm
      _ ≤ δ ^ 12 * δ ^ 8 := Nat.mul_le_mul_left _ hδPow
      _ = δ ^ 20 := by ring
      _ = δ ^ 20 * 1 := (Nat.mul_one _).symm
      _ ≤ δ ^ 20 * b ^ 2 := Nat.mul_le_mul_left _ hbTwo
      _ ≤ n := hScale
  constructor
  · calc
      δ ^ 4 * (n * δ ^ 2) ^ 7 * τ * b
          = (δ ^ 4 * (n * δ ^ 2) ^ 7 * b) * τ := by ring
      _ ≤ (δ ^ 4 * (n * δ ^ 2) ^ 7 * b) * (3 * δ ^ 2) :=
        Nat.mul_le_mul_left _ hLength
      _ = (3 * n ^ 7 * δ ^ 20) * b := by ring
      _ ≤ (3 * n ^ 7 * δ ^ 20) * b ^ 2 := Nat.mul_le_mul_left _ hbSquare
      _ = (3 * n ^ 7) * (δ ^ 20 * b ^ 2) := by ring
      _ ≤ (3 * n ^ 7) * n := Nat.mul_le_mul_left _ hScale
      _ = 3 * n ^ 8 := by ring
  constructor
  · calc
      δ ^ 2 * τ ^ 2 * (n * δ ^ 2) ^ 3
          = (δ ^ 2 * (n * δ ^ 2) ^ 3) * τ ^ 2 := by ring
      _ ≤ (δ ^ 2 * (n * δ ^ 2) ^ 3) * (3 * δ ^ 2) ^ 2 :=
        Nat.mul_le_mul_left _ hLengthSquare
      _ = (9 * n ^ 3) * δ ^ 12 := by ring
      _ ≤ (9 * n ^ 3) * n := Nat.mul_le_mul_left _ hMiddle
      _ = 9 * n ^ 4 := by ring
  · calc
      δ ^ 2 * τ ^ 2 * n ^ 3 * δ ^ 14 * b ^ 2
          = (δ ^ 2 * n ^ 3 * δ ^ 14 * b ^ 2) * τ ^ 2 := by ring
      _ ≤ (δ ^ 2 * n ^ 3 * δ ^ 14 * b ^ 2) * (3 * δ ^ 2) ^ 2 :=
        Nat.mul_le_mul_left _ hLengthSquare
      _ = (9 * n ^ 3) * (δ ^ 20 * b ^ 2) := by ring
      _ ≤ (9 * n ^ 3) * n := Nat.mul_le_mul_left _ hScale
      _ = 9 * n ^ 4 := by ring

end ClassTwoIsomorphism

#print axioms ClassTwoIsomorphism.restrictionCostBounds
