import EvenP1RectTail

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open Matrix
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp)
open Mathproof.EvenTI.Reciprocal.Part1 (coefficientRank uniformFraction_coefficientRank_le)

variable {K I B L : Type*} [Field K] [Fintype K]
  [Fintype I] [DecidableEq I] [Fintype B] [Fintype L]

/-- The checked rectangular tail charges both the low-coefficient-rank
event and the subsequent annihilation event at the same square-cut scale. -/
theorem square_cut_coefficient_failure (Z : Matrix I I K) (hZ : ∀ c : K, Z ≠ c • 1)
    (hb : 0 < Fintype.card L) (hs : 5 * Fintype.card L ≤ Fintype.card B) :
    uniformFraction (L → Matrix I B K) (fun U => coefficientRank Z U < Fintype.card L / 2) ≤
      1 / (Fintype.card K : ℝ) ^ (Fintype.card L * (Fintype.card L / 2)) := by
  classical
  let b := Fintype.card L
  let r := b/2
  let n := Fintype.card B
  have hr : r ≤ b := by dsimp [r]; omega
  have hbr : b+r ≤ n := by omega
  have htail := uniformFraction_coefficientRank_le Z hZ r hr hbr
  have hsmall : uniformFraction (L → Matrix I B K) (fun U => coefficientRank Z U < r) ≤
      uniformFraction (L → Matrix I B K) (fun U => coefficientRank Z U ≤ r) :=
    uniformFraction_le_of_imp (fun _ h => Nat.le_of_lt h)
  let e := (b-r)*(n-b-r)
  have h₁ : b*r ≤ (b-r)*b := by
    rw [Nat.mul_comm b r]
    exact Nat.mul_le_mul_right b (by dsimp [r]; omega)
  have h₂ : b ≤ (b-r)*b := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right b (show 1 ≤ b-r by dsimp [r]; omega)
  have h₃ : (b-r)*(b+b) ≤ e :=
    Nat.mul_le_mul_left _ (by dsimp [n, r, b] at *; omega)
  have he : b + b*r ≤ e := by rw [Nat.mul_add] at h₃; omega
  have hq : (2 : ℝ) ≤ Fintype.card K := by
    have hk : 2 ≤ Fintype.card K := Nat.succ_le_of_lt (Fintype.one_lt_card (α := K))
    exact_mod_cast hk
  have hbound : (2 : ℝ)^b / (Fintype.card K : ℝ)^e ≤
      1 / (Fintype.card K : ℝ)^(b*r) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul]
    calc
      _ ≤ (Fintype.card K : ℝ)^b * (Fintype.card K : ℝ)^(b*r) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hq _) (by positivity)
      _ = (Fintype.card K : ℝ)^(b+b*r) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) he
  exact hsmall.trans (htail.trans hbound)

#print axioms square_cut_coefficient_failure

end Mathproof.EvenTI.Reciprocal.SquareLow
