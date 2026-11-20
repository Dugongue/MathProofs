import Mathlib.Tactic.Ring

namespace Mathproof.EvenTI.Reciprocal.Next

/-- Enough retained blocks for the target Fourier rank on each nontrivial label. -/
theorem reciprocal_rank_arithmetic (n : Nat) (hn : 8 ≤ n) :
    4 * n ^ 2 ≤ ((n - 1) ^ 2 - 1) * (n - 2) := by
  let z := n - 2
  have hzn : n = z + 2 := by dsimp [z]; omega
  have hz : 6 ≤ z := by omega
  have hsub : (n - 1) ^ 2 - 1 = n * z := by
    apply Nat.sub_eq_of_eq_add
    rw [show n - 1 = z + 1 by omega, hzn]
    ring
  have hzmul := Nat.mul_le_mul_right z hz
  have hzlinear : 4 * n ≤ 6 * z := by omega
  calc
    _ = n * (4 * n) := by ring
    _ ≤ n * (z * z) := Nat.mul_le_mul_left _ (hzlinear.trans hzmul)
    _ = _ := by rw [hsub, ← mul_assoc]

#print axioms reciprocal_rank_arithmetic

end Mathproof.EvenTI.Reciprocal.Next
