import EvenP14CRTLoop

namespace EvenTI.P14Recovery

open EvenTI.P12Compare

/-- Fifth-degree word-operation bound for the complete coordinate loop. -/
theorem recoverAllCoordinatesCost_le (M m n : ℕ) :
    recoverAllCoordinatesCost M m n ≤ 53000*(Nat.size M+m+2*n+2)^5 := by
  let X := Nat.size M+m+2*n+2
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hm : m+n+1 ≤ X := by dsimp [X]; omega
  have hn : n ≤ X := by dsimp [X]; omega
  have hx₂ : X^2 ≤ X^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hx₄ : 1 ≤ X^4 := one_le_pow₀ hX
  have hx₅ : 1 ≤ X^5 := one_le_pow₀ hX
  have hw := smithRecoverAndCommitCost_le M (m+n) n
  rw [show Nat.size M+(m+n)+n+2 = X by dsimp [X]; omega] at hw
  have hCopy := Nat.mul_le_mul hm hn
  rw [←pow_two X] at hCopy
  have hRound : recoverRoundCost M m n+54 ≤ 52104*X^4 := by unfold recoverRoundCost; omega
  have hTotal := Nat.mul_le_mul hRound hn
  rw [show 52104*X^4*X = 52104*X^5 by ring] at hTotal
  change recoverAllCoordinatesCost M m n ≤ 53000*X^5
  unfold recoverAllCoordinatesCost
  omega

#print axioms recoverAllCoordinatesCost_le

end EvenTI.P14Recovery
