import EvenP3RecipHighPrimal

namespace Mathproof.EvenTI.Reciprocal.Four

abbrev highBatches : ℕ := 10000000
abbrev highPrimalSize : ℕ := 10000000000
abbrev highBatchWidth (n : ℕ) : ℕ := n / 50000000
abbrev highDualSize (n : ℕ) : ℕ := highBatches * highBatchWidth n
abbrev highColumns (n : ℕ) : ℕ := n / 40000000
abbrev highRows (n : ℕ) : ℕ := n - 1 - highColumns n
abbrev highDefect (n : ℕ) : ℕ := n / 8000000
abbrev highRowRank (n : ℕ) : ℕ := 90 * n
abbrev highRelationRank (n : ℕ) : ℕ := highBatchWidth n * highPrimalSize + n^2 / 2000000
abbrev highCutoff (n : ℕ) : ℕ := n^2 / 1000000
abbrev highExponent (n : ℕ) : ℕ := n / 16000000

structure HighBudgets (n : ℕ) : Prop where
  primalEmbed : highPrimalSize ≤ n / 2
  dualEmbed : highDualSize n ≤ n / 2
  groupCard : highColumns n + highRows n = n - 1
  conditionLaw : highDualSize n * (n - 1) + highPrimalSize + 1 ≤ n^2
  relRank : highRelationRank n + highPrimalSize + 2 * (n * highDefect n) ≤ highCutoff n
  rowRank : highRowRank n + highPrimalSize ≤ highBatchWidth n * highPrimalSize
  physicalRank : 5 * n^2 ≤ highColumns n * highDualSize n * highPrimalSize
  primalExponent : highPrimalSize + highExponent n ≤ highDefect n
  colExponent : n^2 + highColumns n * highPrimalSize + highExponent n ≤ highBatches * (n^2 / 2000000)
  rowExponent : n^2 + highColumns n * highDualSize n * highPrimalSize + highExponent n ≤ highRows n * highRowRank n

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
/-- A concrete choice of all group sizes and exponents needed for the
square-cut high-label estimate. -/
theorem high_budgets (n : ℕ) (hn : 10^19 ≤ n) : HighBudgets n := by
  let a := highBatchWidth n
  let c := highColumns n
  let d := highDefect n
  let g := highRows n
  let x := highExponent n
  have hn' : 10000000000000000000 ≤ n := hn
  have haU : 50000000 * a ≤ n := by dsimp only [a, highBatchWidth]; omega
  have haL : n ≤ 100000000 * a := by dsimp only [a, highBatchWidth]; omega
  have hcU : 40000000 * c ≤ n := by dsimp only [c, highColumns]; omega
  have hcL : n ≤ 80000000 * c := by dsimp only [c, highColumns]; omega
  have hdU : 8000000 * d ≤ n := by dsimp only [d, highDefect]; omega
  have hg : 10 * g ≥ 9 * n := by dsimp only [g, highRows, highColumns]; omega
  have hPW : 10000000000000000000 * n ≤ n^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right n hn'
  have hnd : 8000000 * (n*d) ≤ n^2 := by
    calc
      _ = n*(8000000*d) := by ring
      _ ≤ n*n := Nat.mul_le_mul_left n hdU
      _ = _ := (pow_two n).symm
  have hcaL : n^2 ≤ 8000000000000000 * (c*a) := by
    calc
      _ = n*n := pow_two n
      _ ≤ (80000000*c)*(100000000*a) := Nat.mul_le_mul hcL haL
      _ = _ := by ring
  have hcaU : 2000000000000000 * (c*a) ≤ n^2 := by
    calc
      _ = (40000000*c)*(50000000*a) := by ring
      _ ≤ n*n := Nat.mul_le_mul hcU haU
      _ = _ := (pow_two n).symm
  have hgn : 10 * (g*n) ≥ 9 * n^2 := by
    simpa only [pow_two, mul_assoc] using Nat.mul_le_mul_right n hg
  have han : 50000000 * (a*n) ≤ n^2 := by
    simpa only [pow_two, mul_assoc] using Nat.mul_le_mul_right n haU
  have hsub : a * (n-1) ≤ a*n := Nat.mul_le_mul_left a (Nat.sub_le _ _)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (by omega : 10000000000 ≤ n / 2)
  · change 10000000 * a ≤ n / 2
    omega
  · change c + g = n - 1
    dsimp only [g, highRows, c, highColumns]
    omega
  · change (10000000*a) * (n-1) + 10000000000 + 1 ≤ n^2
    rw [mul_assoc]
    omega
  · change a*10000000000 + n^2/2000000 + 10000000000 + 2*(n*d) ≤ n^2/1000000
    omega
  · change 90*n + 10000000000 ≤ a*10000000000
    omega
  · change 5*n^2 ≤ c * (10000000*a) * 10000000000
    rw [show c*(10000000*a)*10000000000 = 100000000000000000*(c*a) by ring]
    omega
  · change 10000000000 + n/16000000 ≤ n/8000000
    omega
  · change n^2 + c*10000000000 + n/16000000 ≤ 10000000 * (n^2/2000000)
    omega
  · change n^2 + c * (10000000*a) * 10000000000 + n/16000000 ≤ g * (90*n)
    rw [show c*(10000000*a)*10000000000 = 100000000000000000*(c*a) by ring,
      show g*(90*n) = 90*(g*n) by ring]
    omega

#print axioms high_budgets

end Mathproof.EvenTI.Reciprocal.Four