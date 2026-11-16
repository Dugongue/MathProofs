import Mathproof.MinimumGenerationRankCoefficientBits
import Mathproof.MinimumGenerationRankSpace
import Mathlib.Tactic.Linarith

namespace Mathproof.MinimumGeneration.RankBerkowitz.Formula

open BitEvaluation

/-- The actual coefficient formula has depth polynomial in the double
logarithm of the ambient binary input when the column dimension is polylog. -/
theorem coefficientBudget_le_innerCap (L n exponent : Nat)
    (hn : n+1 ≤ rawCap L ^ exponent) :
    BitOperations.coefficientBudget n + 1 ≤ 11 * (exponent+2)^2 * innerCap L ^ 2 := by
  let cap := rawCap L
  have hv : (n+1).size ≤ exponent*cap.size+1 := by
    apply Nat.size_le.mpr
    calc
      n+1 ≤ cap ^ exponent := hn
      _ ≤ (2^cap.size)^exponent := Nat.pow_le_pow_left (Nat.lt_size_self cap).le _
      _ = 2^(exponent*cap.size) := by rw [← pow_mul,Nat.mul_comm]
      _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  let m := (n+1).size
  have hm : n.size ≤ m := Nat.size_le_size (Nat.le_succ n)
  have hmul : n.size*(n.size+1) ≤ m*(m+1) := Nat.mul_le_mul hm (Nat.add_le_add_right hm 1)
  have hprod : n.size*(m+1) ≤ m*(m+1) := Nat.mul_le_mul_right _ hm
  have hSize : m+1 ≤ (exponent+2)*innerCap L := by
    unfold innerCap
    change m+1 ≤ (exponent+2)*(cap.size+1)
    change m ≤ exponent*cap.size+1 at hv
    nlinarith
  calc
    _ ≤ 11*(m+1)^2 := by unfold BitOperations.coefficientBudget factorDepth; nlinarith
    _ ≤ 11*((exponent+2)*innerCap L)^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSize _)
    _ = _ := by ring

theorem coefficientAddress_le_innerCap (L n exponent : Nat)
    (hn : n+1 ≤ rawCap L ^ exponent) (d : Fin (n+1)) (path : List Bool)
    (tag : Node) (h : coefficientNode n d path = some tag) :
    path.length + 1 ≤ 11*(exponent+2)^2*innerCap L ^ 2 := by
  have hp := coefficientNode_path_bound n d path tag h
  exact (Nat.add_le_add_right hp 1).trans (coefficientBudget_le_innerCap L n exponent hn)

end Mathproof.MinimumGeneration.RankBerkowitz.Formula
