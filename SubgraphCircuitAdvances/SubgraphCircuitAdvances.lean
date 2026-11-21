import Mathlib.Tactic

open scoped BigOperators

namespace SubgraphCircuitAdvances

theorem thresholdHitsTriple (a b c : ℚ) (h : 1 ≤ a + b + c) :
    (1 : ℚ) / 3 ≤ a ∨ (1 : ℚ) / 3 ≤ b ∨ (1 : ℚ) / 3 ≤ c := by
  by_contra! hn
  rcases hn with ⟨ha, hb, hc⟩
  linarith

theorem thresholdCardBound {V : Type*} [DecidableEq V] (vertices : Finset V)
    (weight : V → ℚ) (hn : ∀ v ∈ vertices, 0 ≤ weight v) :
    ((vertices.filter fun v => (1 : ℚ) / 3 ≤ weight v).card : ℚ) ≤
      3 * ∑ v ∈ vertices, weight v := by
  let chosen := vertices.filter fun v => (1 : ℚ) / 3 ≤ weight v
  have hlocal : (∑ v ∈ chosen, (1 : ℚ)) ≤ ∑ v ∈ chosen, 3 * weight v := by
    apply Finset.sum_le_sum
    intro v hv
    have h := (Finset.mem_filter.mp hv).2
    linarith
  have hsum : (∑ v ∈ chosen, weight v) ≤ ∑ v ∈ vertices, weight v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
      intro v hv _
      exact hn v hv)
  change (chosen.card : ℚ) ≤ 3 * ∑ v ∈ vertices, weight v
  calc
    (chosen.card : ℚ) = ∑ _v ∈ chosen, (1 : ℚ) := by simp
    _ ≤ ∑ v ∈ chosen, 3 * weight v := hlocal
    _ = 3 * ∑ v ∈ chosen, weight v := by rw [Finset.mul_sum]
    _ ≤ 3 * ∑ v ∈ vertices, weight v := by linarith

theorem signedPathSwitch {R : Type*} [CommRing R] (w : R) :
    w * 1 + w * (-1) = 0 ∧ w * (1 * 1) + w * (1 * (-1)) = 0 := by
  constructor <;> ring

theorem andPortWeights {R : Type*} [CommRing R] (w a b : R) :
    w - w * a - w * b + w * a * b = w * (1 - a) * (1 - b) := by
  ring

theorem disjointPortSum {R : Type*} [CommRing R] (a b c d e f : R) :
    a * e + a * f + b * d + b * f + c * d + c * e =
      (a + b + c) * (d + e + f) - (a * d + b * e + c * f) := by
  ring

def pairCompletionCount : ℕ → ℕ
  | 0 => 1
  | j + 1 => (2 * j + 1) * pairCompletionCount j

theorem pairCompletionCountOdd (j : ℕ) : pairCompletionCount j % 2 = 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h : (2 * j + 1) % 2 = 1 := by omega
    simp [pairCompletionCount, Nat.mul_mod, h, ih]

end SubgraphCircuitAdvances
