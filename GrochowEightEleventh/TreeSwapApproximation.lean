import Mathlib.Tactic

namespace TreeSwapApproximation

theorem swapBeatsBaseline (err tail added removed steps rank : ℝ)
    (nonneg : 0 ≤ err) (rank_pos : 0 < rank) (steps_ge_one : 1 ≤ steps)
    (tail_bound : tail ≤ err) (cost_bound : added ≤ 2 * (err / (8 * rank)))
    (removed_bound : 3 * (err / (8 * rank)) ≤ removed) :
    tail + added + steps * (err - removed) ≤
      (steps + 1) * err - err / (8 * rank) := by
  have hnon : 0 ≤ removed :=
    le_trans (by positivity) removed_bound
  have hmul := mul_le_mul_of_nonneg_right steps_ge_one hnon
  linarith only [tail_bound, cost_bound, removed_bound, hmul]

#print axioms swapBeatsBaseline

end TreeSwapApproximation
