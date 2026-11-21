import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

/-- Expanding edge weights agrees with independently contracting each pair of boundary legs. -/
theorem expandCrossingWeights {E I K : Type*} [Fintype E] [DecidableEq E]
    [Fintype I] [CommSemiring K] (left right : E → I → K) (bridge : E → I → I → K) :
    (∏ e, ∑ i, ∑ j, left e i * bridge e i j * right e j) =
      ∑ a : E → I, ∑ b : E → I, ∏ e, left e (a e) * bridge e (a e) (b e) * right e (b e) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact Fintype.prod_sum (fun e j => left e (a e) * bridge e (a e) j * right e j)
