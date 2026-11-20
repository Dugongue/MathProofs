import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

namespace GrochowRegularity

open scoped BigOperators

theorem implication_chain_certificate {R : Type*} [CommRing R] (x : ℕ → R) (n : ℕ) :
    (1 - x 0) + x n +
        (∑ i ∈ Finset.range n, (x i * (1 - x (i + 1)) - x (i + 1) * (1 - x i))) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        _ = (1 - x 0) + x n +
            (∑ i ∈ Finset.range n,
              (x i * (1 - x (i + 1)) - x (i + 1) * (1 - x i))) := by ring
        _ = 1 := ih

end GrochowRegularity

#print axioms GrochowRegularity.implication_chain_certificate
