import Mathlib.Algebra.BigOperators.Ring.Finset

namespace QPFTINext

theorem averaged_generalized_inverse {R : Type*} [Ring R] {ι : Type*}
    (s : Finset ι) (a c : R) (b : ι → R) (h : ∀ i ∈ s, a * b i * a = c) :
    a * (∑ i ∈ s, b i) * a = (s.card : R) * c := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl h]
  simp

end QPFTINext
