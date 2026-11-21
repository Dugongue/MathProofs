import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace SquareZeroDirect

theorem incidence_potential {I J R : Type*} [Fintype I] [Fintype J] [CommSemiring R]
    (z : I → J → R) (a : I → R) (b : J → R)
    (row : ∀ i, ∑ j, z i j = 1) (col : ∀ j, ∑ i, z i j = 1) :
    (∑ i, ∑ j, z i j * (a i + b j)) = (∑ i, a i) + (∑ j, b j) := by
  classical
  calc
    _ = (∑ i, ∑ j, z i j * a i) + (∑ i, ∑ j, z i j * b j) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, z i j * a i) + (∑ j, ∑ i, z i j * b j) := by
      rw [Finset.sum_comm (f := fun i j => z i j * b j)]
    _ = (∑ i, a i) + (∑ j, b j) := by
      simp only [← Finset.sum_mul, row, col, one_mul]

end SquareZeroDirect
