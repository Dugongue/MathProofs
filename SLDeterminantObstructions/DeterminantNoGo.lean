import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Abs

namespace DeterminantNoGo

open scoped BigOperators

theorem nonzeroWinding_requires_weight {ι : Type*} (s : Finset ι)
    {n : ℤ} (hn : 0 < n) (quotient residue : ι → ℤ) (d : ℤ)
    (hbalance : n * (∑ i ∈ s, quotient i) = d - ∑ i ∈ s, residue i)
    (hwinding : (∑ i ∈ s, quotient i) ≠ 0) :
    n ≤ |d| + ∑ i ∈ s, |residue i| := by
  have hq : 1 ≤ |∑ i ∈ s, quotient i| := Int.one_le_abs hwinding
  have hsub : |d - ∑ i ∈ s, residue i| ≤ |d| + |∑ i ∈ s, residue i| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le d (-(∑ i ∈ s, residue i)))
  calc
    n = n * 1 := by simp
    _ ≤ n * |∑ i ∈ s, quotient i| := Int.mul_le_mul_of_nonneg_left hq hn.le
    _ = |n * ∑ i ∈ s, quotient i| := by rw [abs_mul, abs_of_pos hn]
    _ = |d - ∑ i ∈ s, residue i| := by rw [hbalance]
    _ ≤ |d| + |∑ i ∈ s, residue i| := hsub
    _ ≤ |d| + ∑ i ∈ s, |residue i| :=
      add_le_add (le_refl |d|) (Finset.abs_sum_le_sum_abs residue s)

end DeterminantNoGo
