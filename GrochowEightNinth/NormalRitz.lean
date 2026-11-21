import Mathlib.Tactic

open scoped BigOperators

namespace NormalRitz

theorem pairSumDeterminant {ι : Type*} (s : Finset ι) (w x y : ι → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) * (y i - y j)) =
    2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i * y i) -
        (∑ i ∈ s, w i * x i) * (∑ i ∈ s, w i * y i)) := by
  classical
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (w i * (w j * x j * y j) + (w i * x i * y i) * w j -
          (w i * x i) * (w j * y j) - (w i * y i) * (w j * x j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem discriminantScale (a b v : ℂ) (nonzero : v ≠ 0) :
    ((a / v) ^ 2 - 4 * (b / v)) * v ^ 2 = a ^ 2 - 4 * b * v := by
  field_simp

#print axioms pairSumDeterminant
#print axioms discriminantScale

end NormalRitz
