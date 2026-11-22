import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace PCThreeRoutes

theorem cube_support {R ι : Type*} [CommRing R] [CharP R 3] [Fintype ι]
    (x w : ι → R) (unit_sum : ∑ i, w i * x i = 1)
    (minor : ∀ i j, i ≠ j → x i ^ 2 * x j ^ 2 = 0) :
    (∑ i, (w i * x i) ^ 3) = 1 ∧
    (∀ i, (w i * x i) ^ 3 * x i ^ 3 = x i ^ 3) ∧
    (∀ i, ((w i * x i) ^ 3) ^ 2 = (w i * x i) ^ 3) := by
  classical
  have total : (∑ i, (w i * x i) ^ 3) = 1 := by
    calc
      _ = (frobenius R 3) (∑ i, w i * x i) := (map_sum _ _ _).symm
      _ = 1 := by rw [unit_sum, map_one]
  have support (i : ι) : (w i * x i) ^ 3 * x i ^ 3 = x i ^ 3 := by
    calc
      _ = ∑ j, (w j * x j) ^ 3 * x i ^ 3 := by
        symm
        apply Finset.sum_eq_single i
        · intro j _ hji
          calc
            _ = (x j ^ 2 * x i ^ 2) * (w j ^ 3 * x j * x i) := by ring
            _ = 0 := by rw [minor j i hji, zero_mul]
        · simp
      _ = x i ^ 3 := by rw [← Finset.sum_mul, total, one_mul]
  refine ⟨total, support, ?_⟩
  intro i
  calc
    _ = w i ^ 3 * ((w i * x i) ^ 3 * x i ^ 3) := by ring
    _ = (w i * x i) ^ 3 := by rw [support, mul_pow]

end PCThreeRoutes
