import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace PCThreeRoutes

theorem pure_pivot {R ι : Type*} [CommRing R] [Fintype ι]
    (x coeff : ι → R) (a b : ι) (inv : R) (unit : inv * coeff a = 1)
    (mixed : (∑ j, coeff j * x j) * (x a ^ 2 * x b) = 0)
    (private_minor : ∀ j, j ≠ a → (x a ^ 2 * x b) * x j = 0) :
    x a ^ 3 * x b = 0 := by
  classical
  have isolate : (∑ j, coeff j * x j) * (x a ^ 2 * x b) =
      (coeff a * x a) * (x a ^ 2 * x b) := by
    rw [Finset.sum_mul]
    apply Finset.sum_eq_single a
    · intro j _ hj
      calc
        _ = coeff j * ((x a ^ 2 * x b) * x j) := by ring
        _ = 0 := by rw [private_minor j hj, mul_zero]
    · simp
  calc
    _ = (inv * coeff a) * (x a ^ 3 * x b) := by rw [unit, one_mul]
    _ = inv * ((coeff a * x a) * (x a ^ 2 * x b)) := by ring
    _ = 0 := by rw [← isolate, mixed, mul_zero]

theorem rank_three_collision {R ι : Type*} [CommRing R] [Fintype ι]
    (x : ι → R) (w : ι → ι → ι → R) (marked : ι → Prop)
    (unit_cover : (∑ a, ∑ b, ∑ c, w a b c * (x a * x b * x c)) = 1)
    (four : ∀ i j a b, i ≠ j → a ≠ b → (x i * x j) * (x a * x b) = 0)
    (pure : ∀ a, ¬marked a → w a a a = 0)
    (pivot : ∀ a b, marked a → a ≠ b → x a ^ 3 * x b = 0)
    (i j : ι) (different : i ≠ j) : x i * x j = 0 := by
  classical
  have term (a b c : ι) : (x i * x j) * (w a b c * (x a * x b * x c)) = 0 := by
    by_cases hab : a = b
    · subst b
      by_cases hac : a = c
      · subst c
        by_cases hm : marked a
        · by_cases hai : a = i
          · subst i
            calc
              _ = (x a ^ 3 * x j) * (w a a a * x a) := by ring
              _ = 0 := by rw [pivot a j hm different, zero_mul]
          · calc
              _ = (x a ^ 3 * x i) * (w a a a * x j) := by ring
              _ = 0 := by rw [pivot a i hm hai, zero_mul]
        · rw [pure a hm, zero_mul, mul_zero]
      · calc
          _ = ((x i * x j) * (x a * x c)) * (w a a c * x a) := by ring
          _ = 0 := by rw [four i j a c different hac, zero_mul]
    · calc
        _ = ((x i * x j) * (x a * x b)) * (w a b c * x c) := by ring
        _ = 0 := by rw [four i j a b different hab, zero_mul]
  calc
    _ = (x i * x j) * (∑ a, ∑ b, ∑ c, w a b c * (x a * x b * x c)) := by
      rw [unit_cover, mul_one]
    _ = 0 := by simp only [Finset.mul_sum, term, Finset.sum_const_zero]

end PCThreeRoutes
