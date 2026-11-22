import Mathlib.Algebra.BigOperators.Ring.Finset

namespace GrochowOrbitNorm

variable {A I : Type*} [Semiring A] [Fintype I]

theorem transport_sum (x : A) (s t : I → A)
    (h : ∀ i, x * s i = t i * x) :
    x * (∑ i, s i) = (∑ i, t i) * x := by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => h i)

theorem left_norm_obstruction (x y : A) (s t : I → A)
    (h : ∀ i, x * s i = t i * x)
    (hinv : y * x = 1) (hs : (∑ i, s i) ≠ 0) (ht : (∑ i, t i) = 0) : False := by
  have hz := transport_sum x s t h
  rw [ht, zero_mul] at hz
  apply hs
  calc
    (∑ i, s i) = (y * x) * (∑ i, s i) := by rw [hinv, one_mul]
    _ = y * (x * (∑ i, s i)) := mul_assoc _ _ _
    _ = 0 := by rw [hz, mul_zero]

theorem right_norm_obstruction (x y : A) (s t : I → A)
    (h : ∀ i, x * s i = t i * x)
    (hinv : x * y = 1) (hs : (∑ i, s i) = 0) (ht : (∑ i, t i) ≠ 0) : False := by
  have hz := transport_sum x s t h
  rw [hs, mul_zero] at hz
  apply ht
  calc
    (∑ i, t i) = (∑ i, t i) * (x * y) := by rw [hinv, mul_one]
    _ = ((∑ i, t i) * x) * y := (mul_assoc _ _ _).symm
    _ = 0 := by rw [← hz, zero_mul]

end GrochowOrbitNorm
