import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace ArithmeticComplexityTransfers

/-- A local integral multiplier lies in each common divisibility condition
on the evaluations of the orbit sums. -/
theorem divides_orbit_combination {A : Type*} [Fintype A]
    (b : ℤ) (value coefficient : A → ℤ)
    (h : ∀ a, b ∣ value a) : b ∣ ∑ a, coefficient a * value a := by
  classical
  exact Finset.dvd_sum fun a _ => dvd_mul_of_dvd_right (h a) _

/-- Integral symmetric multiplier of main-placeholder degree one for two pigeons. -/
def twoPigeonMultiplier {R : Type*} [CommRing R]
    (x y row₁ row₂ collision grid₁ grid₂ : R) : R :=
  -((1 - x) * (1 - y) * (row₁ + row₂)) -
    2 * x * (1 - y) * row₂ - 2 * (1 - x) * y * row₁ +
    2 * x * y * collision -
    ((1 + 3 * y) * grid₁ + (1 + 3 * x) * grid₂ + 2 * grid₁ * grid₂)

theorem twoPigeonMultiplier_zero {R : Type*} [CommRing R] (x y : R) :
    twoPigeonMultiplier x y 0 0 0 0 0 = 0 := by
  simp [twoPigeonMultiplier]

theorem twoPigeonMultiplier_symmetric {R : Type*} [CommRing R]
    (x y row₁ row₂ collision grid₁ grid₂ : R) :
    twoPigeonMultiplier x y row₁ row₂ collision grid₁ grid₂ =
      twoPigeonMultiplier y x row₂ row₁ collision grid₂ grid₁ := by
  unfold twoPigeonMultiplier
  ring

theorem twoPigeonMultiplier_substitute {R : Type*} [CommRing R] (x y : R) :
    twoPigeonMultiplier x y (x - 1) (y - 1) (x * y) (x ^ 2 - x) (y ^ 2 - y) = 2 := by
  unfold twoPigeonMultiplier
  ring

/-- At the all-zero Boolean assignment, equal coefficients on the swapped
row placeholders force every main-linear integral multiplier to be even. -/
theorem twoPigeon_local_even (a b c multiplier : ℤ)
    (symm : a = b) (eval : a * (-1) + b * (-1) + c * 0 = multiplier) :
    2 ∣ multiplier := by
  refine ⟨-a, ?_⟩
  calc
    multiplier = a * (-1) + a * (-1) + c * 0 := by rw [eval.symm, ← symm]
    _ = 2 * -a := by ring

/-- A reusable multilinearization step for the correction in the reciprocal
construction. The two values are the restrictions at 0 and 1. -/
theorem multiply_linear_interpolation {R : Type*} [CommRing R] (x zero one : R) :
    x * ((1 - x) * zero + x * one) =
      x * one + (x ^ 2 - x) * (one - zero) := by
  ring

end ArithmeticComplexityTransfers
