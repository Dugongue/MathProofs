import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace CharacterEnergy

/-- Expansion of the squared discrepancy over an arbitrary finite panel. -/
theorem gram {I X : Type*} (s : Finset I) (u : Finset X) (a : I → X → ℤ) :
    (∑ x ∈ u, (∑ i ∈ s, a i x)^2) =
      ∑ i ∈ s, ∑ j ∈ s, ∑ x ∈ u, a i x * a j x := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- The computable Gram sum detects exactly the presence of a distinguishing
observation. Signs and repeated observations are allowed. -/
theorem gram_zero_iff {I X : Type*} (s : Finset I) (u : Finset X) (a : I → X → ℤ) :
    (∑ i ∈ s, ∑ j ∈ s, ∑ x ∈ u, a i x * a j x) = 0 ↔
      ∀ x ∈ u, (∑ i ∈ s, a i x) = 0 := by
  rw [← gram]
  constructor
  · intro hz x hx
    have hle := Finset.single_le_sum
      (f := fun y => (∑ i ∈ s, a i y)^2) (fun y _ => sq_nonneg _) hx
    rw [hz] at hle
    nlinarith
  · intro hall
    apply Finset.sum_eq_zero
    intro x hx
    rw [hall x hx]
    norm_num

end CharacterEnergy
