import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators

theorem graded_character_transfer {ι G : Type*} [CommGroup G]
    (s : Finset ι) (full : ι → Prop) [DecidablePred full]
    (r q h : ι → G) (piece : ∀ i ∈ s, h i = r i * q i) :
    (∏ i ∈ s, r i) = (∏ i ∈ s, if full i then h i else 1) *
      (∏ i ∈ s, if full i then (q i)⁻¹ else r i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hf : full i
  · simp [hf, piece i hi, mul_assoc]
  · simp [hf]
