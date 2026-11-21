import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic

namespace RelationOrientation

def adjacent (i j : Fin 5) : Prop :=
  (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val

instance (i j : Fin 5) : Decidable (adjacent i j) := by
  unfold adjacent
  infer_instance

def complementAdjacent (i j : Fin 5) : Prop := i ≠ j ∧ ¬ adjacent i j

instance (i j : Fin 5) : Decidable (complementAdjacent i j) := by
  unfold complementAdjacent
  infer_instance

theorem cycle_separation :
    ∀ i j : Fin 5, i ≠ j → ∃ k : Fin 5, k ≠ i ∧ k ≠ j ∧ adjacent i k ∧ ¬ adjacent j k := by
  decide

theorem complement_separation :
    ∀ i j : Fin 5, i ≠ j →
      ∃ k : Fin 5, k ≠ i ∧ k ≠ j ∧ complementAdjacent i k ∧ ¬ complementAdjacent j k := by
  decide

theorem paired_exponents_even {G : Type*} [Group G] (u : G)
    (h : u ^ (2 : ℕ) = 1) (k : ℕ) : u ^ (2 * k + 2) = 1 := by
  rw [pow_add, pow_mul, h, one_pow, mul_one]

end RelationOrientation
