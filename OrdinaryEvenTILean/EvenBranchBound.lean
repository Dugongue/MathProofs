import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace EvenTI.BranchBudget

/-- Enumeration of a list of inner trials per outer trial has the
product bound on the number of trials actually passed to the driver. -/
theorem length_flatMap_le {A B : Type*} (outer : List A) (inner : A → List B) (bound : Nat)
    (h : ∀ a ∈ outer, (inner a).length ≤ bound) :
    (outer.flatMap inner).length ≤ outer.length * bound := by
  induction outer with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have hx := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- At most two exact kernel-form coordinates are searched in the outer
loop. The checked shape gate bounds repeated primary trials by the full
dense coefficient count. The resulting exponent is independent of order. -/
theorem kernel_primary_trials_le {A B : Type*} (outer : List A) (inner : A → List B)
    {n d : Nat} (hn : 2 ≤ n) (hd : 2 ≤ d) (houter : outer.length ≤ n ^ 2)
    (hinner : ∀ a ∈ outer, (inner a).length ≤ n ^ d) :
    (outer.flatMap inner).length ≤ (n ^ d) ^ 2 := by
  calc
    _ ≤ outer.length * n ^ d := length_flatMap_le outer inner _ hinner
    _ ≤ n ^ 2 * n ^ d := Nat.mul_le_mul_right _ houter
    _ ≤ (n ^ d) ^ 2 := by
      rw [pow_two (n ^ d)]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hd)

#print axioms kernel_primary_trials_le

end EvenTI.BranchBudget
