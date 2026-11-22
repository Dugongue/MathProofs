import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.Basic

theorem synchronize_shifts {G I : Type*} [AddCommGroup G]
    {H : I → Type*} [∀ i, AddCommGroup (H i)]
    (project : (i : I) → G →+ H i) (localGroup : (i : I) → AddSubgroup (H i))
    (offset : (i : I) → H i) (base : G)
    (valid : ∀ i, project i base - offset i ∈ localGroup i) (x : G) :
    (∀ i, project i x - offset i ∈ localGroup i) ↔
      ∃ z : G, (∀ i, project i z ∈ localGroup i) ∧ x = base + z := by
  constructor
  · intro hx
    refine ⟨x - base, ?_, ?_⟩
    · intro i
      rw [map_sub]
      simpa only [sub_sub_sub_cancel_right] using (localGroup i).sub_mem (hx i) (valid i)
    · simp [sub_eq_add_neg, add_comm, add_left_comm]
  · rintro ⟨z, hz, rfl⟩ i
    rw [map_add, add_sub_right_comm]
    exact (localGroup i).add_mem (valid i) (hz i)
