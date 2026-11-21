import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Abel

namespace GrochowCatalogueTenth

theorem projection_coset_iff {A : Type*} [AddCommGroup A]
    (P : A →+ A) (x y : A) :
    x - P x = y - P y ↔ P (x - y) = x - y := by
  rw [map_sub]
  constructor
  · intro h
    calc
      P x - P y = (x - y) - ((x - P x) - (y - P y)) := by abel
      _ = x - y := by rw [h, sub_self, sub_zero]
  · intro h
    calc
      x - P x = (y - P y) + ((x - y) - (P x - P y)) := by abel
      _ = y - P y := by rw [h, sub_self, add_zero]

/-- An idempotent projection selects exactly one kernel representative of each
    coset of its image. -/
theorem unique_projection_representative {A : Type*} [AddCommGroup A]
    (P : A →+ A) (hP : ∀ x, P (P x) = P x) (x : A) :
    ∃! y : A, P y = 0 ∧ P (x - y) = x - y := by
  refine ⟨x - P x, ⟨?_, ?_⟩, ?_⟩
  · rw [map_sub, hP, sub_self]
  · rw [show x - (x - P x) = P x by abel, hP]
  · intro y hy
    have hn := (projection_coset_iff P x y).2 hy.2
    simpa [hy.1] using hn.symm

end GrochowCatalogueTenth

#print axioms GrochowCatalogueTenth.projection_coset_iff
#print axioms GrochowCatalogueTenth.unique_projection_representative
