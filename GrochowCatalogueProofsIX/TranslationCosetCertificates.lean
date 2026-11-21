import Mathlib.Algebra.Group.Basic

namespace GrochowCatalogueNinth

/-- Translating a multiplicity function by an additive group element. -/
def shift {A B : Type*} [AddCommGroup A] (a : A) (f : A → B) : A → B :=
  fun x => f (x - a)

theorem shift_comp {A B : Type*} [AddCommGroup A] (a b : A) (f : A → B) :
    shift a (shift b f) = shift (a + b) f := by
  funext x
  simp only [shift, sub_sub]

/-- Once one transport is known, a second offset works exactly when their
    difference stabilizes the source multiplicity function. -/
theorem translation_offset_iff {A B : Type*} [AddCommGroup A]
    (a b : A) (f g : A → B) (ha : shift a f = g) :
    shift b f = g ↔ shift (b - a) f = f := by
  constructor
  · intro hb
    have h := congrArg (shift (-a)) (hb.trans ha.symm)
    rw [shift_comp, shift_comp, neg_add_cancel] at h
    have hz : shift (0 : A) f = f := by
      funext x
      simp [shift]
    rw [hz] at h
    simpa only [sub_eq_add_neg, add_comm] using h
  · intro h
    have h' := congrArg (shift a) h
    rw [shift_comp] at h'
    have he : a + (b - a) = b := by
      rw [add_comm, sub_add_cancel]
    rw [he, ha] at h'
    exact h'

end GrochowCatalogueNinth

#print axioms GrochowCatalogueNinth.shift_comp
#print axioms GrochowCatalogueNinth.translation_offset_iff
