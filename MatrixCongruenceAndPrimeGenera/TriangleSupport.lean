import Init

namespace TriangleSupport

/-- For three distinct edges in canonical lexicographic order, a vanishing
binary incidence sum characterizes the three edges of a triangle. -/
theorem triangleSupport (a b c d e f : Nat) (hab : a < b) (hcd : c < d)
    (hef : e < f) (h12 : a < c ∨ (a = c ∧ b < d))
    (h23 : c < e ∨ (c = e ∧ d < f)) :
    (∀ v : Nat, (¬ ((v = a ∨ v = b) ↔ (v = c ∨ v = d))) ↔
      (v = e ∨ v = f)) ↔ (a = c ∧ b = e ∧ d = f) := by
  constructor
  · intro h
    have ha := h a
    have hb := h b
    have hd := h d
    grind
  · rintro ⟨rfl, rfl, rfl⟩ v
    grind

end TriangleSupport
