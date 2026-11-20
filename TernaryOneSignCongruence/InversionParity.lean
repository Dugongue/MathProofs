import Mathlib.Logic.Basic

namespace AlternatingSignQueries

inductive InversionTree (I : Type*) where
  | leaf (i : I)
  | fork (left right : InversionTree I)

def InversionTree.parity {I : Type*} (value : I → Bool) : InversionTree I → Bool
  | .leaf i => value i
  | .fork l r => Bool.xor (l.parity value) (r.parity value)

def InversionTree.rails {I : Type*} (query : I → Bool → Prop) :
    InversionTree I → Prop × Prop
  | .leaf i => (query i false, query i true)
  | .fork l r =>
      let a := l.rails query
      let b := r.rails query
      ((a.1 ∧ b.1) ∨ (a.2 ∧ b.2), (a.1 ∧ b.2) ∨ (a.2 ∧ b.1))

theorem inversionRails_exact {I : Type*} (tree : InversionTree I)
    (query : I → Bool → Prop) (value : I → Bool)
    (sound : ∀ i b, query i b ↔ value i = b) :
    ((tree.rails query).1 ↔ tree.parity value = false) ∧
      ((tree.rails query).2 ↔ tree.parity value = true) := by
  induction tree with
  | leaf i => exact ⟨sound i false, sound i true⟩
  | fork l r hl hr =>
    simp only [InversionTree.rails, InversionTree.parity, hl.1, hl.2, hr.1, hr.2]
    cases l.parity value <;> cases r.parity value <;> decide

/-- With a unique induced label map, all individual inversion queries read the
same witness, even when the raw congruence itself is not unique. -/
theorem inversionRails_for_witnesses {I W P : Type*} (tree : InversionTree I)
    (label : W → P) (inversion : P → I → Bool)
    (uniqueLabel : ∀ u v, label u = label v) (desired : Bool) :
    let queries := tree.rails fun i b => ∃ w, inversion (label w) i = b
    (Nonempty W ∧ (if desired then queries.2 else queries.1)) ↔
      ∃ w, tree.parity (inversion (label w)) = desired := by
  by_cases h : Nonempty W
  · obtain ⟨w₀⟩ := h
    have queries : ∀ i b, (∃ w, inversion (label w) i = b) ↔
        inversion (label w₀) i = b := by
      intro i b
      constructor
      · rintro ⟨w, hw⟩
        simpa only [uniqueLabel w w₀] using hw
      · exact fun hw => ⟨w₀, hw⟩
    obtain ⟨even, odd⟩ := inversionRails_exact tree _ _ queries
    have root : (∃ w, tree.parity (inversion (label w)) = desired) ↔
        tree.parity (inversion (label w₀)) = desired := by
      constructor
      · rintro ⟨w, hw⟩
        simpa only [uniqueLabel w w₀] using hw
      · exact fun hw => ⟨w₀, hw⟩
    cases desired <;> simp [Nonempty.intro w₀, even, odd, root]
  · simp only [h, false_and, false_iff]
    exact fun ⟨w, _⟩ => h ⟨w⟩

end AlternatingSignQueries
