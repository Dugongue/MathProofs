namespace DirectionalDifference

def hit (a b x y : Bool) : Prop :=
  ∃ s t : Bool, (s = false ∨ a = true) ∧
    (t = false ∨ b = true) ∧ x = s ∧ y = (!s != t)

theorem edge_hit (a b : Bool) : hit a b true false ↔ a = true := by
  constructor
  · rintro ⟨s, t, hs, ht, hx, hy⟩
    subst s
    simpa using hs
  · intro ha
    exact ⟨true, false, Or.inr ha, Or.inl rfl, rfl, rfl⟩

theorem zero_hit (a b : Bool) : hit a b false false ↔ b = true := by
  constructor
  · rintro ⟨s, t, hs, ht, hx, hy⟩
    subst s
    cases t
    · simp at hy
    · simpa using ht
  · intro hb
    exact ⟨false, true, Or.inl rfl, Or.inr hb, rfl, rfl⟩

theorem directional_difference (a b : Bool) :
    (hit a b true false ∧ ¬ hit a b false false) ↔
      a = true ∧ b = false := by
  rw [edge_hit, zero_hit]
  cases b <;> simp

end DirectionalDifference
