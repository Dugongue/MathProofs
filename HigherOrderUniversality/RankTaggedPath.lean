import Mathlib.Data.Nat.Basic

theorem fixesMarkedPath {V : Type*} (cornerRank : V → V → ℕ)
    (path mark : ℕ → V) (last : ℕ) (g : V → V)
    (preserves : ∀ x y, cornerRank (g x) (g y) = cornerRank x y)
    (first : g (path 0) = path 0)
    (next : ∀ i, i < last → ∀ v, cornerRank (path i) v = 2 ↔ v = path (i + 1))
    (tag : ∀ i, i ≤ last → ∀ v, cornerRank (path i) v = 1 ↔ v = mark i) :
    ∀ i, i ≤ last → g (path i) = path i ∧ g (mark i) = mark i := by
  have fixedPath : ∀ i, i ≤ last → g (path i) = path i := by
    intro i
    induction i with
    | zero =>
      intro _
      exact first
    | succ i ih =>
      intro hi
      have hi' : i < last := Nat.lt_of_succ_le hi
      have prior := ih (Nat.le_of_lt hi')
      have rankEquality := preserves (path i) (path (i + 1))
      rw [prior] at rankEquality
      exact (next i hi' _).mp (rankEquality.trans ((next i hi' _).mpr rfl))
  intro i hi
  have prior := fixedPath i hi
  have rankEquality := preserves (path i) (mark i)
  rw [prior] at rankEquality
  exact ⟨prior, (tag i hi _).mp (rankEquality.trans ((tag i hi _).mpr rfl))⟩
