import Mathlib.Data.Matrix.Basic

theorem commonRectangularAdjointBlock
    {RowOut RowIn Col R : Type*}
    [Nonempty RowOut] [Nonempty RowIn] [DecidableEq RowOut] [DecidableEq RowIn]
    [Zero R]
    (left : RowOut → RowOut → Col → Col → R)
    (right : RowIn → RowIn → Col → Col → R)
    (intertwines : ∀ i j u v a b,
      (if v = j then left u i a b else 0) =
        (if u = i then right j v a b else 0)) :
    ∃ corner : Col → Col → R,
      (∀ u i a b, left u i a b = if u = i then corner a b else 0) ∧
      (∀ j v a b, right j v a b = if v = j then corner a b else 0) := by
  obtain ⟨i₀⟩ := ‹Nonempty RowOut›
  obtain ⟨j₀⟩ := ‹Nonempty RowIn›
  refine ⟨left i₀ i₀, ?_, ?_⟩
  · intro u i a b
    by_cases eq : u = i
    · subst u
      simpa using (intertwines i j₀ i j₀ a b).trans
        (by simpa using (intertwines i₀ j₀ i₀ j₀ a b).symm)
    · simpa [eq] using intertwines i j₀ u j₀ a b
  · intro j v a b
    simpa using (intertwines i₀ j i₀ v a b).symm
