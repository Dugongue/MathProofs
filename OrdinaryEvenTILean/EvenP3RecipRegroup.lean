import EvenP1Geometry

namespace Mathproof.EvenTI.Reciprocal.Coverage

open EvenTI.Action

noncomputable section

abbrev SquareGroups (n : ℕ) := Fin 4 ⊕ Fin (n - 5)
abbrev SquareRows (n : ℕ) := Sum (High 1 n) (Low 1 n) × Option (SquareGroups n)
abbrev SquareCols (n : ℕ) := Fin n × Coord 1 n

theorem squareGroups_card (n : ℕ) (hn : 5 ≤ n) :
    Fintype.card (SquareGroups n) = n - 1 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

/-- The square-cut reciprocal basis exposes four particular groups while
leaving the others available for any independent second partition. -/
def squareLeftRegroup {n : ℕ} (hn : 5 ≤ n) (i : Fin 2) : SquareRows n ≃ Coord 2 n :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.optionCongr (Fintype.equivOfCardEq (by
    rw [squareGroups_card n hn, Fintype.card_fin])))).trans (leftRegroup (by omega) i)

#print axioms squareLeftRegroup

end
end Mathproof.EvenTI.Reciprocal.Coverage
