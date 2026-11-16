import Mathproof.MinimumGenerationRankTopMinor

namespace Mathproof.MinimumGeneration.RankMinors

variable {K L : Type*} [Field K] [Field L] {m n : ℕ}

private theorem card_le_rank_of_column_minor (A : Matrix (Fin m) (Fin n) K)
    (s : Finset (Fin n)) (t : ColumnSets s (Fin m))
    (h : (columnMinor (A.transpose.submatrix (Subtype.val : s → Fin n) id) t).det ≠ 0) :
    s.card ≤ A.rank := by
  let B := A.transpose.submatrix (Subtype.val : s → Fin n) id
  have hminor := Matrix.rank_submatrix_le B (columnIndexEquiv t) (Subtype.val : t.val → Fin m)
  change (columnMinor B t).rank ≤ B.rank at hminor
  have hb := Matrix.rank_submatrix_le A.transpose (Subtype.val : s → Fin n) id
  rw [Matrix.rank_transpose] at hb
  have ht : Fintype.card (t.val : Type _) = s.card := by
    rw [Fintype.card_coe, (Finset.mem_powersetCard.mp t.property).2, Fintype.card_coe]
  rw [Matrix.rank_of_det_ne_zero h, ht] at hminor
  exact hminor.trans hb

/-- The input rank is unchanged by the field embedding used to enlarge the
grid. Both inequalities follow by transporting a full-rank minor. -/
theorem rank_map_field_eq (A : Matrix (Fin m) (Fin n) K) (f : K →+* L) :
    (A.map f).rank = A.rank := by
  obtain ⟨sK, tK, hK, -⟩ := exists_lexicographic_minimum_top_minor A Fin.val Fin.val
    (fun _ _ h => h) (fun _ _ h => h)
  obtain ⟨sL, tL, hL, -⟩ := exists_lexicographic_minimum_top_minor (A.map f) Fin.val Fin.val
    (fun _ _ h => h) (fun _ _ h => h)
  have hsK := (Finset.mem_powersetCard.mp sK.property).2
  have hsL := (Finset.mem_powersetCard.mp sL.property).2
  apply Nat.le_antisymm
  · rw [← hsL]
    apply card_le_rank_of_column_minor A sL.val tL
    intro hzero
    apply hL
    calc
      _ = f (columnMinor (A.transpose.submatrix (Subtype.val : sL.val → Fin n) id) tL).det := by
        exact columnMinor_map_det _ f _
      _ = 0 := by rw [hzero, map_zero]
  · rw [← hsK]
    apply card_le_rank_of_column_minor (A.map f) sK.val tK
    intro hzero
    apply hK
    apply f.injective
    rw [map_zero, ← columnMinor_map_det]
    exact hzero

end Mathproof.MinimumGeneration.RankMinors
