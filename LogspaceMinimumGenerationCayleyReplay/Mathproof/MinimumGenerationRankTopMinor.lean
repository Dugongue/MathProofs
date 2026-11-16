import Mathproof.MinimumGenerationRankBasisExchange
import Mathproof.MinimumGenerationWeightedRank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Mathproof.MinimumGeneration.RankMinors

open Submodule

variable {K ι κ : Type*} [Field K]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private theorem colBasisOfFullRank (A : Matrix ι κ K) {S : Finset κ}
    (hfull : (A.submatrix id (Subtype.val : S → κ)).rank = S.card)
    (hcard : S.card = A.rank) :
    LinearIndepOn K A.col (S : Set κ) ∧
      span K (A.col '' (S : Set κ)) = span K (A.col '' (↑(Finset.univ : Finset κ) : Set κ)) := by
  classical
  have hr : Set.range ((A.submatrix id (Subtype.val : S → κ)).col) =
      A.col '' (S : Set κ) := by
    ext x
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hi : LinearIndependent K (A.submatrix id (Subtype.val : S → κ)).col := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Fintype.card_coe, Set.finrank, ← Matrix.rank_eq_finrank_span_cols, hfull]
  refine ⟨hi, Submodule.eq_of_le_of_finrank_eq (span_mono (Set.image_mono ?_)) ?_⟩
  · simp
  · rw [← hr, ← Matrix.rank_eq_finrank_span_cols, hfull, Finset.coe_univ, Set.image_univ,
      ← Matrix.rank_eq_finrank_span_cols, hcard]

private theorem rank_colBasis (A : Matrix ι κ K) {S : Finset κ}
    (hi : LinearIndepOn K A.col (S : Set κ)) :
    (A.submatrix id (Subtype.val : S → κ)).rank = S.card := by
  have h : LinearIndependent K (A.submatrix id (Subtype.val : S → κ)).col := hi
  rw [Matrix.rank_eq_finrank_span_cols, ← show _ = Module.finrank K (span K (Set.range ((A.submatrix id (Subtype.val : S → κ)).col))) from linearIndependent_iff_card_eq_finrank_span.mp h,
    Fintype.card_coe]

variable [LinearOrder ι] [LinearOrder κ]

/-- A top-dimensional nonzero minor is isolated by first minimizing total
column weight and then total row weight. The comparison ranges over all
nonzero minors of that size. -/
theorem exists_lexicographic_minimum_top_minor
    (A : Matrix ι κ K) (a : ι → ℕ) (b : κ → ℕ)
    (ha : StrictMono a) (hb : StrictMono b) :
    ∃ s : ((Finset.univ : Finset κ).powersetCard A.rank),
      ∃ t : ColumnSets (s.val : Finset κ) ι,
        (columnMinor (A.transpose.submatrix (Subtype.val : s.val → κ) id) t).det ≠ 0 ∧
        ∀ s' : ((Finset.univ : Finset κ).powersetCard A.rank),
          ∀ t' : ColumnSets (s'.val : Finset κ) ι,
            (columnMinor (A.transpose.submatrix (Subtype.val : s'.val → κ) id) t').det ≠ 0 →
              ((s' ≠ s ∧ (∑ j ∈ s.val, b j) < ∑ j ∈ s'.val, b j) ∨
                (∃ h : s' = s, h ▸ t' ≠ t ∧ (∑ i ∈ t.val, a i) < ∑ i ∈ t'.val, a i) ∨
                (HEq t' t ∧ s' = s)) := by
  classical
  obtain ⟨S, -, hSi, hSspan, hSmin⟩ :=
    RankIsolation.exists_unique_minimum_spanning_basis (K := K) A.col Finset.univ b hb
  have hSc : S.card = A.rank := by
    rw [← RankIsolation.finrank_span_image_eq_card A.col hSi, hSspan,
      Finset.coe_univ, Set.image_univ, ← Matrix.rank_eq_finrank_span_cols]
  let s : ((Finset.univ : Finset κ).powersetCard A.rank) :=
    ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hSc⟩⟩
  let B := A.transpose.submatrix (Subtype.val : S → κ) id
  have hBs : B.rank = S.card := by
    change (A.submatrix id (Subtype.val : S → κ)).transpose.rank = S.card
    rw [Matrix.rank_transpose]
    exact rank_colBasis A hSi
  obtain ⟨T, -, hTi, hTspan, hTmin⟩ :=
    RankIsolation.exists_unique_minimum_spanning_basis (K := K) B.col Finset.univ a ha
  have hTc : T.card = Fintype.card S := by
    rw [← RankIsolation.finrank_span_image_eq_card B.col hTi, hTspan,
      Finset.coe_univ, Set.image_univ, ← Matrix.rank_eq_finrank_span_cols, hBs, Fintype.card_coe]
  let t : ColumnSets (s.val : Finset κ) ι :=
    ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTc⟩⟩
  have hminor_rank : (columnMinor B t).rank = T.card := by
    change ((B.submatrix id (Subtype.val : T → ι)).submatrix
      (columnIndexEquiv t) (Equiv.refl T)).rank = T.card
    rw [Matrix.rank_submatrix]
    exact rank_colBasis B hTi
  have htdet : (columnMinor B t).det ≠ 0 := by
    apply isUnit_iff_ne_zero.mp
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols, hminor_rank, Fintype.card_coe]
  refine ⟨s, t, htdet, ?_⟩
  intro s' t' ht'
  have hs' : s'.val.card = A.rank := (Finset.mem_powersetCard.mp s'.property).2
  have ht'c : t'.val.card = s'.val.card := by
    rw [(Finset.mem_powersetCard.mp t'.property).2, Fintype.card_coe]
  let B' := A.transpose.submatrix (Subtype.val : s'.val → κ) id
  have hB' : B'.rank = s'.val.card := by
    apply Nat.le_antisymm (by simpa using Matrix.rank_le_card_height B')
    have hl := Matrix.rank_submatrix_le B' (columnIndexEquiv t') (Subtype.val : t'.val → ι)
    change (columnMinor B' t').rank ≤ B'.rank at hl
    rwa [Matrix.rank_of_det_ne_zero ht', Fintype.card_coe, ht'c] at hl
  by_cases h : s' = s
  · subst s'
    by_cases ht : t' = t
    · exact Or.inr (Or.inr ⟨heq_of_eq ht, rfl⟩)
    · apply Or.inr
      apply Or.inl
      refine ⟨rfl, ht, ?_⟩
      have hfull : (B.submatrix id (Subtype.val : t'.val → ι)).rank = t'.val.card := by
        rw [← Matrix.rank_submatrix _ (columnIndexEquiv t') (Equiv.refl t'.val)]
        change (columnMinor B t').rank = _
        rw [Matrix.rank_of_det_ne_zero ht', Fintype.card_coe]
      obtain ⟨hi, hs⟩ := colBasisOfFullRank B hfull (ht'c.trans hBs.symm)
      exact hTmin _ (Finset.subset_univ _) hi hs (fun hv => ht (Subtype.ext hv))
  · apply Or.inl
    refine ⟨h, ?_⟩
    have hfull : (A.submatrix id (Subtype.val : s'.val → κ)).rank = s'.val.card := by
      rw [← Matrix.rank_transpose]
      exact hB'
    obtain ⟨hi, hs⟩ := colBasisOfFullRank A hfull hs'
    exact hSmin _ (Finset.subset_univ _) hi hs (fun hv => h (Subtype.ext hv))

end Mathproof.MinimumGeneration.RankMinors
