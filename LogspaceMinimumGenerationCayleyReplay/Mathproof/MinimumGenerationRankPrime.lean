import Mathproof.MinimumGenerationRankField
import Mathproof.MinimumGenerationRankGrid
import Mathproof.MinimumGenerationRankGridField

namespace Mathproof.MinimumGeneration.RankMinors

open RankGridField

noncomputable local instance (p T : ℕ) [Fact p.Prime] : Fintype (Extension p T) :=
  Fintype.ofFinite _

noncomputable local instance (p T : ℕ) [Fact p.Prime] : DecidableEq (Extension p T) :=
  Classical.decEq _
/-- For every prime and rectangular base-field matrix, the deterministic grid
of weighted Berkowitz tests returns the exact base-field rank. The number of
extension elements inspected is bounded by the prime times a polynomial in
the dimensions. The theorem is the functional correctness of the scan. -/
theorem scanWeightedBerkowitzRank_zmod (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod p)) :
    let T := rankProbeDegree m n
    let B := A.map (baseEmbedding p T)
    scanWeightedBerkowitzRank B (fun t i => t ^ i.val)
      (fun t j => t ^ (((∑ i : Fin m, i.val) + 1) * j.val)) = A.rank ∧
    Fintype.card (Extension p T) ≤ p * (m*m + (m*m+1)*(n*n) + 1) := by
  classical
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [scanWeightedBerkowitzRank_eq_rank, rank_map_field_eq]
    change rankProbeDegree m n < Fintype.card (Extension p (rankProbeDegree m n))
    simpa only [Nat.card_eq_fintype_card] using threshold_lt_card p (rankProbeDegree m n)
  · rw [← Nat.card_eq_fintype_card]
    exact (card_le_mul_succ_threshold p (rankProbeDegree m n)).trans
      (Nat.mul_le_mul_left p (Nat.add_le_add_right (rankProbeDegree_le m n) 1))

end Mathproof.MinimumGeneration.RankMinors
