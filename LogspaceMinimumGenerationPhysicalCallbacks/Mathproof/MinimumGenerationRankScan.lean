import Mathproof.MinimumGenerationRankBerkowitz
import Mathproof.MinimumGenerationWeightedRank
import Mathlib.Data.Finset.Lattice.Fold

namespace Mathproof.MinimumGeneration.RankMinors

open Matrix Polynomial
open Mathproof.MinimumGeneration.RankBerkowitz

variable {K : Type*} [Field K] [DecidableEq K] {m n : ℕ}

omit [DecidableEq K] in
theorem balancedCoefficient_weightedGram (A : Matrix (Fin m) (Fin n) K)
    (a : Fin m → K) (b : Fin n → K) (k : Fin (n + 1)) :
    Berkowitz.balancedCoefficient (weightedGram A a b)
        ⟨n - k.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ =
      (-1) ^ k.val * (Matrix.det
        (1 + (X : K[X]) • (weightedGram A a b).map C)).coeff k.val := by
  rw [Berkowitz.balancedCoefficient_eq, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  have hc := Matrix.charpoly_coeff_eq_sum_minors
    (weightedGram A a b) k.val (by simpa using Nat.le_of_lt_succ k.isLt)
  simpa only [Fintype.card_fin] using hc

variable [Fintype K]

/-- Scan all field elements and degrees, keeping the largest nonzero tested
degree. This is the functional specification for the streamed outer loop. -/
noncomputable def scanWeightedBerkowitzRank (A : Matrix (Fin m) (Fin n) K)
    (a : K → Fin m → K) (b : K → Fin n → K) : ℕ :=
  ((Finset.univ : Finset (K × Fin (n + 1))).filter fun tk =>
    Berkowitz.balancedCoefficient (weightedGram A (a tk.1) (b tk.1))
      ⟨n - tk.2.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ≠ 0).sup
    (fun tk => tk.2.val)

theorem scanWeightedBerkowitzRank_le_rank (A : Matrix (Fin m) (Fin n) K)
    (a : K → Fin m → K) (b : K → Fin n → K) :
    scanWeightedBerkowitzRank A a b ≤ A.rank := by
  unfold scanWeightedBerkowitzRank
  apply Finset.sup_le_iff.mpr
  intro tk htk
  have hne := (Finset.mem_filter.mp htk).2
  by_contra! hlt
  rw [balancedCoefficient_weightedGram, weightedGram_coeff_eq_zero_of_rank_lt _ _ _ hlt,
    mul_zero] at hne
  exact hne rfl

theorem scanWeightedBerkowitzRank_eq_rank_of_top (A : Matrix (Fin m) (Fin n) K)
    (a : K → Fin m → K) (b : K → Fin n → K)
    (htop : ∃ t : K, (Matrix.det
      (1 + (X : K[X]) • (weightedGram A (a t) (b t)).map C)).coeff A.rank ≠ 0) :
    scanWeightedBerkowitzRank A a b = A.rank := by
  apply Nat.le_antisymm (scanWeightedBerkowitzRank_le_rank A a b)
  obtain ⟨t, ht⟩ := htop
  have hle : A.rank ≤ n := by simpa using Matrix.rank_le_card_width A
  let k : Fin (n + 1) := ⟨A.rank, Nat.lt_succ_of_le hle⟩
  unfold scanWeightedBerkowitzRank
  apply Finset.le_sup (b := (t, k)) (f := fun tk : K × Fin (n + 1) => tk.2.val)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [balancedCoefficient_weightedGram]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ht

end Mathproof.MinimumGeneration.RankMinors
