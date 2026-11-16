import Mathproof.MinimumGenerationRankMinors
import Mathlib.Algebra.Polynomial.Roots

namespace Mathproof.MinimumGeneration.RankMinors

noncomputable section

open Matrix Polynomial

variable {R ι κ : Type*} [CommRing R]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Scaling both index sets independently makes each principal coefficient a sum
of squared minors weighted by their selected rows and columns. -/
def weightedGram (A : Matrix ι κ R) (a : ι → R) (b : κ → R) : Matrix κ κ R :=
  Matrix.diagonal b * (A.transpose * Matrix.diagonal a * A)

theorem weightedGram_coeff (A : Matrix ι κ R) (a : ι → R) (b : κ → R) (k : ℕ) :
    (Matrix.det (1 + (X : R[X]) • (weightedGram A a b).map C)).coeff k =
      ∑ s ∈ (Finset.univ : Finset κ).powersetCard k,
        (∏ j ∈ s, b j) *
          ∑ t : ColumnSets (s : Finset κ) ι,
            (∏ i : (t.val : Finset ι), a i.val) *
              (columnMinor (A.transpose.submatrix (Subtype.val : s → κ) id) t).det ^ 2 := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro s _
  let B := A.transpose.submatrix (Subtype.val : s → κ) id
  have hsub :
      (weightedGram A a b).submatrix (Subtype.val : s → κ) (Subtype.val : s → κ) =
        Matrix.diagonal (b ∘ (Subtype.val : s → κ)) * (B * Matrix.diagonal a * B.transpose) := by
    ext i j
    simp only [weightedGram, Matrix.submatrix_apply, Matrix.diagonal_mul, Function.comp_apply]
    congr 1
  rw [hsub, Matrix.det_mul, Matrix.det_diagonal, det_weighted_gram_eq_sum_sq_minors]
  change (∏ i : s, b i.val) * _ = _
  rw [Finset.prod_coe_sort s b]

end

section Field

open Matrix Polynomial

variable {K ι κ : Type*} [Field K]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem weightedGram_coeff_eq_zero_of_rank_lt (A : Matrix ι κ K)
    (a : ι → K) (b : κ → K) {k : ℕ} (h : A.rank < k) :
    (Matrix.det (1 + (X : K[X]) • (weightedGram A a b).map C)).coeff k = 0 := by
  rw [weightedGram_coeff]
  apply Finset.sum_eq_zero
  intro s hs
  have hs_card : Fintype.card (s : Type _) = k := by
    rw [Fintype.card_coe, (Finset.mem_powersetCard.mp hs).2]
  suffices hsum : (∑ t : ColumnSets (s : Finset κ) ι,
      (∏ i : (t.val : Finset ι), a i.val) *
        (columnMinor (A.transpose.submatrix (Subtype.val : s → κ) id) t).det ^ 2) = 0 by
    rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro t _
  let B := columnMinor (A.transpose.submatrix (Subtype.val : s → κ) id) t
  have ht_card : Fintype.card (t.val : Type _) = k := by
    rw [Fintype.card_coe, (Finset.mem_powersetCard.mp t.property).2, hs_card]
  have hsub_rank : B.rank ≤ A.rank := by
    rw [← Matrix.rank_transpose A]
    exact (Matrix.rank_submatrix_le _ _ _).trans (Matrix.rank_submatrix_le _ _ _)
  have hdet : B.det = 0 := by
    by_contra hne
    rw [Matrix.rank_of_det_ne_zero hne, ht_card] at hsub_rank
    exact (Nat.not_lt_of_ge hsub_rank) h
  change _ * B.det ^ 2 = 0
  simp [hdet]

end Field

end Mathproof.MinimumGeneration.RankMinors
