import Mathproof.MinimumGenerationRankTopMinor
import Mathproof.MinimumGenerationRankScan
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Mathproof.MinimumGeneration.RankMinors

open Matrix Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m n : ℕ}

private abbrev TopIndex (A : Matrix (Fin m) (Fin n) K) :=
  Σ s : ((Finset.univ : Finset (Fin n)).powersetCard A.rank),
    ColumnSets (s.val : Finset (Fin n)) (Fin m)

private def rowWeight (A : Matrix (Fin m) (Fin n) K) (p : TopIndex A) : ℕ :=
  ∑ i ∈ p.2.val, i.val

private def colWeight (A : Matrix (Fin m) (Fin n) K) (p : TopIndex A) : ℕ :=
  ∑ j ∈ p.1.val, j.val

private noncomputable def minorValue (A : Matrix (Fin m) (Fin n) K) (p : TopIndex A) : K :=
  (columnMinor (A.transpose.submatrix (Subtype.val : p.1.val → Fin n) id) p.2).det ^ 2

private def rowBound (m : ℕ) : ℕ := ∑ i : Fin m, i.val

def rankProbeDegree (m n : ℕ) : ℕ := rowBound m + (rowBound m + 1) * rowBound n

theorem rankProbeDegree_le (m n : ℕ) :
    rankProbeDegree m n ≤ m*m + (m*m+1)*(n*n) := by
  have h (d : ℕ) : rowBound d ≤ d*d := by
    calc
      rowBound d ≤ ∑ _ : Fin d, d := Finset.sum_le_sum fun i _ => Nat.le_of_lt i.isLt
      _ = d*d := by simp
  exact Nat.add_le_add (h m) (Nat.mul_le_mul (Nat.add_le_add_right (h m) 1) (h n))
private def exponent (A : Matrix (Fin m) (Fin n) K) (p : TopIndex A) : ℕ :=
  rowWeight A p + (rowBound m + 1) * colWeight A p

private theorem exponent_le (A : Matrix (Fin m) (Fin n) K) (p : TopIndex A) :
    exponent A p ≤ rankProbeDegree m n := by
  apply Nat.add_le_add
  · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · exact Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.subset_univ _))

private theorem eval_top_polynomial (A : Matrix (Fin m) (Fin n) K) (t : K) :
    (∑ p : TopIndex A, Polynomial.monomial (exponent A p) (minorValue A p)).eval t =
      (Matrix.det (1 + (X : K[X]) •
        (weightedGram A (fun i => t ^ i.val)
          (fun j => t ^ ((rowBound m + 1) * j.val))).map C)).coeff A.rank := by
  classical
  rw [weightedGram_coeff, ← Finset.sum_coe_sort ((Finset.univ : Finset (Fin n)).powersetCard A.rank),
    Polynomial.eval_finsetSum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Polynomial.eval_monomial, Finset.prod_coe_sort u.val (fun i : Fin m => t ^ i.val)]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
  simp only [exponent, minorValue, rowWeight, colWeight, pow_add, pow_mul]
  ring

/-- Over a field large enough for this grid, the exact signed Berkowitz scan
recovers the true rank of every rectangular matrix, in any characteristic.
The exponents are fixed from the dimensions before any matrix entry is read. -/
theorem scanWeightedBerkowitzRank_eq_rank (A : Matrix (Fin m) (Fin n) K)
    (hfield : (∑ i : Fin m, i.val) + ((∑ i : Fin m, i.val) + 1) *
      (∑ j : Fin n, j.val) < Fintype.card K) :
    scanWeightedBerkowitzRank A (fun t i => t ^ i.val)
      (fun t j => t ^ (((∑ i : Fin m, i.val) + 1) * j.val)) = A.rank := by
  classical
  change scanWeightedBerkowitzRank A _ (fun t j => t ^ ((rowBound m + 1) * j.val)) = A.rank
  apply scanWeightedBerkowitzRank_eq_rank_of_top
  obtain ⟨s, u, hminor, hmin⟩ :=
    exists_lexicographic_minimum_top_minor A Fin.val Fin.val
      (fun _ _ h => h) (fun _ _ h => h)
  let p : TopIndex A := ⟨s, u⟩
  have hval : minorValue A p ≠ 0 := pow_ne_zero _ hminor
  have hiso : ∀ q : TopIndex A, q ∈ Finset.univ → q ≠ p →
      exponent A q = exponent A p → minorValue A q = 0 := by
    intro q _ hnq he
    by_contra hne
    have hdet : (columnMinor (A.transpose.submatrix (Subtype.val : q.1.val → Fin n) id)
        q.2).det ≠ 0 := by
      intro hzero
      exact hne (by simp [minorValue, hzero])
    rcases hmin q.1 q.2 hdet with hcol | ⟨hs, hu, hrow⟩ | ⟨hu, hs⟩
    · have hrl : rowWeight A p ≤ rowBound m :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hcl : colWeight A p + 1 ≤ colWeight A q := hcol.2
      have hmul := Nat.mul_le_mul_left (rowBound m + 1) hcl
      rw [Nat.mul_add, Nat.mul_one] at hmul
      unfold exponent at he
      omega
    · have hrl : rowWeight A p < rowWeight A q := hrow
      have hc : colWeight A p = colWeight A q := by simp [colWeight, p, hs]
      unfold exponent at he
      rw [hc] at he
      omega
    · exact hnq (Sigma.ext hs hu)
  obtain ⟨t, heval⟩ := RankIsolation.has_nonzero_evaluation_of_isolated_term
    (Finset.univ : Finset (TopIndex A)) (exponent A) (minorValue A) (rankProbeDegree m n)
      (fun q _ => exponent_le A q) hfield p (Finset.mem_univ p) hval hiso
  rw [eval_top_polynomial A t] at heval
  exact ⟨t, heval⟩

end Mathproof.MinimumGeneration.RankMinors
