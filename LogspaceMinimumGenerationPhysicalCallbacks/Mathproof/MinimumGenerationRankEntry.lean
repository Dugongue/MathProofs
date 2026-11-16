import Mathproof.MinimumGenerationWeightedRank

namespace Mathproof.MinimumGeneration.RankMinors

variable {K : Type*} [CommRing K] {m n : ℕ}

private theorem foldl_add_eq_sum {d : ℕ} (f : Fin d → K) :
    Fin.foldl d (fun acc i => acc + f i) 0 = ∑ i, f i := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
      exact congrArg (fun x => x + f (Fin.last d)) (ih (fun i => f i.castSucc))

/-- The input to a Berkowitz entry query uses two original matrix entries per
row. The fold runs in row order with one field accumulator. -/
def streamWeightedGramEntry (read : Fin m → Fin n → K) (a : Fin m → K) (b : Fin n → K)
    (i j : Fin n) : K :=
  b i * Fin.foldl m (fun sum r => sum + (read r i * a r) * read r j) 0

theorem streamWeightedGramEntry_eq (A : Matrix (Fin m) (Fin n) K)
    (a : Fin m → K) (b : Fin n → K) (i j : Fin n) :
    streamWeightedGramEntry A a b i j = weightedGram A a b i j := by
  unfold streamWeightedGramEntry
  rw [foldl_add_eq_sum, weightedGram, Matrix.diagonal_mul, Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]

end Mathproof.MinimumGeneration.RankMinors
