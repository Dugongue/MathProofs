import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix

theorem two_stripe_rank_bound {K m n : Type*} [Field K] [Fintype n]
    (u : Fin 2 → m → K) (v : Fin 2 → n → K) :
    (vecMulVec (u 0) (v 0) + vecMulVec (u 1) (v 1)).rank ≤ 2 := by
  let L : Matrix m (Fin 2) K := Matrix.of (fun i k => u k i)
  let R : Matrix (Fin 2) n K := Matrix.of (fun k j => v k j)
  have heq : L * R = vecMulVec (u 0) (v 0) + vecMulVec (u 1) (v 1) := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  rw [← heq]
  exact (Matrix.rank_mul_le_left L R).trans (by simpa using Matrix.rank_le_card_width L)

theorem isolated_matching_minor_rank {K m n : Type*} [Field K] [Fintype n]
    (A : Matrix m n K) (row : Fin 3 → m) (col : Fin 3 → n)
    (hdiag : ∀ i : Fin 3, A (row i) (col i) ≠ 0)
    (hoff : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 →
      ∃ i : Fin 3, A (row (σ i)) (col i) = 0) :
    3 ≤ A.rank := by
  classical
  let B := A.submatrix row col
  have hdet : B.det = ∏ i : Fin 3, A (row i) (col i) := by
    rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin 3))]
    · simp [B]
    · intro σ _ hσ
      obtain ⟨i, hi⟩ := hoff σ hσ
      have hz : (∏ j : Fin 3, B (σ j) j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hi
      simp [hz]
    · simp
  have hrank : B.rank = 3 := by
    have hne : B.det ≠ 0 := by
      rw [hdet]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)
    simpa using Matrix.rank_of_det_ne_zero hne
  exact hrank ▸ Matrix.rank_submatrix_le A row col
