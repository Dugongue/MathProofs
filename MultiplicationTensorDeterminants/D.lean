import Mathlib

namespace DetRatioFour.Quiver

open Equiv Equiv.Perm

/-- The coupled action on the endpoint banks and the four paths attached
to each middle vertex is even, including any permutation of middle vertices. -/
theorem coupled_path_sign {V M : Type*} [DecidableEq V] [Fintype V] [DecidableEq M] [Fintype M]
    (σ : Perm V) (τ : Perm M) :
    sign (Equiv.sumCongr (1 : Perm Unit)
      (Equiv.sumCongr (Equiv.sumCongr σ σ) (prodCongrLeft (fun _ : Fin 4 => τ)))) = 1 := by
  rw [sign_sumCongr, sign_sumCongr, sign_sumCongr, sign_prodCongrLeft]
  simp only [map_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.units_mul_self, one_mul]
  rcases Int.units_eq_one_or (sign τ) with h | h
  · simp [h]
  · rw [h, show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_two (-1 : ℤˣ),
        Int.units_mul_self, one_pow]

/-- Exchanging two parallel copies of an odd-size path basis is odd. -/
theorem odd_component_exchange {V : Type*} [DecidableEq V] [Fintype V]
    (k : ℕ) (h : Fintype.card V = 2*k+1) :
    sign (prodCongrRight (fun _ : V => swap false true)) = -1 := by
  rw [sign_prodCongrRight]
  simp only [sign_swap (by decide : false ≠ true), Finset.prod_const, Finset.card_univ, h,
    pow_add, pow_mul, pow_one]
  have hs : (-1 : ℤˣ)^2 = 1 := by rw [pow_two, Int.units_mul_self]
  simp [hs]

/-- Divisibility along a source-to-sink route forces a vertex with
at least p² paths through it when p is prime. -/
theorem prime_path_budget {p : ℕ} (hp : p.Prime) (R L : ℕ → ℕ) (t : ℕ)
    (hR : ∀ i ≤ t, 0 < R i) (hL : ∀ i ≤ t, 0 < L i)
    (start : ¬ p ∣ R 0) (finish : p ∣ R t)
    (edge : ∀ i < t, p ∣ R i * L (i+1)) :
    ∃ i ≤ t, p*p ≤ R i * L i := by
  induction t with
  | zero => exact (start finish).elim
  | succ t ih =>
    by_cases hd : p ∣ R t
    · obtain ⟨i, hi, hb⟩ := ih
        (fun i hi => hR i (Nat.le.step hi))
        (fun i hi => hL i (Nat.le.step hi)) hd
        (fun i hi => edge i (Nat.lt_succ_of_lt hi))
      exact ⟨i, Nat.le.step hi, hb⟩
    · have hl : p ∣ L (t+1) := ((hp.dvd_mul.mp (edge t (Nat.lt_succ_self _))).resolve_left hd)
      exact ⟨t+1, le_rfl, Nat.mul_le_mul (Nat.le_of_dvd (hR _ le_rfl) finish)
        (Nat.le_of_dvd (hL _ le_rfl) hl)⟩

/-- An action repeated on s independent column spaces has an s-th power determinant. -/
theorem determinant_repeated_blocks {R n : Type*} [CommRing R] [Fintype n]
    [DecidableEq n] (s : ℕ) (M : Matrix n n R) :
    (Matrix.blockDiagonal fun _ : Fin s => M).det = M.det ^ s := by
  rw [Matrix.det_blockDiagonal]
  simp

/-- An isomorphism and its contragredient have cancelling determinants. -/
theorem determinant_dual_pair {R n : Type*} [CommRing R] [Fintype n]
    [DecidableEq n] (M N : Matrix n n R) (h : N * M = 1) :
    N.transpose.det * M.det = 1 := by
  rw [Matrix.det_transpose, ← Matrix.det_mul, h, Matrix.det_one]

end DetRatioFour.Quiver
