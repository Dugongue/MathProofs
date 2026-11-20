import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic
import Mathproof.Meta.Problem18FiniteProducts20260929

/-! A narrow source for exact full-row-rank probability and its uniform
finite-product lower bound. The count uses Mathlib's cardinality of independent
tuples and does not import the large historical tensor module. -/

namespace Mathproof.Problem18RankDensity20260929

open Finset
open Mathproof.Problem18FiniteProducts20260929

variable {K : Type*} [Field K] [Fintype K]

set_option backward.isDefEq.respectTransparency false in
private theorem full_row_rank_iff_independent {d n : ℕ}
    (M : Matrix (Fin d) (Fin n) K) :
    M.rank = d ↔ LinearIndependent K M := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.card_fin, Set.finrank]
  change M.rank = d ↔ d = Module.finrank K (Submodule.span K (Set.range M.row))
  rw [← Matrix.rank_eq_finrank_span_row]
  exact eq_comm

/-- Exact full-row-rank count over a finite field. -/
theorem fullRowRank_card {d n : ℕ} (hd : d ≤ n) :
    Nat.card {M : Matrix (Fin d) (Fin n) K // M.rank = d} =
      ∏ a : Fin d, (Fintype.card K ^ n - Fintype.card K ^ a.val) := by
  let e : {M : Matrix (Fin d) (Fin n) K // M.rank = d} ≃
      {M : Fin d → Fin n → K // LinearIndependent K M} :=
    Equiv.subtypeEquivRight (fun M => full_row_rank_iff_independent M)
  rw [Nat.card_congr e]
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    (card_linearIndependent (K := K) (V := Fin n → K)
      (by simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hd))

/-- Exact probability as a product of row-extension success factors. -/
theorem fullRowRank_probability {d n : ℕ} (hd : d ≤ n) :
    (Nat.card {M : Matrix (Fin d) (Fin n) K // M.rank = d} : ℝ) /
      Nat.card (Matrix (Fin d) (Fin n) K) =
      ∏ a : Fin d,
        (1 - (Fintype.card K : ℝ) ^ a.val / (Fintype.card K : ℝ) ^ n) := by
  rw [fullRowRank_card hd]
  have hq : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn (a : Fin d) : Fintype.card K ^ a.val ≤ Fintype.card K ^ n := by
    exact Nat.pow_le_pow_right Fintype.card_pos (Nat.le_of_lt a.isLt |>.trans hd)
  have hcard : Nat.card (Matrix (Fin d) (Fin n) K) =
      Fintype.card K ^ (d * n) := by
    simp [Matrix, Nat.card_eq_fintype_card, ← pow_mul, Nat.mul_comm]
  rw [hcard, Nat.cast_prod, Nat.cast_pow]
  have he : (Fintype.card K : ℝ) ^ (d * n) =
      ∏ _a : Fin d, (Fintype.card K : ℝ) ^ n := by
    simp [← pow_mul, Nat.mul_comm]
  rw [he, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [Nat.cast_sub (hn a), Nat.cast_pow, Nat.cast_pow]
  field_simp

private theorem glFactor_eq_squareProduct
    (q : ℝ) (hq : 0 < q) (d : ℕ) :
    glFactor q d = ∏ a : Fin d, (1 - q ^ a.val / q ^ d) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  unfold glFactor
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => 1 - q ^ j / q ^ d) d]
  rw [← Finset.prod_range_reflect (fun j : ℕ => 1 - q ^ j / q ^ d) d]
  apply Finset.prod_congr rfl
  intro j hj
  have hjd : j < d := Finset.mem_range.mp hj
  have hle : d - 1 - j ≤ d := by omega
  have hsub : d - (d - 1 - j) = j + 1 := by omega
  rw [← hsub, inv_pow_sub₀ hq0 hle]
  ring

/-- The exact full-row-rank source fraction for every rectangular d-by-n
matrix is at least the square GL normalization product. -/
theorem fullRowRank_density_ge_glFactor {d n : ℕ} (hd : d ≤ n) :
    glFactor (Fintype.card K : ℝ) d ≤
      (Nat.card {M : Matrix (Fin d) (Fin n) K // M.rank = d} : ℝ) /
        Nat.card (Matrix (Fin d) (Fin n) K) := by
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by
    dsimp [q]
    have h : (1 : ℝ) < Fintype.card K := by
      exact_mod_cast Fintype.one_lt_card (α := K)
    exact h.le
  rw [glFactor_eq_squareProduct q hq]
  rw [fullRowRank_probability hd]
  apply Finset.prod_le_prod
  · intro a _
    have hpow : q ^ a.val ≤ q ^ d :=
      pow_le_pow_right₀ hq1 (Nat.le_of_lt a.isLt)
    have hqpow : 0 < q ^ d := pow_pos hq _
    have hdiv : q ^ a.val / q ^ d ≤ 1 := (div_le_one hqpow).2 hpow
    linarith
  · intro a _
    have hpow : q ^ d ≤ q ^ n := pow_le_pow_right₀ hq1 hd
    have hdiv : q ^ a.val / q ^ n ≤ q ^ a.val / q ^ d :=
      div_le_div_of_nonneg_left (pow_nonneg hq.le _) (pow_pos hq _) hpow
    linarith

/-- Absolute full-row-rank density over every finite field, including
characteristic two. -/
theorem fullRowRank_density_ge_quarter {d n : ℕ} (hd : d ≤ n) :
    (1 / 4 : ℝ) ≤
      (Nat.card {M : Matrix (Fin d) (Fin n) K // M.rank = d} : ℝ) /
        Nat.card (Matrix (Fin d) (Fin n) K) := by
  have hq : (2 : ℝ) ≤ Fintype.card K := by
    have hn : 2 ≤ Fintype.card K := by
      have h := Fintype.one_lt_card (α := K)
      omega
    exact_mod_cast hn
  exact (glFactor_lower_quarter _ hq d).trans
    (fullRowRank_density_ge_glFactor hd)

/-- Stronger absolute density in odd-sized finite fields. -/
theorem fullRowRank_density_ge_half {d n : ℕ}
    (hd : d ≤ n) (hq : 3 ≤ Fintype.card K) :
    (1 / 2 : ℝ) ≤
      (Nat.card {M : Matrix (Fin d) (Fin n) K // M.rank = d} : ℝ) /
        Nat.card (Matrix (Fin d) (Fin n) K) := by
  have hq' : (3 : ℝ) ≤ Fintype.card K := by exact_mod_cast hq
  exact (glFactor_lower_half _ hq' d).trans
    (fullRowRank_density_ge_glFactor hd)

/-- Two-thirds density over fields of size at least four. -/
theorem fullRowRank_density_ge_twoThirds {d n : ℕ}
    (hd : d ≤ n) (hq : 4 ≤ Fintype.card K) :
    (2 / 3 : ℝ) ≤
      (Nat.card {M : Matrix (Fin d) (Fin n) K // M.rank = d} : ℝ) /
        Nat.card (Matrix (Fin d) (Fin n) K) := by
  have hq' : (4 : ℝ) ≤ Fintype.card K := by exact_mod_cast hq
  exact (glFactor_lower_twoThirds _ hq' d).trans
    (fullRowRank_density_ge_glFactor hd)

end Mathproof.Problem18RankDensity20260929
