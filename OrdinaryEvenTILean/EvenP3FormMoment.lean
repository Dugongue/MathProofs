import EvenP2Corank
import EvenP2FormsRank

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical Matrix
open Matrix Module EvenTI.Primary EvenTI.Action
open Mathproof.EvenTI.Singular.Coverage Mathproof.EvenTI.Singular.Forms
open Mathproof.EvenOrdinaryTISingular
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_one)

noncomputable section

private theorem square_le_double_pow_two (k : ℕ) : k^2 ≤ 2 * 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases hk : 3 ≤ k
    · have hm := Nat.mul_le_mul_right (k+1) hk
      have hstep : (k+1)^2 ≤ 2*k^2 := by nlinarith
      calc
        _ ≤ 2*k^2 := hstep
        _ ≤ 2*(2*2^k) := Nat.mul_le_mul_left 2 ih
        _ = _ := by rw [pow_succ]; ring
    · interval_cases k <;> norm_num

private theorem kernel_indicator_count {K V W : Type*}
    [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    (∑ v : V, if f v = 0 then (1 : ℝ) else 0) =
      ((Fintype.card K ^ finrank K f.ker : ℕ) : ℝ) := by
  letI : Fintype f.ker := Fintype.ofFinite _
  rw [← Module.card_eq_pow_finrank (K := K) (V := f.ker)]
  simp only [Finset.sum_boole]
  congr 1
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.refl f.ker)

theorem mean_kernel_size_le_two {K V W Ω : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup W] [Module K W] [Fintype Ω]
    (A : Ω → V →ₗ[K] W)
    (h0 : ∀ v : V, v ≠ 0 → event (fun x => A x v = 0) ≤ (Fintype.card V : ℝ)⁻¹) :
    mean (fun x => ((Fintype.card K ^ finrank K (A x).ker : ℕ) : ℝ)) ≤ 2 := by
  simp only [← kernel_indicator_count, mean_sum]
  change (∑ v : V, event (fun x => A x v = 0)) ≤ 2
  calc
    _ ≤ ∑ v : V, ((if v = 0 then 1 else 0) + (Fintype.card V : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v = 0
      · rw [if_pos hv]
        have h1 : event (fun x => A x v = 0) ≤ 1 := by
          rw [event_as_fraction]
          exact uniformFraction_le_one _
        exact h1.trans (le_add_of_nonneg_right (by positivity))
      · simpa [hv] using h0 v hv
    _ = 2 := by
      have hc : (Fintype.card V : ℝ) ≠ 0 := by positivity
      simp [Finset.sum_add_distrib, hc, one_add_one_eq_two]

theorem mean_square_kernel_dimension_le_four {K V W Ω : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup W] [Module K W] [Fintype Ω]
    (A : Ω → V →ₗ[K] W)
    (h0 : ∀ v : V, v ≠ 0 → event (fun x => A x v = 0) ≤ (Fintype.card V : ℝ)⁻¹) :
    mean (fun x => ((finrank K (A x).ker ^ 2 : ℕ) : ℝ)) ≤ 4 := by
  have h (x : Ω) : (finrank K (A x).ker ^ 2 : ℕ) ≤
      2 * Fintype.card K ^ finrank K (A x).ker :=
    (square_le_double_pow_two _).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left Fintype.one_lt_card _))
  have hp (x : Ω) : (↑(finrank K (A x).ker ^ 2) : ℝ) ≤
      2 * ↑(Fintype.card K ^ finrank K (A x).ker) := by exact_mod_cast h x
  have hm := mean_mono hp
  rw [mean_mul] at hm
  exact hm.trans (by linarith only [mean_kernel_size_le_two A h0])

theorem mean_square_matrix_defect {K I J : Type*} [Field K] [Fintype K]
    [Fintype I] [Fintype J] [DecidableEq J] (hsize : Fintype.card I = Fintype.card J) :
    mean (fun M : Matrix I J K => ((Fintype.card I - M.rank)^2 : ℕ)) ≤ 4 := by
  have he (M : Matrix I J K) :
      Fintype.card I - M.rank = finrank K M.mulVecLin.ker := by
    have hc := M.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_fintype_fun_eq_card, ← hsize] at hc
    change M.rank + finrank K M.mulVecLin.ker = Fintype.card I at hc
    omega
  simp_rw [he]
  apply mean_square_kernel_dimension_le_four (fun M : Matrix I J K => M.mulVecLin)
  intro v hv
  change event (fun M : Matrix I J K => M.mulVec v = 0) ≤ _
  rw [event_as_fraction, mulVec_zero_fraction v hv, Fintype.card_fun, hsize, Nat.cast_pow, one_div]

def formDefect {K : Type*} [Field K] {n : ℕ} (x : Coord (1+1) n → K) : ℕ :=
  n - (retainedForm (0 : Fin (1+1)) x).rank

private theorem mean_same_fintype {A : Type*} (F G : Fintype A) (f : A → ℝ) :
    @mean A F f = @mean A G f := by
  obtain rfl := Subsingleton.elim F G
  rfl

theorem mean_square_form_defect {K : Type*} [Field K] [Fintype K] {n : ℕ} :
    mean (fun x : Coord (1+1) n → K => (formDefect x ^ 2 : ℕ)) ≤ 4 := by
  let e := retainedFormEquiv (K := K) (n := n) (0 : Fin (1+1))
  let f (M : Matrix (Fin n) (Coord 1 n) K) : ℝ := ((n-M.rank)^2 : ℕ)
  change mean (f ∘ e) ≤ 4
  unfold mean
  change (∑ x, f (e x)) / Fintype.card (Coord (1+1) n → K) ≤ 4
  rw [Equiv.sum_comp e f, Fintype.card_congr e]
  change mean f ≤ 4
  have h := mean_square_matrix_defect (K := K) (I := Fin n) (J := Coord 1 n)
    (by simp only [Fintype.card_fin, cut_side_card, pow_one])
  rw [Fintype.card_fin] at h
  exact (mean_same_fintype _ _ f).le.trans h

#print axioms mean_square_kernel_dimension_le_four
#print axioms mean_square_form_defect

end
end Mathproof.EvenTI.OrderFour
