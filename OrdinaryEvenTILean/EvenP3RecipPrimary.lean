import EvenP3RecipCoverage
import EvenP2SpectralBasic

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Matrix Classical
open Matrix EvenTI.Primary EvenTI.Action
open Mathproof.Problem17PrimaryTail Mathproof.Problem17RepeatedBudget
open Mathproof.EvenTI.Singular.Coverage (primary_pointwise_cap)

noncomputable section

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

abbrev FourModes := Bool × Fin 2

def squareDenseModeAnchor (hn : 5 ≤ n) (i : FourModes) (T : InvertibleCut K 2 n) :
    Matrix (Fin n) (Fin n) K :=
  denseAnchor (squareLeftRegroup hn 0) (rightRegroup i.2) (orientCut i.1 T)

def squareReciprocalBudget (hn : 5 ≤ n) (T : InvertibleCut K 2 n) : ℕ :=
  ∑ i : FourModes, repeatedBudget (squareDenseModeAnchor hn i T).charpoly

private theorem mode_primary_mean (hn : 10^19 ≤ n) (i : FourModes) :
    mean (fun T : InvertibleCut K 2 n =>
      (repeatedBudget (squareDenseModeAnchor (by omega) i T).charpoly : ℝ)) ≤
      budgetConstant K + (↑(n^2) : ℝ) * squareReciprocalError K n := by
  let eL := squareLeftRegroup (show 5 ≤ n by omega) 0
  let eR := rightRegroup (l := 1) (n := n) i.2
  let o := orientCut (K := K) (s := 2) (n := n) i.1
  let B : ℝ := ↑(n^2)
  have hcap (A : Matrix (Fin n) (Fin n) K) : (repeatedBudget A.charpoly : ℝ) ≤ B :=
    primary_pointwise_cap A
  have h := orderFour_reciprocal_coverage (K := K) hn 0 i.2 i.1
  by_cases h₂ : (2 : K) = 0
  · letI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by simpa using h₂)
    have hL := h.1
    let f (y : AnchorTrace K (SquareRows n) (Fin n)) : ℝ := repeatedBudget y.val.charpoly
    have hb := mean_comp_le_uniform_add_l1 (denseTraceAnchor eL eR ∘ o) f B
      (squareReciprocalError K n) (by dsimp [B]; positivity)
      (fun y => ⟨by dsimp [f]; positivity, hcap y.val⟩) hL
    have hm := mean_trace_budget_le (K := K) n (by omega) ((Fintype.card (SquareRows n) : K)^2)
    exact hb.trans (add_le_add hm le_rfl)
  · let f (y : Matrix (Fin n) (Fin n) K) : ℝ := repeatedBudget y.charpoly
    have hb := mean_comp_le_uniform_add_l1 (denseAnchor eL eR ∘ o) f B (squareReciprocalError K n)
      (by dsimp [B]; positivity) (fun y => ⟨by dsimp [f]; positivity, hcap y⟩) (h.2 h₂)
    exact hb.trans (add_le_add (mean_matrix_budget_le (K := K) n) le_rfl)

/-- The original joint q^D ≤ n spectral gate on the invertible cut. -/
theorem orderFour_reciprocal_gate (hn : 10^19 ≤ n) :
    event (fun T : InvertibleCut K 2 n => n < Fintype.card K ^ squareReciprocalBudget (by omega) T) ≤
      4 * (budgetConstant K + (↑(n^2) : ℝ) * squareReciprocalError K n) *
        Real.log (Fintype.card K) / Real.log n := by
  let D (i : FourModes) (T : InvertibleCut K 2 n) : ℕ :=
    repeatedBudget (squareDenseModeAnchor (by omega) i T).charpoly
  let X (i : FourModes) (T : InvertibleCut K 2 n) : ℕ := 4 * D i T
  let B : ℝ := budgetConstant K + (↑(n^2) : ℝ) * squareReciprocalError K n
  have hX (i : FourModes) : mean (fun T => (X i T : ℝ)) ≤ 4 * B := by
    dsimp only [X]
    rw [show (fun T => (↑(4 * D i T) : ℝ)) = fun T => 4 * (D i T : ℝ) by
      funext T; norm_num [Nat.cast_mul], mean_mul]
    exact mul_le_mul_of_nonneg_left (mode_primary_mean hn i) (by norm_num)
  have hm := event_pow_gate_le X _ hX (Fintype.card K) n Fintype.one_lt_card (by omega)
  refine le_trans ?_ hm
  apply mean_mono
  intro T
  by_cases h : n < Fintype.card K ^ squareReciprocalBudget (by omega) T
  · have hh : n ^ Fintype.card FourModes < Fintype.card K ^ (∑ i, X i T) := by
      have hsum : (∑ i, X i T) = (∑ i, D i T) * 4 := by
        dsimp only [X]
        rw [← Finset.mul_sum, Nat.mul_comm 4]
      have hc : Fintype.card FourModes = 4 := by decide
      rw [hc, hsum, pow_mul]
      exact Nat.pow_lt_pow_left h (by decide)
    simp only [if_pos h, if_pos hh, le_refl]
  · rw [if_neg h]
    split <;> norm_num

#print axioms orderFour_reciprocal_gate

end
end Mathproof.EvenTI.Reciprocal.Coverage
