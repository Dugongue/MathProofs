import EvenP3Coverage
import EvenP4OrderFourDecay

namespace Mathproof.EvenTI.OrderFour

open Filter EvenTI.Primary
open Mathproof.EvenTI.Reciprocal.Coverage Mathproof.Problem17PrimaryTail
open scoped Topology Classical

noncomputable section

/-- The exact raw spectral rejection upper bound from the order-four theorem. -/
def orderFourCoverageBound (K : Type*) [Field K] [Fintype K] (n : ℕ) : ℝ :=
  (2 / (n : ℝ) + 8 / (↑(n/2) : ℝ)^2 +
    2 * (8 * (budgetConstant K + 1) + 34) * Real.log (Fintype.card K) / Real.log n) +
  4 * (budgetConstant K + (↑(n^2) : ℝ) * squareReciprocalError K n) *
    Real.log (Fintype.card K) / Real.log n

theorem tendsto_orderFourCoverageBound (K : Type*) [Field K] [Fintype K] :
    Tendsto (orderFourCoverageBound K) atTop (𝓝 0) := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hh2 : Tendsto (fun n : ℕ => 8 / (↑(n/2) : ℝ)^2) atTop (𝓝 0) := by
    have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_nat_div_const_atTop 2 (by decide))).pow 2
    simpa only [Function.comp_apply, div_pow, one_pow, zero_pow (by decide : (2:ℕ) ≠ 0),
      mul_one_div, mul_zero] using h.const_mul (8 : ℝ)
  have hfirst : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  have hsing : Tendsto (fun n : ℕ =>
      2 * (8 * (budgetConstant K + 1) + 34) * Real.log (Fintype.card K) / Real.log n)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hq : 1 < (Fintype.card K : ℝ) := by
    exact_mod_cast Fintype.one_lt_card (α := K)
  have hscaled := tendsto_scaled_squareReciprocalError K hq
  have hrec : Tendsto (fun n : ℕ => 4 * (budgetConstant K + (↑(n^2) : ℝ) *
      squareReciprocalError K n) * Real.log (Fintype.card K) / Real.log n)
      atTop (𝓝 0) := by
    have hm := ((hscaled.const_add (budgetConstant K)).const_mul (4 : ℝ)).mul_const
      (Real.log (Fintype.card K : ℝ))
    simpa only [Nat.cast_pow, Function.comp_apply] using hm.div_atTop hlog
  unfold orderFourCoverageBound
  simpa only [add_zero] using ((hfirst.add hh2).add hsing).add hrec

/-- An eventual epsilon bound for rejection on the actual raw order-four source. -/
theorem orderFour_shape_rejection_eventually_le (K : Type*) [Field K] [Fintype K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 10^19 ≤ N ∧ ∀ n, N ≤ n → ∀ h5 : 5 ≤ n,
      event (fun T : Four K n => ¬ orderFourShapeAccepted h5 T) ≤ ε := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_orderFourCoverageBound K).eventually_lt_const hε)
  refine ⟨max M (10^19), le_max_right _ _, fun n hn h5 => ?_⟩
  have hbig : 10^19 ≤ n := (le_max_right M _).trans hn
  have hbound : orderFourCoverageBound K n < ε := hM n ((le_max_left M _).trans hn)
  exact (orderFour_shape_coverage (K := K) hbig).trans hbound.le

#print axioms tendsto_orderFourCoverageBound
#print axioms orderFour_shape_rejection_eventually_le

end
end Mathproof.EvenTI.OrderFour
