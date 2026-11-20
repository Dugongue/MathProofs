import EvenPrimaryMoment
import EvenPrimaryGate
import EvenPrimaryMarginal

open scoped BigOperators Classical

namespace EvenTI.Primary

open Matrix Mathproof.Problem17PrimaryTail Mathproof.Problem17RepeatedBudget

noncomputable section

variable {K Ω ι : Type*} [Field K] [Fintype K] [Fintype Ω] [Fintype ι] [Nonempty ι]

theorem gate_of_uniform_matrix_marginals {n : ℕ} (hn : 2 ≤ n)
    (A : ι → Ω → SquareMatrix K n) (δ : ℝ)
    (hcap : ∀ B : SquareMatrix K n, (repeatedBudget B.charpoly : ℝ) ≤ (n*(2*n+4) : ℕ))
    (hL : ∀ i, (∑ y, |weight (A i) y - (Fintype.card (SquareMatrix K n):ℝ)⁻¹|) ≤ δ) :
    event (fun x => n^(Fintype.card ι) <
      (Fintype.card K)^(∑ i, repeatedBudget (A i x).charpoly)) ≤
      ((budgetConstant K + (n*(2*n+4) : ℕ) * δ) * Real.log (Fintype.card K)) / Real.log n := by
  let M : ℝ := (n*(2*n+4) : ℕ)
  have hM : 0 ≤ M := by positivity
  have hB (i : ι) :
      mean (fun x => (repeatedBudget (A i x).charpoly : ℝ)) ≤ budgetConstant K + M * δ := by
    have h := mean_comp_le_uniform_add_l1 (A i)
      (fun y => (repeatedBudget y.charpoly : ℝ)) M δ hM
      (fun y => ⟨by positivity, hcap y⟩) (hL i)
    exact h.trans (add_le_add (mean_matrix_budget_le (K := K) n) le_rfl)
  exact event_pow_gate_le (fun i x => repeatedBudget (A i x).charpoly) _ hB _ _ Fintype.one_lt_card hn

theorem gate_of_uniform_trace_marginals {n : ℕ} (hn : 2 ≤ n) (traceValue : ι → K)
    (A : ∀ i, Ω → {B : SquareMatrix K n // B.trace = traceValue i}) (δ : ℝ)
    (hcap : ∀ B : SquareMatrix K n, (repeatedBudget B.charpoly : ℝ) ≤ (n*(2*n+4) : ℕ))
    (hL : ∀ i, (∑ y, |weight (A i) y -
      (Fintype.card {B : SquareMatrix K n // B.trace = traceValue i}:ℝ)⁻¹|) ≤ δ) :
    event (fun x => n^(Fintype.card ι) <
      (Fintype.card K)^(∑ i, repeatedBudget (A i x).val.charpoly)) ≤
      ((budgetConstant K + (n*(2*n+4) : ℕ) * δ) * Real.log (Fintype.card K)) / Real.log n := by
  let M : ℝ := (n*(2*n+4) : ℕ)
  have hM : 0 ≤ M := by positivity
  have hB (i : ι) :
      mean (fun x => (repeatedBudget (A i x).val.charpoly : ℝ)) ≤ budgetConstant K + M * δ := by
    have h := mean_comp_le_uniform_add_l1 (A i)
      (fun y => (repeatedBudget y.val.charpoly : ℝ)) M δ hM
      (fun y => ⟨by positivity, hcap y.val⟩) (hL i)
    exact h.trans (add_le_add (mean_trace_budget_le n (by omega) (traceValue i)) le_rfl)
  exact event_pow_gate_le (fun i x => repeatedBudget (A i x).val.charpoly) _ hB _ _ Fintype.one_lt_card hn

#print axioms gate_of_uniform_matrix_marginals
#print axioms gate_of_uniform_trace_marginals

end
end EvenTI.Primary
