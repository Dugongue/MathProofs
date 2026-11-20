import EvenPrimaryRates
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators Polynomial Classical

namespace EvenTI.Primary

open Polynomial Matrix Mathproof.Problem17PrimaryTail Mathproof.Problem17RepeatedBudget

noncomputable section

variable {K : Type*} [Field K] [Fintype K]

def degreeMass (q : ℝ) (d : ℕ) : ℝ := d * (q⁻¹)^d
def thresholdMass (k : ℕ) : ℝ := (2*(k:ℝ)+3)^2 * (2/3:ℝ)^k

theorem degreeMass_summable {q : ℝ} (hq : 1 < q) : Summable (degreeMass q) := by
  have hq0 : 0 < q := by linarith
  change Summable (fun d : ℕ => (d:ℝ)*(q⁻¹)^d)
  simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (r := q⁻¹) (by rw [Real.norm_of_nonneg (by positivity)]; exact inv_lt_one_of_one_lt₀ hq)

theorem thresholdMass_summable : Summable thresholdMass := by
  have h : ‖(2/3:ℝ)‖ < 1 := by norm_num
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 h
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 h
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 h
  refine (((h2.mul_left 4).add (h1.mul_left 12)).add (h0.mul_left 9)).congr ?_
  intro k
  change (4*((k:ℝ)^2*(2/3:ℝ)^k) + 12*((k:ℝ)^1*(2/3:ℝ)^k)) +
    9*((k:ℝ)^0*(2/3:ℝ)^k) = thresholdMass k
  unfold thresholdMass
  ring

theorem degreeMass_nonneg (q : ℝ) (hq : 0 ≤ q) (d : ℕ) : 0 ≤ degreeMass q d := by
  unfold degreeMass
  positivity

theorem thresholdMass_nonneg (k : ℕ) : 0 ≤ thresholdMass k := by
  unfold thresholdMass
  positivity

def budgetConstant (K : Type*) [Fintype K] : ℝ :=
  (4 * fieldSize K ^ 3) * (∑' d, degreeMass (fieldSize K) d) * ∑' k, thresholdMass k

theorem budgetConstant_nonneg : 0 ≤ budgetConstant K := by
  have hq : 0 ≤ fieldSize K := by linarith [fieldSize_two_le (K := K)]
  unfold budgetConstant
  exact mul_nonneg (mul_nonneg (by positivity)
    (tsum_nonneg fun d => degreeMass_nonneg _ hq d))
    (tsum_nonneg thresholdMass_nonneg)

theorem mean_budget_of_tail {Ω : Type*} [Fintype Ω] (f : Ω → K[X]) (n : ℕ)
    (hne : ∀ A, f A ≠ 0) (hdeg : ∀ A, (f A).natDegree ≤ n)
    (C : ℝ) (hC : 0 ≤ C)
    (hTail : ∀ (p : K[X]), p.Monic → Irreducible p → ∀ k : ℕ,
      event (fun x => p^(2*(k+1)) ∣ f x) ≤
        C * ((fieldSize K)⁻¹)^(2*p.natDegree) * (2/3:ℝ)^k) :
    mean (fun A => (repeatedBudget (f A) : ℝ)) ≤
      C * (∑' d, degreeMass (fieldSize K) d) * ∑' k, thresholdMass k := by
  let q := fieldSize K
  let T := Finset.range (n+1)
  have hq : 1 < q := by linarith [fieldSize_two_le (K := K)]
  have hq0 : 0 < q := by linarith
  have hd (d : Fin (n+1)) :
      (∑ p : DegreeIrreducible K d, ∑ k ∈ T,
        thresholdWeight d k * event (fun x => p.val^(2*(k+1)) ∣ f x)) ≤
      C * degreeMass q d * ∑ k ∈ T, thresholdMass k := by
    let numer k := thresholdWeight d k * (C * (q⁻¹)^(2*d.val) * (2/3:ℝ)^k)
    have hnum (k : ℕ) : 0 ≤ numer k := by
      unfold numer thresholdWeight
      positivity
    have hs : (Fintype.card (DegreeIrreducible K d) : ℝ) ≤ q^d.val := by
      rw [show q = (Fintype.card K : ℝ) from rfl, ← Nat.cast_pow]
      exact_mod_cast degreeIrreducible_card_le (K := K) d
    have hstep (k : ℕ) : q^d.val * numer k = C * degreeMass q d * thresholdMass k := by
      have hcancel : q^d.val * (q⁻¹)^(2*d.val) = (q⁻¹)^d.val := by
        rw [two_mul, pow_add, inv_pow]
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul]
      unfold numer thresholdWeight degreeMass thresholdMass
      push_cast
      calc
        _ = (q^d.val * (q⁻¹)^(2*d.val)) *
            (C * (d.val:ℝ) * (2*(k:ℝ)+3)^2 * (2/3:ℝ)^k) := by ring
        _ = _ := by rw [hcancel]; ring
    calc
      _ ≤ ∑ _p : DegreeIrreducible K d, ∑ k ∈ T, numer k := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ (by unfold thresholdWeight; positivity)
        simpa only [p.property.2.2] using hTail p.val p.property.1 p.property.2.1 k
      _ = (Fintype.card (DegreeIrreducible K d) : ℝ) * ∑ k ∈ T, numer k := by
        simp
      _ ≤ q^d.val * ∑ k ∈ T, numer k :=
        mul_le_mul_of_nonneg_right hs (Finset.sum_nonneg fun k _ => hnum k)
      _ = _ := by simp only [Finset.mul_sum, hstep]
  have htd : (∑ d : Fin (n+1), degreeMass q d) ≤ ∑' d, degreeMass q d := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (degreeMass_summable hq).sum_le_tsum T fun i _ => degreeMass_nonneg _ hq0.le i
  have htt : (∑ k ∈ T, thresholdMass k) ≤ ∑' k, thresholdMass k :=
    thresholdMass_summable.sum_le_tsum T fun k _ => thresholdMass_nonneg k
  calc
    _ ≤ _ := mean_budget_le_threshold_events f n hne hdeg
    _ ≤ ∑ d : Fin (n+1), C * degreeMass q d * ∑ k ∈ T, thresholdMass k :=
      Finset.sum_le_sum fun d _ => hd d
    _ = C * (∑ d : Fin (n+1), degreeMass q d) * ∑ k ∈ T, thresholdMass k := by
      calc
        _ = (∑ d : Fin (n+1), C * degreeMass q d) * ∑ k ∈ T, thresholdMass k :=
          (Finset.sum_mul _ _ _).symm
        _ = _ := by rw [← Finset.mul_sum]
    _ ≤ _ := by
      have hT0 : 0 ≤ ∑ k ∈ T, thresholdMass k :=
        Finset.sum_nonneg fun k _ => thresholdMass_nonneg k
      have hD0 : 0 ≤ ∑' d, degreeMass q d :=
        tsum_nonneg fun d => degreeMass_nonneg _ hq0.le d
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htd hC) hT0).trans
        (mul_le_mul_of_nonneg_left htt (mul_nonneg hC hD0))

set_option maxHeartbeats 500000 in
theorem mean_trace_budget_le (n : ℕ) (hn : 0 < n) (a : K) :
    mean (fun A : {A : SquareMatrix K n // A.trace = a} =>
      (repeatedBudget A.val.charpoly : ℝ)) ≤ budgetConstant K := by
  unfold budgetConstant
  have hq : 0 ≤ fieldSize K := by linarith [fieldSize_two_le (K := K)]
  let f := fun A : {A : SquareMatrix K n // A.trace = a} => A.val.charpoly
  have hTail (p : K[X]) (hp : p.Monic) (hi : Irreducible p) (k : ℕ) :
      event (fun x => p^(2*(k+1)) ∣ f x) ≤
        (4 * fieldSize K ^ 3) * ((fieldSize K)⁻¹)^(2*p.natDegree) * (2/3:ℝ)^k :=
    event_trace_threshold_le p hp hi n k hn a
  exact mean_budget_of_tail f n (fun A => A.val.charpoly_monic.ne_zero)
    (fun A => by simp [f]) (4 * fieldSize K^3) (by positivity) hTail

theorem mean_matrix_budget_le (n : ℕ) :
    mean (fun A : SquareMatrix K n => (repeatedBudget A.charpoly : ℝ)) ≤ budgetConstant K := by
  unfold budgetConstant
  have hq : 2 ≤ fieldSize K := fieldSize_two_le
  have hq0 : 0 ≤ fieldSize K := by linarith
  refine (mean_budget_of_tail (fun (A : SquareMatrix K n) => A.charpoly) n
    (fun A => A.charpoly_monic.ne_zero) (fun A => by simp) (4 * fieldSize K ^ 2) (by positivity)
    (fun p hp hi k => event_matrix_threshold_le p hp hi n k)).trans ?_
  have hp : (0:ℝ) ≤ ∑' d, degreeMass (fieldSize K) d :=
    tsum_nonneg fun d => degreeMass_nonneg _ hq0 d
  have ht : (0:ℝ) ≤ ∑' k, thresholdMass k := tsum_nonneg thresholdMass_nonneg
  have hc : (4 * fieldSize K ^ 2) ≤ 4 * fieldSize K ^ 3 := by
    have he := (show (1:ℝ) ≤ fieldSize K by linarith)
    calc
      _ = (4 * fieldSize K ^ 2) * 1 := (mul_one _).symm
      _ ≤ (4 * fieldSize K ^ 2) * fieldSize K := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hp) ht

#print axioms mean_matrix_budget_le
#print axioms mean_trace_budget_le

end
end EvenTI.Primary
