import EvenPrimaryEnvelope
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Mathproof.EvenTI.GlobalCoverage

open scoped BigOperators Classical
open EvenTI.Primary Filter

noncomputable section

theorem event_le_of_imp {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : event P ≤ event Q := by
  unfold event
  apply mean_mono
  intro a
  by_cases hp : P a
  · simp [hp, h a hp]
  · simp only [if_neg hp]
    split <;> norm_num

theorem event_union_le {A : Type*} [Fintype A] (P Q : A → Prop) :
    event (fun a => P a ∨ Q a) ≤ event P + event Q := by
  unfold event mean
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq]

theorem failure_of_intersection_le {A : Type*} [Fintype A] (P Q : A → Prop) :
    event (fun a => ¬(P a ∧ Q a)) ≤ event (fun a => ¬P a) + event (fun a => ¬Q a) :=
  (event_le_of_imp fun _ h => not_and_or.mp h).trans (event_union_le _ _)

theorem two_over_n_le_log (n : ℕ) (hn : 2 ≤ n) :
    2 / (n : ℝ) ≤ 2 / Real.log n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact div_le_div_of_nonneg_left (by norm_num) (Real.log_pos h1)
    (Real.log_le_self (by positivity))

/-- Both exponential remainder terms can be paid by the same logarithmic
bound, for every field size and every sufficiently large side length. -/
theorem inverse_pow_le_inv_log (q n e : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) (he : n ≤ e) :
    ((q : ℝ)^e)⁻¹ ≤ 1 / Real.log n := by
  have hnReal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hne : n ≤ q^e := calc
    n ≤ 2^n := Nat.lt_two_pow_self.le
    _ ≤ q^n := Nat.pow_le_pow_left hq n
    _ ≤ q^e := Nat.pow_le_pow_right (by omega) he
  have hpow : (n : ℝ) ≤ (q : ℝ)^e := by exact_mod_cast hne
  rw [← one_div]
  exact div_le_div_of_nonneg_left zero_le_one (Real.log_pos hnReal)
    ((Real.log_le_self (by positivity)).trans hpow)

theorem div_log_eventually_le (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, c / Real.log n ≤ ε := by
  have hLog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (hLog.const_div_atTop c).eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact ⟨N, fun n hn => (hN n hn).le⟩

#print axioms failure_of_intersection_le
#print axioms inverse_pow_le_inv_log
#print axioms div_log_eventually_le

end
end Mathproof.EvenTI.GlobalCoverage
