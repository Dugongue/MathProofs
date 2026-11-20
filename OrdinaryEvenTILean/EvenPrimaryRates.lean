import EvenPrimaryEnvelope
import PrimaryTailRates
import PrimaryTailTrace

open scoped BigOperators Polynomial Classical

namespace EvenTI.Primary

open Polynomial Matrix Mathproof.Problem17PrimaryTail Mathproof.Problem17RepeatedBudget

noncomputable section

variable {K : Type*} [Field K] [Fintype K]

def fieldSize (K : Type*) [Fintype K] : ℝ := Fintype.card K

theorem fieldSize_two_le : 2 ≤ fieldSize K := by
  unfold fieldSize
  exact_mod_cast (Fintype.one_lt_card (α := K))

theorem event_matrix_threshold_le (p : K[X]) (hp : p.Monic) (hi : Irreducible p) (n k : ℕ) :
    event (fun A : SquareMatrix K n => p^(2*(k+1)) ∣ A.charpoly) ≤
      (4 * fieldSize K ^ 2) * ((fieldSize K)⁻¹)^(2*p.natDegree) * (2/3:ℝ)^k := by
  let q := fieldSize K
  let Q := q ^ p.natDegree
  have hq : 2 ≤ q := fieldSize_two_le
  have hq0 : 0 < q := by linarith
  rw [event_eq_card]
  by_cases hd : p.natDegree = 1
  · have h := matrix_even_power_event_probability_le p hp hi (k+1) n
    refine h.trans ?_
    change _ ≤ (4*q^2)*(q⁻¹)^(2*p.natDegree)*(2/3:ℝ)^k
    rw [hd]
    have hc : (4*q^2)*(q⁻¹)^(2*1) = 4 := by
      norm_num
      field_simp
    rw [hc, pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2/3) k]
  · have hp2 : 2 ≤ p.natDegree := by
      have := hi.natDegree_pos
      omega
    have hQ : 4 ≤ Q := by
      calc
        (4:ℝ) ≤ q^2 := by nlinarith
        _ ≤ Q := pow_le_pow_right₀ (by linarith) hp2
    have hQ0 : 0 < Q := by linarith
    have hQ1 : 0 < Q-1 := by linarith
    have hsmall : (Q-1)⁻¹ ≤ 2*Q⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv]
      exact (div_le_div_iff₀ hQ1 hQ0).mpr (by linarith)
    have hloss : ((Q-1)⁻¹)^2 ≤ 2/3 := by
      have hh : (Q-1)⁻¹ ≤ 1/2 := by
        rw [← one_div]
        exact (div_le_div_iff₀ hQ1 (by norm_num)).mpr (by linarith)
      calc
        _ ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ (by positivity) hh _
        _ ≤ _ := by norm_num
    have hfirst : ((Q-1)⁻¹)^2 ≤ 4*(q⁻¹)^(2*p.natDegree) := by
      calc
        _ ≤ (2*Q⁻¹)^2 := pow_le_pow_left₀ (by positivity) hsmall _
        _ = _ := by
          rw [Nat.mul_comm 2 p.natDegree, pow_mul]
          simp only [Q, inv_pow]
          ring
    have hm := matrix_power_event_probability_le p hp hi (2*(k+1)) n
    rw [Nat.card_eq_fintype_card (α := K)] at hm
    refine hm.trans ?_
    change (((Q-1)^(2*(k+1)))⁻¹) ≤ (4*q^2)*(q⁻¹)^(2*p.natDegree)*(2/3:ℝ)^k
    rw [← inv_pow, pow_mul, pow_succ' _ k]
    calc
      _ ≤ (4*(q⁻¹)^(2*p.natDegree))*(2/3:ℝ)^k := by
        exact mul_le_mul hfirst (pow_le_pow_left₀ (by positivity) hloss _) (by positivity) (by positivity)
      _ ≤ _ := by
        have hlarge : (4:ℝ) ≤ 4*q^2 := by nlinarith
        gcongr

theorem event_trace_le (n : ℕ) (hn : 0 < n) (a : K) (P : SquareMatrix K n → Prop) :
    event (fun A : {A : SquareMatrix K n // A.trace = a} => P A.val) ≤
      fieldSize K * event P := by
  rw [event_eq_card, event_eq_card]
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let e : {A : {A : SquareMatrix K n // A.trace = a} // P A.val} ≃
      {A : SquareMatrix K n // A.trace = a ∧ P A} :=
    { toFun := fun A => ⟨A.val.val, A.val.property, A.property⟩
      invFun := fun A => ⟨⟨A.val,A.property.1⟩,A.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simpa only [fieldSize, Nat.card_eq_fintype_card (α := K)] using trace_condition_amplification a P

theorem event_trace_threshold_le (p : K[X]) (hp : p.Monic) (hi : Irreducible p)
    (n k : ℕ) (hn : 0 < n) (a : K) :
    event (fun A : {A : SquareMatrix K n // A.trace = a} => p^(2*(k+1)) ∣ A.val.charpoly) ≤
      (4 * fieldSize K ^ 3) * ((fieldSize K)⁻¹)^(2*p.natDegree) * (2/3:ℝ)^k := by
  have hq : 0 ≤ fieldSize K := by linarith [fieldSize_two_le (K := K)]
  refine (event_trace_le n hn a (fun A : SquareMatrix K n => p^(2*(k+1)) ∣ A.charpoly)).trans ?_
  calc
    _ ≤ fieldSize K * ((4 * fieldSize K ^ 2) * ((fieldSize K)⁻¹)^(2*p.natDegree) * (2/3:ℝ)^k) :=
      mul_le_mul_of_nonneg_left (event_matrix_threshold_le p hp hi n k) hq
    _ = _ := by ring

#print axioms event_matrix_threshold_le
#print axioms event_trace_threshold_le

end
end EvenTI.Primary
