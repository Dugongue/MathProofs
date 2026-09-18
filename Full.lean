import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.CardEmbedding
set_option maxHeartbeats 1600000

def TStarCoeff (m n k : Nat) : Nat :=
  if m = 1 ∨ (m = 2 ∧ n = 2) then (m*n).choose k
  else if k = 0 then 1
  else if k = 1 then m*n
  else if k = 2 then (m*n).choose 2
  else if m = 2 then 2 * n.choose k
  else m * n.choose k + n * m.choose k +
    k.factorial * m.choose k * n.choose k +
    m.choose 2 * n.choose 2 * (4 : Nat).choose k

def TStarUnimodal (m n : Nat) : Prop :=
  ∃ p : Nat, (∀ k, k < p → TStarCoeff m n k ≤ TStarCoeff m n (k+1)) ∧
    (∀ k, p ≤ k → TStarCoeff m n (k+1) ≤ TStarCoeff m n k)

def TStarBad (m n : Nat) : Prop :=
  (m = 2 ∧ n = 8) ∨ (m = 3 ∧ 11 ≤ n ∧ n ≤ 17) ∨
    (4 ≤ m ∧ 2*m+4 ≤ n ∧ n ≤ m+(m+1)*(1+(m-1).factorial))

-- The fixed universal target is in plan.json; no placeholder proof is asserted here.


namespace TStarFormal

def Peak (f : ℕ → ℕ) : Prop :=
  ∃ p, (∀ k, k < p → f k ≤ f (k+1)) ∧ (∀ k, p ≤ k → f (k+1) ≤ f k)

theorem peak_iff_no_valley (f : ℕ → ℕ) (N : ℕ)
    (hzero : ∀ k, N ≤ k → f k = 0) :
    Peak f ↔ ∀ i j, i < j → f (i+1) < f i → f (j+1) ≤ f j := by
  constructor
  · rintro ⟨p, hup, hdown⟩ i j hij hi
    have hp : p ≤ i := by
      by_contra h
      have := hup i (by omega)
      omega
    exact hdown j (by omega)
  · intro h
    by_cases hex : ∃ k, f (k+1) < f k
    · refine ⟨Nat.find hex, ?_, ?_⟩
      · intro k hk
        have := Nat.find_min hex hk
        omega
      · intro k hk
        by_cases he : k = Nat.find hex
        · subst k
          exact le_of_lt (Nat.find_spec hex)
        · exact h (Nat.find hex) k (by omega) (Nat.find_spec hex)
    · refine ⟨N, ?_, ?_⟩
      · intro k hk
        by_contra hn
        exact hex ⟨k, by omega⟩
      · intro k hk
        rw [hzero k hk, hzero (k+1) (by omega)]

theorem valley_not_peak (f : ℕ → ℕ) (k : ℕ)
    (hleft : f (k+1) < f k) (hright : f (k+1) < f (k+2)) : ¬ Peak f := by
  rintro ⟨p, hu, hd⟩
  by_cases h : k < p
  · have := hu k h
    omega
  · have ht := hd (k+1) (by omega)
    have he : k+1+1 = k+2 := by omega
    rw [he] at ht
    omega

theorem choose_step_up (n k : ℕ) (h : 2*k+1 ≤ n) :
    n.choose k ≤ n.choose (k+1) := by
  have he := Nat.choose_succ_right_eq n k
  have hs : k+1 ≤ n-k := by omega
  have hm := Nat.mul_le_mul_left (n.choose k) hs
  nlinarith

theorem choose_step_down (n k : ℕ) (h : n ≤ 2*k+1) :
    n.choose (k+1) ≤ n.choose k := by
  have he := Nat.choose_succ_right_eq n k
  have hs : n-k ≤ k+1 := by omega
  have hm := Nat.mul_le_mul_left (n.choose k) hs
  nlinarith

theorem choose_step_strict (n k : ℕ) (h : 2*k+2 ≤ n) :
    n.choose k < n.choose (k+1) := by
  have he := Nat.choose_succ_right_eq n k
  have hp := Nat.choose_pos (show k ≤ n by omega)
  have hs : k+2 ≤ n-k := by omega
  have hm := Nat.mul_le_mul_left (n.choose k) hs
  nlinarith

theorem binomial_peak (n a : ℕ) : Peak (fun k => a * n.choose k) := by
  refine ⟨n/2, ?_, ?_⟩
  · intro k hk
    exact Nat.mul_le_mul_left a (choose_step_up n k (by omega))
  · intro k hk
    exact Nat.mul_le_mul_left a (choose_step_down n k (by omega))

end TStarFormal


namespace TStarFormal

theorem choose_weight (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : n ≤ k * n.choose k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hp := Nat.choose_pos (show k ≤ n by omega)
  have he := Nat.add_one_mul_choose_eq n k
  nlinarith

theorem factorial_bound (k : ℕ) (hk : 5 ≤ k) : 2*k*(k+1) ≤ k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    have h := Nat.mul_le_mul_left (k+1) ih
    have hkk : k*k ≥ k+2 := by nlinarith
    nlinarith

theorem choose_real_2 (n : ℕ) : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ)-1) / 2 := by
  by_cases hn : 1 ≤ n
  · have he := Nat.choose_succ_right_eq n 1
    have hr : (n.choose 2 : ℝ) * 2 = (n.choose 1 : ℝ) * (n-1 : ℕ) := by exact_mod_cast he
    rw [Nat.cast_sub hn] at hr
    simp only [Nat.choose_one_right, Nat.cast_one] at hr
    norm_num at hr
    linear_combination hr / 2
  · interval_cases n <;> norm_num [Nat.choose]

theorem choose_real_3 (n : ℕ) : (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) / 6 := by
  by_cases hn : 2 ≤ n
  · have he := Nat.choose_succ_right_eq n 2
    have hr : (n.choose 3 : ℝ) * 3 = (n.choose 2 : ℝ) * (n-2 : ℕ) := by exact_mod_cast he
    rw [Nat.cast_sub hn] at hr
    rw [choose_real_2] at hr
    norm_num at hr
    linear_combination hr / 3
  · interval_cases n <;> norm_num [Nat.choose]

theorem choose_real_4 (n : ℕ) : (n.choose 4 : ℝ) = (n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) * ((n : ℝ)-3) / 24 := by
  by_cases hn : 3 ≤ n
  · have he := Nat.choose_succ_right_eq n 3
    have hr : (n.choose 4 : ℝ) * 4 = (n.choose 3 : ℝ) * (n-3 : ℕ) := by exact_mod_cast he
    rw [Nat.cast_sub hn] at hr
    rw [choose_real_3] at hr
    norm_num at hr
    linear_combination hr / 4
  · interval_cases n <;> norm_num [Nat.choose]

theorem choose_real_5 (n : ℕ) : (n.choose 5 : ℝ) = (n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) * ((n : ℝ)-3) * ((n : ℝ)-4) / 120 := by
  by_cases hn : 4 ≤ n
  · have he := Nat.choose_succ_right_eq n 4
    have hr : (n.choose 5 : ℝ) * 5 = (n.choose 4 : ℝ) * (n-4 : ℕ) := by exact_mod_cast he
    rw [Nat.cast_sub hn] at hr
    rw [choose_real_4] at hr
    norm_num at hr
    linear_combination hr / 5
  · interval_cases n <;> norm_num [Nat.choose]

end TStarFormal


-- These universal polynomial inequalities are partial certificates, not the classification theorem.
namespace TStarCertificates

theorem initial_3 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (u + 3)*(v + 3)*(-15*u - 15*v + (u + 3)^2*(v + 3)^2 - 3*(u + 3)^2*(v + 3) + 3*(u + 3)^2 - 3*(u + 3)*(v + 3)^2 + 12*(u + 3)*(v + 3) + 3*(v + 3)^2 - 73)/6 := by
  have h : (u + 3)*(v + 3)*(-15*u - 15*v + (u + 3)^2*(v + 3)^2 - 3*(u + 3)^2*(v + 3) + 3*(u + 3)^2 - 3*(u + 3)*(v + 3)^2 + 12*(u + 3)*(v + 3) + 3*(v + 3)^2 - 73)/6 = u^3*v^3/6 + u^3*v^2 + 2*u^3*v + 3*u^3/2 + u^2*v^3 + 13*u^2*v^2/2 + 14*u^2*v + 21*u^2/2 + 2*u*v^3 + 14*u*v^2 + 94*u*v/3 + 22*u + 3*v^3/2 + 21*v^2/2 + 22*v + 12 := by ring
  rw [h]
  positivity

theorem initial_4 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (u + 5)*(v + 6)*(-u - v + (u + 5)^3*(v + 6)^3 - 6*(u + 5)^3*(v + 6)^2 + 11*(u + 5)^3*(v + 6) - 5*(u + 5)^3 - 6*(u + 5)^2*(v + 6)^3 + 32*(u + 5)^2*(v + 6)^2 - 54*(u + 5)^2*(v + 6) + 18*(u + 5)^2 + 11*(u + 5)*(v + 6)^3 - 54*(u + 5)*(v + 6)^2 + 67*(u + 5)*(v + 6) - 5*(v + 6)^3 + 18*(v + 6)^2 - 37)/24 := by
  have h : (u + 5)*(v + 6)*(-u - v + (u + 5)^3*(v + 6)^3 - 6*(u + 5)^3*(v + 6)^2 + 11*(u + 5)^3*(v + 6) - 5*(u + 5)^3 - 6*(u + 5)^2*(v + 6)^3 + 32*(u + 5)^2*(v + 6)^2 - 54*(u + 5)^2*(v + 6) + 18*(u + 5)^2 + 11*(u + 5)*(v + 6)^3 - 54*(u + 5)*(v + 6)^2 + 67*(u + 5)*(v + 6) - 5*(v + 6)^3 + 18*(v + 6)^2 - 37)/24 = u^4*v^4/24 + 3*u^4*v^3/4 + 119*u^4*v^2/24 + 343*u^4*v/24 + 61*u^4/4 + 7*u^3*v^4/12 + 31*u^3*v^3/3 + 803*u^3*v^2/12 + 2251*u^3*v/12 + 385*u^3/2 + 71*u^2*v^4/24 + 205*u^2*v^3/4 + 7711*u^2*v^2/24 + 20555*u^2*v/24 + 3233*u^2/4 + 155*u*v^4/24 + 433*u*v^3/4 + 15403*u*v^2/24 + 18493*u*v/12 + 1154*u + 125*v^4/24 + 995*v^3/12 + 10615*v^2/24 + 9715*v/12 + 95 := by ring
  rw [h]
  positivity

theorem dominance_4 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (u + 5)*(v + 6)*(-91*u - 91*v + (u + 5)^3*(v + 6)^3 - 6*(u + 5)^3*(v + 6)^2 + 11*(u + 5)^3*(v + 6) - 11*(u + 5)^3 - 6*(u + 5)^2*(v + 6)^3 + 36*(u + 5)^2*(v + 6)^2 - 66*(u + 5)^2*(v + 6) + 66*(u + 5)^2 + 11*(u + 5)*(v + 6)^3 - 66*(u + 5)*(v + 6)^2 + 91*(u + 5)*(v + 6) - 11*(v + 6)^3 + 66*(v + 6)^2 - 935)/120 := by
  have h : (u + 5)*(v + 6)*(-91*u - 91*v + (u + 5)^3*(v + 6)^3 - 6*(u + 5)^3*(v + 6)^2 + 11*(u + 5)^3*(v + 6) - 11*(u + 5)^3 - 6*(u + 5)^2*(v + 6)^3 + 36*(u + 5)^2*(v + 6)^2 - 66*(u + 5)^2*(v + 6) + 66*(u + 5)^2 + 11*(u + 5)*(v + 6)^3 - 66*(u + 5)*(v + 6)^2 + 91*(u + 5)*(v + 6) - 11*(v + 6)^3 + 66*(v + 6)^2 - 935)/120 = u^4*v^4/120 + 3*u^4*v^3/20 + 119*u^4*v^2/120 + 337*u^4*v/120 + 11*u^4/4 + 7*u^3*v^4/60 + 21*u^3*v^3/10 + 833*u^3*v^2/60 + 2359*u^3*v/60 + 77*u^3/2 + 71*u^2*v^4/120 + 213*u^2*v^3/20 + 8419*u^2*v^2/120 + 23597*u^2*v/120 + 751*u^2/4 + 149*u*v^4/120 + 447*u*v^3/20 + 17461*u*v^2/120 + 23609*u*v/60 + 341*u + 19*v^4/24 + 57*v^3/4 + 2141*v^2/24 + 843*v/4 + 105 := by ring
  rw [h]
  positivity

theorem m4_prefix (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (v + 9)*(107*v + 7*(v + 9)^3 - 70*(v + 9)^2 + 901)/6 := by
  have h : (v + 9)*(107*v + 7*(v + 9)^3 - 70*(v + 9)^2 + 901)/6 = 7*v^4/6 + 91*v^3/3 + 1619*v^2/6 + 2633*v/3 + 501 := by ring
  rw [h]
  positivity

theorem m4_transition (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (v + 40)*(-525*v + (v + 40)^4 - 45*(v + 40)^3 + 245*(v + 40)^2 - 20706)/30 := by
  have h : (v + 40)*(-525*v + (v + 40)^4 - 45*(v + 40)^3 + 245*(v + 40)^2 - 20706)/30 = v^5/30 + 31*v^4/6 + 603*v^3/2 + 47375*v^2/6 + 1207147*v/15 + 68392 := by ring
  rw [h]
  positivity

theorem m3_prefix (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (v + 18)*(11*v + (v + 18)^3 - 18*(v + 18)^2 + 196)/8 := by
  have h : (v + 18)*(11*v + (v + 18)^3 - 18*(v + 18)^2 + 196)/8 = v^4/8 + 27*v^3/4 + 983*v^2/8 + 3113*v/4 + 441 := by ring
  rw [h]
  positivity

theorem m3_transition (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (v + 17)*(v + 18)*(51*v + (v + 18)^3 - 14*(v + 18)^2 + 804)/40 := by
  have h : (v + 17)*(v + 18)*(51*v + (v + 18)^3 - 14*(v + 18)^2 + 804)/40 = v^5/40 + 15*v^4/8 + 445*v^3/8 + 6501*v^2/8 + 116157*v/20 + 16065 := by ring
  rw [h]
  positivity

end TStarCertificates

namespace TStarFormal

theorem coeff_zero (m n : ℕ) : TStarCoeff m n 0 = 1 := by
  unfold TStarCoeff
  split_ifs <;> simp_all

theorem coeff_one (m n : ℕ) : TStarCoeff m n 1 = m*n := by
  unfold TStarCoeff
  split_ifs <;> simp_all

theorem coeff_two (m n : ℕ) : TStarCoeff m n 2 = (m*n).choose 2 := by
  unfold TStarCoeff
  split_ifs <;> simp_all

theorem coeff_large (m n k : ℕ) (hm : 3 ≤ m) (hk : 3 ≤ k) :
    TStarCoeff m n k = m * n.choose k + n * m.choose k +
      k.factorial * m.choose k * n.choose k + m.choose 2 * n.choose 2 * (4 : Nat).choose k := by
  simp only [TStarCoeff]
  split_ifs <;> omega

theorem coeff_tail (m n k : ℕ) (hm : 3 ≤ m) (hk : 5 ≤ k) (hmk : m < k) :
    TStarCoeff m n k = m * n.choose k := by
  rw [coeff_large m n k hm (by omega), Nat.choose_eq_zero_of_lt hmk,
    Nat.choose_eq_zero_of_lt (show 4 < k by omega)]
  simp

theorem coeff_support (m n k : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hk : m*n+5 ≤ k) : TStarCoeff m n k = 0 := by
  have hn : n < k := by nlinarith
  have hm' : m < k := by omega
  have hmn' : m*n < k := by omega
  unfold TStarCoeff
  split_ifs <;> simp_all [Nat.choose_eq_zero_of_lt hn, Nat.choose_eq_zero_of_lt hm',
    Nat.choose_eq_zero_of_lt hmn', Nat.choose_eq_zero_of_lt (show 4 < k by omega)] <;> omega

end TStarFormal

namespace TStarFormal

def Matching (m n k : ℕ) := k.factorial * m.choose k * n.choose k

theorem matching_recurrence (m n k : ℕ) :
    Matching m n (k+1) * (k+1) = Matching m n k * (m-k) * (n-k) := by
  unfold Matching
  rw [Nat.factorial_succ]
  calc
    (k+1) * k.factorial * m.choose (k+1) * n.choose (k+1) * (k+1) =
      k.factorial * (m.choose (k+1) * (k+1)) * (n.choose (k+1) * (k+1)) := by ring
    _ = _ := by rw [Nat.choose_succ_right_eq, Nat.choose_succ_right_eq]; ring

theorem matching_dominance (m n k : ℕ) (hk : 5 ≤ k) (hkm : k ≤ m) (hkn : k ≤ n) :
    (k+1) * (m*n.choose k + n*m.choose k) ≤ Matching m n k := by
  have h1 := Nat.mul_le_mul_right (n.choose k) (choose_weight m k (by omega) hkm)
  have h2 := Nat.mul_le_mul_right (m.choose k) (choose_weight n k (by omega) hkn)
  have h3 := Nat.mul_le_mul_right (m.choose k * n.choose k) (factorial_bound k hk)
  have h4 := Nat.mul_le_mul_left (k+1) (Nat.add_le_add h1 h2)
  unfold Matching
  nlinarith

theorem coeff_step_up_high (m n k : ℕ) (hm : 3 ≤ m) (hk : 5 ≤ k)
    (hkm : k < m) (hmn : m ≤ n) (hd : k+2 ≤ (m-k)*(n-k)) :
    TStarCoeff m n k ≤ TStarCoeff m n (k+1) := by
  have hdom := matching_dominance m n k hk (by omega) (by omega)
  have hrec := matching_recurrence m n k
  have hmul := Nat.mul_le_mul_left (Matching m n k) hd
  have hx : m*n.choose k + n*m.choose k + Matching m n k ≤ Matching m n (k+1) := by
    nlinarith
  rw [coeff_large m n k hm (by omega), coeff_large m n (k+1) hm (by omega)]
  rw [Nat.choose_eq_zero_of_lt (show 4 < k by omega), Nat.choose_eq_zero_of_lt (show 4 < k+1 by omega)]
  unfold Matching at hx
  nlinarith

theorem coeff_step_down_high (m n k : ℕ) (hm : 3 ≤ m) (hk : 4 ≤ k)
    (hkm : k < m) (hmn : m ≤ n) (hd : (m-k)*(n-k) ≤ k+1) :
    TStarCoeff m n (k+1) ≤ TStarCoeff m n k := by
  have hmk : 1 ≤ m-k := by omega
  have hnk : n-k ≤ k+1 := by nlinarith
  have hmk' : m-k ≤ k+1 := by omega
  have hu := choose_step_down n k (by omega)
  have hv := choose_step_down m k (by omega)
  have hrec := matching_recurrence m n k
  have hmul := Nat.mul_le_mul_left (Matching m n k) hd
  have hx : Matching m n (k+1) ≤ Matching m n k := by nlinarith
  have hu' := Nat.mul_le_mul_left m hu
  have hv' := Nat.mul_le_mul_left n hv
  rw [coeff_large m n k hm (by omega), coeff_large m n (k+1) hm (by omega)]
  rw [Nat.choose_eq_zero_of_lt (show 4 < k+1 by omega)]
  unfold Matching at hx
  simp only [mul_zero, add_zero]
  omega

end TStarFormal

namespace TStarFormal

theorem coeff_real_3 (m n : ℕ) (hm : 3 ≤ m) :
    (TStarCoeff m n 3 : ℝ) = m * ((n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) / 6) + n * ((m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) / 6) + 6 * ((m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) / 6) * ((n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) / 6) + ((m : ℝ) * ((m : ℝ)-1) / 2) * ((n : ℝ) * ((n : ℝ)-1) / 2) * 4 := by
  rw [coeff_large m n 3 hm (by omega)]
  push_cast
  rw [choose_real_3, choose_real_3, choose_real_2, choose_real_2]
  norm_num [Nat.factorial, Nat.choose]

theorem coeff_real_4 (m n : ℕ) (hm : 3 ≤ m) :
    (TStarCoeff m n 4 : ℝ) = m * ((n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) * ((n : ℝ)-3) / 24) + n * ((m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) * ((m : ℝ)-3) / 24) + 24 * ((m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) * ((m : ℝ)-3) / 24) * ((n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) * ((n : ℝ)-3) / 24) + ((m : ℝ) * ((m : ℝ)-1) / 2) * ((n : ℝ) * ((n : ℝ)-1) / 2) * 1 := by
  rw [coeff_large m n 4 hm (by omega)]
  push_cast
  rw [choose_real_4, choose_real_4, choose_real_2, choose_real_2]
  norm_num [Nat.factorial, Nat.choose]

theorem coeff_real_5 (m n : ℕ) (hm : 3 ≤ m) :
    (TStarCoeff m n 5 : ℝ) = m * ((n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) * ((n : ℝ)-3) * ((n : ℝ)-4) / 120) + n * ((m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) * ((m : ℝ)-3) * ((m : ℝ)-4) / 120) + 120 * ((m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) * ((m : ℝ)-3) * ((m : ℝ)-4) / 120) * ((n : ℝ) * ((n : ℝ)-1) * ((n : ℝ)-2) * ((n : ℝ)-3) * ((n : ℝ)-4) / 120) + ((m : ℝ) * ((m : ℝ)-1) / 2) * ((n : ℝ) * ((n : ℝ)-1) / 2) * 0 := by
  rw [coeff_large m n 5 hm (by omega)]
  push_cast
  rw [choose_real_5, choose_real_5, choose_real_2, choose_real_2]
  norm_num [Nat.factorial, Nat.choose]

theorem coeff_initial_3 (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) :
    TStarCoeff m n 2 ≤ TStarCoeff m n 3 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h := TStarCertificates.initial_3 ((m : ℝ)-3) ((n : ℝ)-3)
    (by linarith) (by linarith)
  have h3 := coeff_real_3 m n hm
  have h2 : (TStarCoeff m n 2 : ℝ) = (m*n : ℝ)*(m*n-1)/2 := by
    rw [coeff_two, choose_real_2]
    push_cast
    rfl
  have hh : (TStarCoeff m n 2 : ℝ) ≤ (TStarCoeff m n 3 : ℝ) := by nlinarith [h]
  exact_mod_cast hh

theorem coeff_initial_4 (m n : ℕ) (hm : 5 ≤ m) (hn : 6 ≤ n) :
    TStarCoeff m n 3 ≤ TStarCoeff m n 4 := by
  have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have h := TStarCertificates.initial_4 ((m : ℝ)-5) ((n : ℝ)-6) (by linarith) (by linarith)
  have h3 := coeff_real_3 m n (by omega)
  have h4 := coeff_real_4 m n (by omega)
  have hh : (TStarCoeff m n 3 : ℝ) ≤ (TStarCoeff m n 4 : ℝ) := by nlinarith [h]
  exact_mod_cast hh

end TStarFormal

namespace TStarFormal

theorem dominance_four (m n : ℕ) (hm : 5 ≤ m) (hn : 6 ≤ n) :
    5 * (m*n.choose 4 + n*m.choose 4 + m.choose 2*n.choose 2) ≤ Matching m n 4 := by
  have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have h := TStarCertificates.dominance_4 ((m : ℝ)-5) ((n : ℝ)-6) (by linarith) (by linarith)
  have hr : (5 : ℝ) * ((m*n.choose 4 : ℕ) + (n*m.choose 4 : ℕ) + (m.choose 2*n.choose 2 : ℕ)) ≤ (Matching m n 4 : ℝ) := by
    unfold Matching
    push_cast
    rw [choose_real_4, choose_real_4, choose_real_2, choose_real_2]
    norm_num [Nat.factorial]
    nlinarith [h]
  exact_mod_cast hr

theorem coeff_step_up_four (m n : ℕ) (hm : 5 ≤ m) (hn : 6 ≤ n)
    (hd : 6 ≤ (m-4)*(n-4)) : TStarCoeff m n 4 ≤ TStarCoeff m n 5 := by
  have hdom := dominance_four m n hm hn
  have hrec := matching_recurrence m n 4
  have hmul := Nat.mul_le_mul_left (Matching m n 4) hd
  have hx : m*n.choose 4 + n*m.choose 4 + m.choose 2*n.choose 2 + Matching m n 4 ≤ Matching m n 5 := by
    nlinarith
  rw [coeff_large m n 4 (by omega) (by omega), coeff_large m n 5 (by omega) (by omega)]
  norm_num [Nat.choose]
  norm_num [Matching, Nat.factorial] at hx
  omega

theorem coeff_initial (m n k : ℕ) (hm : 5 ≤ m) (hn : 6 ≤ n) (hk : k < 4) :
    TStarCoeff m n k ≤ TStarCoeff m n (k+1) := by
  interval_cases k
  · rw [coeff_zero, coeff_one]
    nlinarith
  · rw [coeff_one, coeff_two]
    have he := choose_real_2 (m*n)
    have hs : (3 : ℝ) ≤ (m*n : ℕ) := by exact_mod_cast (show 3 ≤ m*n by nlinarith)
    have hh : (m*n : ℕ) ≤ ((m*n).choose 2 : ℝ) := by nlinarith [he]
    exact_mod_cast hh
  · exact coeff_initial_3 m n (by omega) (by omega)
  · exact coeff_initial_4 m n hm hn

theorem phase_decreasing (m n i j : ℕ) (hij : i < j) :
    (m-j)*(n-j) ≤ (m-i)*(n-i) := by
  exact Nat.mul_le_mul (by omega) (by omega)

theorem coeff_prefix_no_valley (m n i j : ℕ) (hm : 5 ≤ m) (hn : 6 ≤ n)
    (hmn : m ≤ n) (hij : i < j) (hjm : j < m)
    (hi : TStarCoeff m n (i+1) < TStarCoeff m n i) :
    TStarCoeff m n (j+1) ≤ TStarCoeff m n j := by
  have hi4 : 4 ≤ i := by
    by_contra h
    have := coeff_initial m n i hm hn (by omega)
    omega
  have hd : (m-i)*(n-i) ≤ i+1 := by
    by_contra h
    have hiup : TStarCoeff m n i ≤ TStarCoeff m n (i+1) := by
      by_cases hi5 : 5 ≤ i
      · exact coeff_step_up_high m n i (by omega) hi5 (by omega) hmn (by omega)
      · have he : i=4 := by omega
        subst i
        exact coeff_step_up_four m n hm hn (by omega)
    omega
  have hp := phase_decreasing m n i j hij
  exact coeff_step_down_high m n j (by omega) (by omega) hjm hmn (by omega)

theorem coeff_prefix_up (m n k : ℕ) (hm : 5 ≤ m) (hn : 2*m ≤ n) (hk : k < m) :
    TStarCoeff m n k ≤ TStarCoeff m n (k+1) := by
  have hn6 : 6 ≤ n := by omega
  by_cases hk4 : k < 4
  · exact coeff_initial m n k hm hn6 hk4
  have hd : k+2 ≤ (m-k)*(n-k) := by
    have ha : 1 ≤ m-k := by omega
    have hb : k+2 ≤ n-k := by omega
    nlinarith
  by_cases hk5 : 5 ≤ k
  · exact coeff_step_up_high m n k (by omega) hk5 hk (by omega) hd
  · have he : k=4 := by omega
    subst k
    exact coeff_step_up_four m n hm hn6 hd

end TStarFormal

namespace TStarFormal

def Threshold (m : ℕ) := m+(m+1)*(1+(m-1).factorial)

theorem threshold_large (m : ℕ) (hm : 5 ≤ m) : 2*m+3 ≤ Threshold m := by
  have h := Nat.factorial_le (show 2 ≤ m-1 by omega)
  norm_num at h
  unfold Threshold
  nlinarith

theorem coeff_at_cut (m n : ℕ) (hm : 5 ≤ m) :
    TStarCoeff m n m = (m+m.factorial)*n.choose m+n := by
  rw [coeff_large m n m (by omega) (by omega), Nat.choose_self,
    Nat.choose_eq_zero_of_lt (show 4 < m by omega)]
  ring

theorem transition_balance (m n : ℕ) (hm : 5 ≤ m) (hmn : m ≤ n) :
    (m+1)*TStarCoeff m n (m+1) + m*n.choose m*Threshold m + (m+1)*n =
      m*n.choose m*n + (m+1)*TStarCoeff m n m := by
  rw [coeff_at_cut m n hm, coeff_tail m n (m+1) (by omega) (by omega) (by omega)]
  have hc := Nat.choose_succ_right_eq n m
  have hf : m.factorial = m*(m-1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m by omega)]
    rw [Nat.factorial_succ]
    congr 1
    omega
  have hs : m*n.choose m*(n-m)+m*n.choose m*m = m*n.choose m*n := by
    rw [← mul_add, Nat.sub_add_cancel hmn]
  unfold Threshold
  rw [hf]
  nlinarith

theorem transition_down (m n : ℕ) (hm : 5 ≤ m) (hmn : m ≤ n) (hn : n ≤ Threshold m) :
    TStarCoeff m n (m+1) < TStarCoeff m n m := by
  have h := transition_balance m n hm hmn
  have hx := Nat.mul_le_mul_left (m*n.choose m) hn
  have hnpos : 0 < n := by omega
  have hp : 0 < (m+1)*n := by positivity
  nlinarith

theorem choose_at_cut_large (m n : ℕ) (hm : 5 ≤ m) (hn : m+3 ≤ n) :
    (m+1)*n ≤ m*n.choose m := by
  have hchoose := Nat.choose_le_choose (m-1) (show m+1 ≤ n-1 by omega)
  have hsym : (m+1).choose (m-1) = (m+1).choose 2 := by
    have h := Nat.choose_symm (show m-1 ≤ m+1 by omega)
    have he : m+1-(m-1)=2 := by omega
    simpa only [he] using h.symm
  rw [hsym] at hchoose
  have hsmall : m+1 ≤ (m+1).choose 2 := by
    have hc := choose_real_2 (m+1)
    have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at hc
    have h : (m+1 : ℕ) ≤ ((m+1).choose 2 : ℝ) := by push_cast; nlinarith [hc]
    exact_mod_cast h
  have he := Nat.add_one_mul_choose_eq (n-1) (m-1)
  rw [Nat.sub_add_cancel (show 1 ≤ n by omega), Nat.sub_add_cancel (show 1 ≤ m by omega)] at he
  have hmul := Nat.mul_le_mul_left n (le_trans hsmall hchoose)
  nlinarith

theorem transition_up (m n : ℕ) (hm : 5 ≤ m) (hn : Threshold m < n) :
    TStarCoeff m n m ≤ TStarCoeff m n (m+1) := by
  have ht := threshold_large m hm
  have hmn : m ≤ n := by omega
  have h := transition_balance m n hm hmn
  have hc := choose_at_cut_large m n hm (by omega)
  have hx := Nat.mul_le_mul_left (m*n.choose m) (show Threshold m+1 ≤ n by omega)
  nlinarith

end TStarFormal

namespace TStarFormal

theorem tail_no_valley (m n i j : ℕ) (hm : 3 ≤ m) (hi5 : 5 ≤ i)
    (hmi : m < i) (hij : i < j)
    (hi : TStarCoeff m n (i+1) < TStarCoeff m n i) :
    TStarCoeff m n (j+1) ≤ TStarCoeff m n j := by
  rw [coeff_tail m n i hm hi5 hmi, coeff_tail m n (i+1) hm (by omega) (by omega)] at hi
  rw [coeff_tail m n j hm (by omega) (by omega), coeff_tail m n (j+1) hm (by omega) (by omega)]
  have hn : n ≤ 2*i+1 := by
    by_contra h
    have hh := Nat.mul_le_mul_left m (choose_step_up n i (by omega))
    omega
  exact Nat.mul_le_mul_left m (choose_step_down n j (by omega))

theorem five_five_peak : Peak (TStarCoeff 5 5) := by
  refine ⟨3, ?_, ?_⟩
  · intro k hk
    interval_cases k <;> norm_num [TStarCoeff, Nat.choose, Nat.factorial]
  · intro k hk
    by_cases h : k ≤ 5
    · interval_cases k <;> norm_num [TStarCoeff, Nat.choose, Nat.factorial]
    · rw [coeff_tail 5 5 k (by omega) (by omega) (by omega),
        coeff_tail 5 5 (k+1) (by omega) (by omega) (by omega),
        Nat.choose_eq_zero_of_lt (show 5 < k by omega),
        Nat.choose_eq_zero_of_lt (show 5 < k+1 by omega)]

theorem classification_large (m n : ℕ) (hm : 5 ≤ m) (hmn : m ≤ n) :
    Peak (TStarCoeff m n) ↔ ¬ (2*m+4 ≤ n ∧ n ≤ Threshold m) := by
  constructor
  · intro hp hb
    have hd := transition_down m n hm hmn hb.2
    have hu : TStarCoeff m n (m+1) < TStarCoeff m n (m+2) := by
      rw [coeff_tail m n (m+1) (by omega) (by omega) (by omega),
        coeff_tail m n (m+2) (by omega) (by omega) (by omega)]
      have h := choose_step_strict n (m+1) (by omega)
      have hmpos : 0 < m := by omega
      convert Nat.mul_lt_mul_of_pos_left h hmpos using 1 <;> congr 2 <;> omega
    exact valley_not_peak (TStarCoeff m n) m hd hu hp
  · intro hbad
    by_cases he : m=5 ∧ n=5
    · rcases he with ⟨rfl,rfl⟩
      exact five_five_peak
    have hn6 : 6 ≤ n := by omega
    apply (peak_iff_no_valley (TStarCoeff m n) (m*n+5)
      (fun k hk => coeff_support m n k (by omega) hmn hk)).2
    intro i j hij hi
    by_cases hn : n ≤ 2*m+3
    · by_cases hjm : j < m
      · exact coeff_prefix_no_valley m n i j hm hn6 hmn hij hjm hi
      · by_cases hj : j=m
        · subst j
          exact le_of_lt (transition_down m n hm hmn (le_trans hn (threshold_large m hm)))
        · rw [coeff_tail m n j (by omega) (by omega) (by omega),
            coeff_tail m n (j+1) (by omega) (by omega) (by omega)]
          exact Nat.mul_le_mul_left m (choose_step_down n j (by omega))
    · have hR : Threshold m < n := by omega
      have him : m < i := by
        by_contra h
        by_cases hi' : i<m
        · have hh := coeff_prefix_up m n i hm (by omega) hi'
          omega
        · have hei : i=m := by omega
          subst i
          have hh := transition_up m n hm hR
          omega
      exact tail_no_valley m n i j (by omega) (by omega) him hij hi

end TStarFormal

namespace TStarFormal

theorem peak_join_binomial (f : ℕ → ℕ) (B n a : ℕ)
    (hup : ∀ k, k < B → f k ≤ f (k+1))
    (htail : ∀ k, B ≤ k → f k = a*n.choose k) : Peak f := by
  refine ⟨max B (n/2), ?_, ?_⟩
  · intro k hk
    by_cases hb : k < B
    · exact hup k hb
    · rw [htail k (by omega), htail (k+1) (by omega)]
      exact Nat.mul_le_mul_left a (choose_step_up n k (by omega))
  · intro k hk
    rw [htail k (by omega), htail (k+1) (by omega)]
    exact Nat.mul_le_mul_left a (choose_step_down n k (by omega))

theorem peak_finite (f : ℕ → ℕ) (B p : ℕ) (hp : p ≤ B)
    (hup : ∀ k : Fin B, k.val < p → f k.val ≤ f (k.val+1))
    (hdown : ∀ k : Fin B, p ≤ k.val → f (k.val+1) ≤ f k.val)
    (hzero : ∀ k, B ≤ k → f k = 0) : Peak f := by
  refine ⟨p, ?_, ?_⟩
  · intro k hk
    exact hup ⟨k, by omega⟩ hk
  · intro k hk
    by_cases hb : k < B
    · exact hdown ⟨k,hb⟩ hk
    · rw [hzero k (by omega), hzero (k+1) (by omega)]

theorem coeff_first_two (m n k : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) (hk : k < 2) :
    TStarCoeff m n k ≤ TStarCoeff m n (k+1) := by
  interval_cases k
  · rw [coeff_zero, coeff_one]
    nlinarith
  · rw [coeff_one, coeff_two]
    have he := choose_real_2 (m*n)
    have hs : (3 : ℝ) ≤ (m*n : ℕ) := by exact_mod_cast (show 3 ≤ m*n by nlinarith)
    have hh : (m*n : ℕ) ≤ ((m*n).choose 2 : ℝ) := by nlinarith [he]
    exact_mod_cast hh

theorem four_initial (n : ℕ) (hn : 9 ≤ n) : TStarCoeff 4 n 3 ≤ TStarCoeff 4 n 4 := by
  have hn' : (9 : ℝ) ≤ n := by exact_mod_cast hn
  have h := TStarCertificates.m4_prefix 0 ((n : ℝ)-9) (by norm_num) (by linarith)
  have h3 := coeff_real_3 4 n (by omega)
  have h4 := coeff_real_4 4 n (by omega)
  norm_num at h3 h4
  have hh : (TStarCoeff 4 n 3 : ℝ) ≤ (TStarCoeff 4 n 4 : ℝ) := by nlinarith [h]
  exact_mod_cast hh

theorem four_transition (n : ℕ) (hn : 40 ≤ n) : TStarCoeff 4 n 4 ≤ TStarCoeff 4 n 5 := by
  have hn' : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have h := TStarCertificates.m4_transition 0 ((n : ℝ)-40) (by norm_num) (by linarith)
  have h4 := coeff_real_4 4 n (by omega)
  have h5 := coeff_real_5 4 n (by omega)
  norm_num at h4 h5
  have hh : (TStarCoeff 4 n 4 : ℝ) ≤ (TStarCoeff 4 n 5 : ℝ) := by nlinarith [h]
  exact_mod_cast hh

theorem three_initial (n : ℕ) (hn : 18 ≤ n) : TStarCoeff 3 n 3 ≤ TStarCoeff 3 n 4 := by
  have hn' : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have h := TStarCertificates.m3_prefix 0 ((n : ℝ)-18) (by norm_num) (by linarith)
  have h3 := coeff_real_3 3 n (by omega)
  have h4 := coeff_real_4 3 n (by omega)
  norm_num at h3 h4
  have hh : (TStarCoeff 3 n 3 : ℝ) ≤ (TStarCoeff 3 n 4 : ℝ) := by nlinarith [h]
  exact_mod_cast hh

theorem three_transition (n : ℕ) (hn : 18 ≤ n) : TStarCoeff 3 n 4 ≤ TStarCoeff 3 n 5 := by
  have hn' : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have h := TStarCertificates.m3_transition 0 ((n : ℝ)-18) (by norm_num) (by linarith)
  have h4 := coeff_real_4 3 n (by omega)
  have h5 := coeff_real_5 3 n (by omega)
  norm_num at h4 h5
  have hh : (TStarCoeff 3 n 4 : ℝ) ≤ (TStarCoeff 3 n 5 : ℝ) := by nlinarith [h]
  exact_mod_cast hh

theorem four_peak_large (n : ℕ) (hn : 40 ≤ n) : Peak (TStarCoeff 4 n) := by
  apply peak_join_binomial (TStarCoeff 4 n) 5 n 4
  · intro k hk
    by_cases hk2 : k < 2
    · exact coeff_first_two 4 n k (by omega) (by omega) hk2
    interval_cases k
    · exact coeff_initial_3 4 n (by omega) (by omega)
    · exact four_initial n (by omega)
    · exact four_transition n hn
  · intro k hk
    exact coeff_tail 4 n k (by omega) hk (by omega)

theorem three_peak_large (n : ℕ) (hn : 18 ≤ n) : Peak (TStarCoeff 3 n) := by
  apply peak_join_binomial (TStarCoeff 3 n) 5 n 3
  · intro k hk
    by_cases hk2 : k < 2
    · exact coeff_first_two 3 n k (by omega) (by omega) hk2
    interval_cases k
    · exact coeff_initial_3 3 n (by omega) (by omega)
    · exact three_initial n hn
    · exact three_transition n hn
  · intro k hk
    exact coeff_tail 3 n k (by omega) hk (by omega)

end TStarFormal

namespace TStarFormal

theorem two_tail (n k : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    TStarCoeff 2 n k = 2*n.choose k := by
  simp only [TStarCoeff]
  split_ifs <;> omega

theorem two_transition (n : ℕ) (hn : 9 ≤ n) : TStarCoeff 2 n 2 ≤ TStarCoeff 2 n 3 := by
  have hn' : (9 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (TStarCoeff 2 n 3 : ℝ) = 2*((n : ℝ)*(n-1)*(n-2)/6) := by
    rw [two_tail n 3 (by omega) (by omega)]
    push_cast
    rw [choose_real_3]
  have h2 : (TStarCoeff 2 n 2 : ℝ) = (2*n : ℝ)*(2*n-1)/2 := by
    rw [coeff_two, choose_real_2]
    push_cast
    rfl
  have hpos : 0 ≤ (n : ℝ)*(n-9) := mul_nonneg (by positivity) (by linarith)
  have hpos' : 0 ≤ (n : ℝ)*(n^2-9*n+5) := mul_nonneg (by positivity) (by nlinarith)
  have h : (TStarCoeff 2 n 2 : ℝ) ≤ (TStarCoeff 2 n 3 : ℝ) := by nlinarith [hpos']
  exact_mod_cast h

theorem two_peak_large (n : ℕ) (hn : 9 ≤ n) : Peak (TStarCoeff 2 n) := by
  apply peak_join_binomial (TStarCoeff 2 n) 3 n 2
  · intro k hk
    interval_cases k
    · rw [coeff_zero, coeff_one]; omega
    · rw [coeff_one, coeff_two]
      have he := choose_real_2 (2*n)
      have hn' : (9 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at he
      have h : (2*n : ℕ) ≤ ((2*n).choose 2 : ℝ) := by push_cast; nlinarith [he]
      exact_mod_cast h
    · exact two_transition n hn
  · intro k hk
    exact two_tail n k (by omega) hk

theorem one_peak (n : ℕ) : Peak (TStarCoeff 1 n) := by
  have he : TStarCoeff 1 n = fun k => 1*n.choose k := by funext k; simp [TStarCoeff]
  rw [he]
  exact binomial_peak n 1

theorem two_two_peak : Peak (TStarCoeff 2 2) := by
  have he : TStarCoeff 2 2 = fun k => 1*(4 : ℕ).choose k := by funext k; simp [TStarCoeff]
  rw [he]
  exact binomial_peak 4 1

end TStarFormal

namespace TStarFormal

theorem peak_2_3 : Peak (TStarCoeff 2 3) := by
  apply peak_finite (TStarCoeff 2 3) 5 2 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [two_tail 3 k (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 3 < k by omega)]

theorem peak_2_4 : Peak (TStarCoeff 2 4) := by
  apply peak_finite (TStarCoeff 2 4) 5 2 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [two_tail 4 k (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 4 < k by omega)]

theorem peak_2_5 : Peak (TStarCoeff 2 5) := by
  apply peak_finite (TStarCoeff 2 5) 6 2 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [two_tail 5 k (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 5 < k by omega)]

theorem peak_2_6 : Peak (TStarCoeff 2 6) := by
  apply peak_finite (TStarCoeff 2 6) 7 2 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [two_tail 6 k (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 6 < k by omega)]

theorem peak_2_7 : Peak (TStarCoeff 2 7) := by
  apply peak_finite (TStarCoeff 2 7) 8 2 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [two_tail 7 k (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 7 < k by omega)]

theorem peak_3_3 : Peak (TStarCoeff 3 3) := by
  apply peak_finite (TStarCoeff 3 3) 5 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 3 3 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 3 < k by omega)]

theorem peak_3_4 : Peak (TStarCoeff 3 4) := by
  apply peak_finite (TStarCoeff 3 4) 5 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 3 4 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 4 < k by omega)]

theorem peak_3_5 : Peak (TStarCoeff 3 5) := by
  apply peak_finite (TStarCoeff 3 5) 6 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 3 5 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 5 < k by omega)]

theorem peak_3_6 : Peak (TStarCoeff 3 6) := by
  apply peak_finite (TStarCoeff 3 6) 7 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 3 6 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 6 < k by omega)]

theorem peak_3_7 : Peak (TStarCoeff 3 7) := by
  apply peak_finite (TStarCoeff 3 7) 8 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 3 7 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 7 < k by omega)]

theorem peak_3_8 : Peak (TStarCoeff 3 8) := by
  apply peak_finite (TStarCoeff 3 8) 9 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 3 8 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 8 < k by omega)]

theorem peak_3_9 : Peak (TStarCoeff 3 9) := by
  apply peak_finite (TStarCoeff 3 9) 10 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 3 9 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 9 < k by omega)]

theorem peak_3_10 : Peak (TStarCoeff 3 10) := by
  apply peak_finite (TStarCoeff 3 10) 11 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 3 10 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 10 < k by omega)]

theorem peak_4_4 : Peak (TStarCoeff 4 4) := by
  apply peak_finite (TStarCoeff 4 4) 5 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 4 4 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 4 < k by omega)]

theorem peak_4_5 : Peak (TStarCoeff 4 5) := by
  apply peak_finite (TStarCoeff 4 5) 6 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 4 5 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 5 < k by omega)]

theorem peak_4_6 : Peak (TStarCoeff 4 6) := by
  apply peak_finite (TStarCoeff 4 6) 7 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 4 6 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 6 < k by omega)]

theorem peak_4_7 : Peak (TStarCoeff 4 7) := by
  apply peak_finite (TStarCoeff 4 7) 8 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 4 7 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 7 < k by omega)]

theorem peak_4_8 : Peak (TStarCoeff 4 8) := by
  apply peak_finite (TStarCoeff 4 8) 9 3 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 4 8 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 8 < k by omega)]

theorem peak_4_9 : Peak (TStarCoeff 4 9) := by
  apply peak_finite (TStarCoeff 4 9) 10 4 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 4 9 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 9 < k by omega)]

theorem peak_4_10 : Peak (TStarCoeff 4 10) := by
  apply peak_finite (TStarCoeff 4 10) 11 4 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 4 10 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 10 < k by omega)]

theorem peak_4_11 : Peak (TStarCoeff 4 11) := by
  apply peak_finite (TStarCoeff 4 11) 12 4 (by omega)
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · norm_num [Fin.forall_fin_succ, TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · intro k hk
    rw [coeff_tail 4 11 k (by omega) (by omega) (by omega), Nat.choose_eq_zero_of_lt (show 11 < k by omega)]

theorem bad_2 (n : ℕ) (hlo : 8 ≤ n) (hhi : n ≤ 8) : ¬ Peak (TStarCoeff 2 n) := by
  apply valley_not_peak (TStarCoeff 2 n) 2
  · interval_cases n <;> norm_num [TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · interval_cases n <;> norm_num [TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem bad_3 (n : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 17) : ¬ Peak (TStarCoeff 3 n) := by
  apply valley_not_peak (TStarCoeff 3 n) 3
  · interval_cases n <;> norm_num [TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · interval_cases n <;> norm_num [TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem bad_4 (n : ℕ) (hlo : 12 ≤ n) (hhi : n ≤ 39) : ¬ Peak (TStarCoeff 4 n) := by
  apply valley_not_peak (TStarCoeff 4 n) 4
  · interval_cases n <;> norm_num [TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  · interval_cases n <;> norm_num [TStarCoeff, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

end TStarFormal

namespace TStarFormal

theorem classification_four (n : ℕ) (hn : 4 ≤ n) :
    Peak (TStarCoeff 4 n) ↔ ¬ (12 ≤ n ∧ n ≤ 39) := by
  constructor
  · intro hp h
    exact bad_4 n h.1 h.2 hp
  · intro h
    by_cases h40 : 40 ≤ n
    · exact four_peak_large n h40
    have h11 : n ≤ 11 := by omega
    interval_cases n
    · exact peak_4_4
    · exact peak_4_5
    · exact peak_4_6
    · exact peak_4_7
    · exact peak_4_8
    · exact peak_4_9
    · exact peak_4_10
    · exact peak_4_11

theorem classification_three (n : ℕ) (hn : 3 ≤ n) :
    Peak (TStarCoeff 3 n) ↔ ¬ (11 ≤ n ∧ n ≤ 17) := by
  constructor
  · intro hp h
    exact bad_3 n h.1 h.2 hp
  · intro h
    by_cases h18 : 18 ≤ n
    · exact three_peak_large n h18
    have h10 : n ≤ 10 := by omega
    interval_cases n
    · exact peak_3_3
    · exact peak_3_4
    · exact peak_3_5
    · exact peak_3_6
    · exact peak_3_7
    · exact peak_3_8
    · exact peak_3_9
    · exact peak_3_10

theorem classification_two (n : ℕ) (hn : 2 ≤ n) :
    Peak (TStarCoeff 2 n) ↔ n ≠ 8 := by
  constructor
  · intro hp h
    subst n
    exact bad_2 8 (by omega) (by omega) hp
  · intro h
    by_cases h9 : 9 ≤ n
    · exact two_peak_large n h9
    have h7 : n ≤ 7 := by omega
    interval_cases n
    · exact two_two_peak
    · exact peak_2_3
    · exact peak_2_4
    · exact peak_2_5
    · exact peak_2_6
    · exact peak_2_7

end TStarFormal

-- Exact arithmetic target, with only the previously recorded numeral syntax repair.
theorem tstar_complete_classification (m n : Nat) (hm : 1 ≤ m) (hmn : m ≤ n) :
    TStarUnimodal m n ↔ ¬ TStarBad m n := by
  change TStarFormal.Peak (TStarCoeff m n) ↔ ¬ TStarBad m n
  by_cases hm5 : 5 ≤ m
  · simpa [TStarBad, TStarFormal.Threshold, show m ≠ 2 by omega,
      show m ≠ 3 by omega, show 4 ≤ m by omega] using TStarFormal.classification_large m n hm5 hmn
  · interval_cases m
    · simpa [TStarBad] using TStarFormal.one_peak n
    · simpa [TStarBad] using TStarFormal.classification_two n hmn
    · simpa [TStarBad] using TStarFormal.classification_three n hmn
    · simpa [TStarBad, Nat.factorial] using TStarFormal.classification_four n hmn


namespace TStarGraph

def grid (m n : ℕ) : SimpleGraph (Fin m × Fin n) where
  Adj u v := u.1 ≠ v.1 ∧ u.2 ≠ v.2
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

def GeneralPosition {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
    G.edist x z ≠ ⊤ → G.edist x z ≠ G.edist x y + G.edist y z

def Cluster {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ z → G.Adj x y → G.Adj y z → G.Adj x z

theorem third_fin (n : ℕ) (hn : 3 ≤ n) (a b : Fin n) : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  by_contra h
  push_neg at h
  have h0 := h (⟨0, by omega⟩ : Fin n)
  have h1 := h (⟨1, by omega⟩ : Fin n)
  have h2 := h (⟨2, by omega⟩ : Fin n)
  grind [Fin.ext_iff]


theorem common_neighbor (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) (u v : Fin m × Fin n) :
    ((grid m n).commonNeighbors u v).Nonempty := by
  obtain ⟨i,hi,hj⟩ := third_fin m hm u.1 v.1
  obtain ⟨a,ha,hb⟩ := third_fin n hn u.2 v.2
  refine ⟨(i,a), ?_⟩
  exact ⟨⟨hi.symm,ha.symm⟩,⟨hj.symm,hb.symm⟩⟩

theorem distance_nonadjacent (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n)
    (u v : Fin m × Fin n) (huv : u ≠ v) (h : ¬ (grid m n).Adj u v) :
    (grid m n).edist u v = 2 := by
  exact SimpleGraph.edist_eq_two_iff.mpr ⟨huv,h,common_neighbor m n hm hn u v⟩

theorem general_position_iff_cluster (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n)
    (S : Set (Fin m × Fin n)) : GeneralPosition (grid m n) S ↔ Cluster (grid m n) S := by
  constructor
  · intro h x hx y hy z hz hxz hxy hyz
    by_contra hno
    have hd := distance_nonadjacent m n hm hn x z hxz hno
    have h1 := SimpleGraph.edist_eq_one_iff_adj.mpr hxy
    have h2 := SimpleGraph.edist_eq_one_iff_adj.mpr hyz
    have hh := h x hx y hy z hz hxy.ne hyz.ne hxz (by rw [hd]; simp)
    apply hh
    rw [hd,h1,h2]
    norm_num
  · intro h x hx y hy z hz hxy hyz hxz hfin heq
    classical
    have hdxy : (grid m n).edist x y = (if (grid m n).Adj x y then 1 else 2) := by
      split_ifs with ht
      · exact SimpleGraph.edist_eq_one_iff_adj.mpr ht
      · exact distance_nonadjacent m n hm hn x y hxy ht
    have hdyz : (grid m n).edist y z = (if (grid m n).Adj y z then 1 else 2) := by
      split_ifs with ht
      · exact SimpleGraph.edist_eq_one_iff_adj.mpr ht
      · exact distance_nonadjacent m n hm hn y z hyz ht
    have hdxz : (grid m n).edist x z = (if (grid m n).Adj x z then 1 else 2) := by
      split_ifs with ht
      · exact SimpleGraph.edist_eq_one_iff_adj.mpr ht
      · exact distance_nonadjacent m n hm hn x z hxz ht
    rw [hdxy,hdyz,hdxz] at heq
    by_cases ha : (grid m n).Adj x y <;> by_cases hb : (grid m n).Adj y z <;>
      by_cases hc : (grid m n).Adj x z <;>
      simp only [ha,hb,hc,if_true,if_false] at heq <;> norm_num at heq
    exact hc (h x hx y hy z hz hxz ha hb)

end TStarGraph

namespace TStarGraph

def InRow {m n : ℕ} (S : Set (Fin m × Fin n)) : Prop :=
  ∃ i, ∀ v ∈ S, v.1=i

def InColumn {m n : ℕ} (S : Set (Fin m × Fin n)) : Prop :=
  ∃ j, ∀ v ∈ S, v.2=j

def IsMatching {m n : ℕ} (S : Set (Fin m × Fin n)) : Prop :=
  Set.InjOn Prod.fst S ∧ Set.InjOn Prod.snd S

def InRectangle {m n : ℕ} (S : Set (Fin m × Fin n)) : Prop :=
  ∃ i h : Fin m, ∃ j l : Fin n, i≠h ∧ j≠l ∧
    ∀ v ∈ S, (v.1=i ∨ v.1=h) ∧ (v.2=j ∨ v.2=l)

theorem rectangle_from_three {m n : ℕ} (S : Set (Fin m × Fin n))
    (hc : Cluster (grid m n) S) (i h : Fin m) (j l : Fin n)
    (hih : i≠h) (hjl : j≠l) (hu : (i,j) ∈ S) (hv : (i,l) ∈ S) (hw : (h,j) ∈ S) :
    ∀ z ∈ S, (z.1=i ∨ z.1=h) ∧ (z.2=j ∨ z.2=l) := by
  intro z hz
  have hzcol : z.2=j ∨ z.2=l := by
    by_contra hn
    push_neg at hn
    by_cases hzi : z.1=i
    · have hzv : z ≠ (i,l) := by intro he; apply hn.2; exact congrArg Prod.snd he
      have ha : (grid m n).Adj z (h,j) := ⟨by simpa [hzi] using hih,hn.1⟩
      have hb : (grid m n).Adj (h,j) (i,l) := ⟨hih.symm,hjl⟩
      exact (hc z hz (h,j) hw (i,l) hv hzv ha hb).1 hzi
    · have huv : (i,j) ≠ (i,l) := by intro he; exact hjl (congrArg Prod.snd he)
      have ha : (grid m n).Adj (i,j) z := ⟨(Ne.symm hzi),hn.1.symm⟩
      have hb : (grid m n).Adj z (i,l) := ⟨hzi,hn.2⟩
      exact (hc (i,j) hu z hz (i,l) hv huv ha hb).1 rfl
  refine ⟨?_,hzcol⟩
  by_cases hzi : z.1=i
  · exact Or.inl hzi
  right
  by_contra hzh
  rcases hzcol with hzj | hzl
  · have hzw : z ≠ (h,j) := by intro he; exact hzh (congrArg Prod.fst he)
    have ha : (grid m n).Adj z (i,l) := ⟨hzi,by simpa [hzj] using hjl⟩
    have hb : (grid m n).Adj (i,l) (h,j) := ⟨hih,hjl.symm⟩
    exact (hc z hz (i,l) hv (h,j) hw hzw ha hb).2 hzj
  · have huw : (i,j) ≠ (h,j) := by intro he; exact hih (congrArg Prod.fst he)
    have ha : (grid m n).Adj (i,j) z := ⟨(Ne.symm hzi),by simpa [hzl] using hjl⟩
    have hb : (grid m n).Adj z (h,j) := ⟨hzh,by simpa [hzl] using hjl.symm⟩
    exact (hc (i,j) hu z hz (h,j) hw huw ha hb).2 rfl

theorem pair_row_or_rectangle {m n : ℕ} (S : Set (Fin m × Fin n))
    (hc : Cluster (grid m n) S) (i : Fin m) (j l : Fin n)
    (hjl : j≠l) (hu : (i,j) ∈ S) (hv : (i,l) ∈ S) : InRow S ∨ InRectangle S := by
  classical
  by_cases hr : ∀ z ∈ S, z.1=i
  · exact Or.inl ⟨i,hr⟩
  push_neg at hr
  obtain ⟨w,hw,hwi⟩ := hr
  have hwcol : w.2=j ∨ w.2=l := by
    by_contra h
    push_neg at h
    have huv : (i,j) ≠ (i,l) := by intro he; exact hjl (congrArg Prod.snd he)
    have ha : (grid m n).Adj (i,j) w := ⟨hwi.symm,h.1.symm⟩
    have hb : (grid m n).Adj w (i,l) := ⟨hwi,h.2⟩
    exact (hc (i,j) hu w hw (i,l) hv huv ha hb).1 rfl
  right
  rcases hwcol with hwj | hwl
  · have he : w = (w.1,j) := Prod.ext rfl hwj
    rw [he] at hw
    exact ⟨i,w.1,j,l,hwi.symm,hjl,rectangle_from_three S hc i w.1 j l hwi.symm hjl hu hv hw⟩
  · have he : w = (w.1,l) := Prod.ext rfl hwl
    rw [he] at hw
    exact ⟨i,w.1,l,j,hwi.symm,hjl.symm,rectangle_from_three S hc i w.1 l j hwi.symm hjl.symm hv hu hw⟩

end TStarGraph

namespace TStarGraph

theorem cluster_swap {m n : ℕ} (S : Set (Fin m × Fin n)) (hc : Cluster (grid m n) S) :
    Cluster (grid n m) {v | v.swap ∈ S} := by
  intro x hx y hy z hz hxz hxy hyz
  have he : x.swap ≠ z.swap := by intro hh; apply hxz; exact Prod.swap_injective hh
  have hh := hc x.swap hx y.swap hy z.swap hz he ⟨hxy.2,hxy.1⟩ ⟨hyz.2,hyz.1⟩
  exact ⟨hh.2,hh.1⟩

theorem cluster_structure {m n : ℕ} (S : Set (Fin m × Fin n)) (hc : Cluster (grid m n) S) :
    InRow S ∨ InColumn S ∨ IsMatching S ∨ InRectangle S := by
  classical
  by_cases hf : Set.InjOn Prod.fst S
  · by_cases hs : Set.InjOn Prod.snd S
    · exact Or.inr (Or.inr (Or.inl ⟨hf,hs⟩))
    · simp only [Set.InjOn] at hs
      push_neg at hs
      obtain ⟨x,hx,y,hy,hxy,hne⟩ := hs
      have hjl : x.1 ≠ y.1 := by intro he; exact hne (Prod.ext he hxy)
      let S' : Set (Fin n × Fin m) := {v | v.swap ∈ S}
      have hx' : (x.2,x.1) ∈ S' := hx
      have hy' : (x.2,y.1) ∈ S' := by
        change (y.1,x.2) ∈ S
        simpa only [hxy] using hy
      rcases pair_row_or_rectangle S' (cluster_swap S hc) x.2 x.1 y.1 hjl hx' hy' with hr | hr
      · rcases hr with ⟨i,hi⟩
        exact Or.inr (Or.inl ⟨i,fun v hv => hi v.swap hv⟩)
      · rcases hr with ⟨i,h,j,l,hih,hjl,hrect⟩
        refine Or.inr (Or.inr (Or.inr ⟨j,l,i,h,hjl,hih,?_⟩))
        intro v hv
        have hh := hrect v.swap hv
        exact ⟨hh.2,hh.1⟩
  · simp only [Set.InjOn] at hf
    push_neg at hf
    obtain ⟨x,hx,y,hy,hxy,hne⟩ := hf
    have hjl : x.2 ≠ y.2 := by intro he; exact hne (Prod.ext hxy he)
    have hx' : (x.1,x.2) ∈ S := hx
    have hy' : (x.1,y.2) ∈ S := by simpa only [hxy] using hy
    rcases pair_row_or_rectangle S hc x.1 x.2 y.2 hjl hx' hy' with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inr (Or.inr hr))

theorem structure_cluster {m n : ℕ} (S : Set (Fin m × Fin n))
    (hs : InRow S ∨ InColumn S ∨ IsMatching S ∨ InRectangle S) : Cluster (grid m n) S := by
  rcases hs with hr | hc | hm | hrect
  · rcases hr with ⟨i,hi⟩
    intro x hx y hy z hz hxz hxy hyz
    exact False.elim (hxy.1 ((hi x hx).trans (hi y hy).symm))
  · rcases hc with ⟨j,hj⟩
    intro x hx y hy z hz hxz hxy hyz
    exact False.elim (hxy.2 ((hj x hx).trans (hj y hy).symm))
  · intro x hx y hy z hz hxz hxy hyz
    exact ⟨fun he => hxz (hm.1 hx hz he),fun he => hxz (hm.2 hx hz he)⟩
  · rcases hrect with ⟨i,h,j,l,hih,hjl,hr⟩
    intro x hx y hy z hz hxz hxy hyz
    have hx' := hr x hx
    have hy' := hr y hy
    have hz' := hr z hz
    have he1 : x.1=z.1 := by
      have h1 := hxy.1
      have h2 := hyz.1
      grind
    have he2 : x.2=z.2 := by
      have h1 := hxy.2
      have h2 := hyz.2
      grind
    exact False.elim (hxz (Prod.ext he1 he2))

theorem general_position_structure (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n)
    (S : Set (Fin m × Fin n)) : GeneralPosition (grid m n) S ↔
      InRow S ∨ InColumn S ∨ IsMatching S ∨ InRectangle S := by
  rw [general_position_iff_cluster m n hm hn S]
  exact ⟨cluster_structure S,structure_cluster S⟩

end TStarGraph

namespace TStarGraph

noncomputable def gpCoeff (m n k : ℕ) : ℕ :=
  Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ GeneralPosition (grid m n) (S : Set (Fin m × Fin n))}

theorem general_position_small {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (hs : S.card ≤ 2) : GeneralPosition G (S : Set V) := by
  intro x hx y hy z hz hxy hyz hxz hfin heq
  have hsub : ({x,y,z} : Finset V) ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  have he : ({x,y,z} : Finset V).card=3 := by
    simp [hxy,hxz,hyz]
  rw [he] at hc
  omega

theorem card_fixed_subsets (α : Type*) [Fintype α] (k : ℕ) :
    Nat.card {S : Finset α // S.card=k} = (Fintype.card α).choose k := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_of_subtype ((Finset.univ : Finset α).powersetCard k)
    (by intro S; simp)]
  simp

theorem gpCoeff_small (m n k : ℕ) (hk : k ≤ 2) : gpCoeff m n k = (m*n).choose k := by
  classical
  let e : {S : Finset (Fin m × Fin n) // S.card=k ∧ GeneralPosition (grid m n) (S : Set (Fin m × Fin n))} ≃
      {S : Finset (Fin m × Fin n) // S.card=k} :=
    { toFun := fun s => ⟨s.1,s.2.1⟩
      invFun := fun s => ⟨s.1,s.2,general_position_small (grid m n) s.1 (by omega)⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  unfold gpCoeff
  rw [Nat.card_congr e,card_fixed_subsets]
  simp

end TStarGraph

namespace TStarGraph

noncomputable def rowSet {m n : ℕ} (i : Fin m) (J : Finset (Fin n)) : Finset (Fin m × Fin n) :=
  J.image (fun j => (i,j))

theorem rowSet_mem {m n : ℕ} (i : Fin m) (J : Finset (Fin n)) (v : Fin m × Fin n) :
    v ∈ rowSet i J ↔ v.1=i ∧ v.2∈J := by
  simp [rowSet,Prod.ext_iff,eq_comm,and_comm]

theorem rowSet_card {m n : ℕ} (i : Fin m) (J : Finset (Fin n)) : (rowSet i J).card=J.card := by
  unfold rowSet
  apply Finset.card_image_of_injective
  intro a b he
  exact congrArg Prod.snd he

noncomputable def rowEncode (m n k : ℕ) :
    (Fin m × {J : Finset (Fin n) // J.card=k}) →
      {S : Finset (Fin m × Fin n) // S.card=k ∧ InRow (S : Set (Fin m × Fin n))} :=
  fun p => ⟨rowSet p.1 p.2.1,by rw [rowSet_card,p.2.2],⟨p.1,by
    intro v hv
    exact (rowSet_mem p.1 p.2.1 v).mp hv |>.1⟩⟩

theorem rowEncode_injective (m n k : ℕ) (hk : 1 ≤ k) : Function.Injective (rowEncode m n k) := by
  intro a b he
  have heS : rowSet a.1 a.2.1 = rowSet b.1 b.2.1 := congrArg Subtype.val he
  have ha : a.2.1.Nonempty := Finset.card_pos.mp (by rw [a.2.2]; omega)
  obtain ⟨j,hj⟩ := ha
  have hmem : (a.1,j) ∈ rowSet b.1 b.2.1 := by
    rw [← heS]
    exact (rowSet_mem a.1 a.2.1 (a.1,j)).mpr ⟨rfl,hj⟩
  have hi : a.1=b.1 := ((rowSet_mem b.1 b.2.1 (a.1,j)).mp hmem).1
  have hJ : a.2.1=b.2.1 := by
    ext x
    have hx := congrArg (fun S => (a.1,x) ∈ S) heS
    simpa only [rowSet_mem,hi,eq_self_iff_true,true_and] using (iff_of_eq hx)
  exact Prod.ext hi (Subtype.ext hJ)

theorem rowEncode_surjective (m n k : ℕ) : Function.Surjective (rowEncode m n k) := by
  intro S
  obtain ⟨i,hi⟩ := S.2.2
  let J := S.1.image Prod.snd
  have hj : J.card=k := by
    calc
      J.card = S.1.card := Finset.card_image_iff.mpr (by
        intro x hx y hy he
        exact Prod.ext ((hi x hx).trans (hi y hy).symm) he)
      _ = k := S.2.1
  refine ⟨(i,⟨J,hj⟩),Subtype.ext ?_⟩
  change rowSet i J = S.1
  ext v
  rw [rowSet_mem]
  constructor
  · rintro ⟨hvi,hvj⟩
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hvj
    have hvw : v=w := Prod.ext (hvi.trans (hi w hw).symm) he.symm
    simpa only [hvw] using hw
  · intro hv
    exact ⟨hi v hv,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩

theorem count_rows (m n k : ℕ) (hk : 1 ≤ k) :
    Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ InRow (S : Set (Fin m × Fin n))} =
      m*n.choose k := by
  classical
  have he := Nat.card_congr (Equiv.ofBijective (rowEncode m n k)
    ⟨rowEncode_injective m n k hk,rowEncode_surjective m n k⟩)
  rw [← he,Nat.card_prod,card_fixed_subsets]
  simp

end TStarGraph

namespace TStarGraph

noncomputable def matchingSet {m n : ℕ} (I : Finset (Fin m)) (f : I ↪ Fin n) : Finset (Fin m × Fin n) :=
  I.attach.image (fun i => (i.1,f i))

theorem matchingSet_mem {m n : ℕ} (I : Finset (Fin m)) (f : I ↪ Fin n) (v : Fin m × Fin n) :
    v ∈ matchingSet I f ↔ ∃ h : v.1∈I, f ⟨v.1,h⟩=v.2 := by
  constructor
  · intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    subst v
    exact ⟨i.2,rfl⟩
  · rintro ⟨hi,hf⟩
    exact Finset.mem_image.mpr ⟨⟨v.1,hi⟩,Finset.mem_attach _ _,Prod.ext rfl hf⟩

theorem matchingSet_card {m n : ℕ} (I : Finset (Fin m)) (f : I ↪ Fin n) :
    (matchingSet I f).card=I.card := by
  unfold matchingSet
  rw [Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro a b he
    exact Subtype.ext (congrArg Prod.fst he)

theorem matchingSet_matching {m n : ℕ} (I : Finset (Fin m)) (f : I ↪ Fin n) :
    IsMatching (matchingSet I f : Set (Fin m × Fin n)) := by
  constructor
  · intro x hx y hy he
    obtain ⟨hi,hf⟩ := (matchingSet_mem I f x).mp hx
    obtain ⟨hj,hg⟩ := (matchingSet_mem I f y).mp hy
    have he' : (⟨x.1,hi⟩ : I)=⟨y.1,hj⟩ := Subtype.ext he
    exact Prod.ext he (hf.symm.trans ((congrArg f he').trans hg))
  · intro x hx y hy he
    obtain ⟨hi,hf⟩ := (matchingSet_mem I f x).mp hx
    obtain ⟨hj,hg⟩ := (matchingSet_mem I f y).mp hy
    have he' := f.injective (hf.trans (he.trans hg.symm))
    exact Prod.ext (congrArg Subtype.val he') he

theorem matchingSet_rows {m n : ℕ} (I : Finset (Fin m)) (f : I ↪ Fin n) :
    (matchingSet I f).image Prod.fst=I := by
  ext i
  constructor
  · intro hi
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hi
    obtain ⟨hh,hf⟩ := (matchingSet_mem I f v).mp hv
    simpa only [he] using hh
  · intro hi
    exact Finset.mem_image.mpr ⟨(i,f ⟨i,hi⟩),(matchingSet_mem I f _).mpr ⟨hi,rfl⟩,rfl⟩

noncomputable def matchingEncode (m n k : ℕ) :
    (Σ I : {I : Finset (Fin m) // I.card=k}, I.1 ↪ Fin n) →
      {S : Finset (Fin m × Fin n) // S.card=k ∧ IsMatching (S : Set (Fin m × Fin n))} :=
  fun p => ⟨matchingSet p.1.1 p.2,by rw [matchingSet_card,p.1.2],matchingSet_matching p.1.1 p.2⟩

theorem matchingEncode_injective (m n k : ℕ) : Function.Injective (matchingEncode m n k) := by
  rintro ⟨I,f⟩ ⟨J,g⟩ he
  have hs : matchingSet I.1 f=matchingSet J.1 g := congrArg Subtype.val he
  have hi := congrArg (Finset.image Prod.fst) hs
  rw [matchingSet_rows,matchingSet_rows] at hi
  have hij : I=J := Subtype.ext hi
  subst J
  have hfg : f=g := by
    ext i
    have hv : (i.1,f i)∈matchingSet I.1 g := by
      rw [← hs]
      exact (matchingSet_mem I.1 f _).mpr ⟨i.2,rfl⟩
    obtain ⟨h,hf⟩ := (matchingSet_mem I.1 g _).mp hv
    exact congrArg Fin.val hf.symm
  subst g
  rfl

noncomputable def vertexForRow {m n : ℕ} (S : Finset (Fin m × Fin n))
    (i : ↥(S.image Prod.fst)) : Fin m × Fin n := Classical.choose (Finset.mem_image.mp i.2)

theorem vertexForRow_spec {m n : ℕ} (S : Finset (Fin m × Fin n)) (i : ↥(S.image Prod.fst)) :
    vertexForRow S i ∈ S ∧ (vertexForRow S i).1=i.1 := Classical.choose_spec (Finset.mem_image.mp i.2)

theorem matchingEncode_surjective (m n k : ℕ) : Function.Surjective (matchingEncode m n k) := by
  classical
  intro S
  let I := S.1.image Prod.fst
  have hi : I.card=k := by
    rw [Finset.card_image_iff.mpr S.2.2.1]
    exact S.2.1
  let f : I ↪ Fin n :=
    { toFun := fun i => (vertexForRow S.1 i).2
      inj' := by
        intro a b he
        have h := S.2.2.2 (vertexForRow_spec S.1 a).1 (vertexForRow_spec S.1 b).1 he
        apply Subtype.ext
        exact (vertexForRow_spec S.1 a).2.symm.trans ((congrArg Prod.fst h).trans (vertexForRow_spec S.1 b).2) }
  refine ⟨⟨⟨I,hi⟩,f⟩,Subtype.ext ?_⟩
  change matchingSet I f=S.1
  ext v
  rw [matchingSet_mem]
  constructor
  · rintro ⟨hv,hf⟩
    have hrow := vertexForRow_spec S.1 (⟨v.1,hv⟩ : I)
    have he : vertexForRow S.1 (⟨v.1,hv⟩ : I)=v := Prod.ext hrow.2 hf
    simpa only [he] using hrow.1
  · intro hv
    have hI : v.1∈I := Finset.mem_image.mpr ⟨v,hv,rfl⟩
    refine ⟨hI,?_⟩
    have hrow := vertexForRow_spec S.1 (⟨v.1,hI⟩ : I)
    have he := S.2.2.1 hrow.1 hv hrow.2
    exact congrArg Prod.snd he

theorem count_matchings (m n k : ℕ) :
    Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ IsMatching (S : Set (Fin m × Fin n))} =
      k.factorial*m.choose k*n.choose k := by
  classical
  have he := Nat.card_congr (Equiv.ofBijective (matchingEncode m n k)
    ⟨matchingEncode_injective m n k,matchingEncode_surjective m n k⟩)
  rw [← he,Nat.card_sigma]
  have hc : ∀ I : {I : Finset (Fin m) // I.card=k}, Nat.card (I.1 ↪ Fin n)=n.descFactorial k := by
    intro I
    rw [Nat.card_eq_fintype_card,Fintype.card_embedding_eq]
    simp [I.2]
  simp_rw [hc]
  rw [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,← Nat.card_eq_fintype_card,card_fixed_subsets]
  simp only [Fintype.card_fin,Nat.descFactorial_eq_factorial_mul_choose]
  ring

end TStarGraph

namespace TStarGraph

theorem count_columns (m n k : ℕ) (hk : 1 ≤ k) :
    Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ InColumn (S : Set (Fin m × Fin n))} =
      n*m.choose k := by
  classical
  let e : {S : Finset (Fin m × Fin n) // S.card=k ∧ InColumn (S : Set (Fin m × Fin n))} ≃
      {S : Finset (Fin n × Fin m) // S.card=k ∧ InRow (S : Set (Fin n × Fin m))} :=
    { toFun := fun s => ⟨s.1.image Prod.swap,by rw [Finset.card_image_of_injective _ Prod.swap_injective,s.2.1],by
        obtain ⟨j,hj⟩ := s.2.2
        refine ⟨j,?_⟩
        intro v hv
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
        exact hj w hw⟩
      invFun := fun s => ⟨s.1.image Prod.swap,by rw [Finset.card_image_of_injective _ Prod.swap_injective,s.2.1],by
        obtain ⟨j,hj⟩ := s.2.2
        refine ⟨j,?_⟩
        intro v hv
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
        exact hj w hw⟩
      left_inv := by intro s; apply Subtype.ext; simp [Finset.image_image]
      right_inv := by intro s; apply Subtype.ext; simp [Finset.image_image] }
  rw [Nat.card_congr e,count_rows n m k hk]

theorem rectangle_rows_full {m n : ℕ} (S : Finset (Fin m × Fin n))
    (I : Finset (Fin m)) (J : Finset (Fin n)) (hI : I.card=2) (hJ : J.card=2)
    (hS : S ⊆ I.product J) (hk : 3 ≤ S.card) : S.image Prod.fst=I := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_product.mp (hS hv)).1
  · intro i hi
    by_contra hno
    have hs : S ⊆ (I.erase i).product J := by
      intro v hv
      have hp := Finset.mem_product.mp (hS hv)
      refine Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨?_,hp.1⟩,hp.2⟩
      intro he
      exact hno (Finset.mem_image.mpr ⟨v,hv,he⟩)
    have hc := Finset.card_le_card hs
    rw [Finset.product_eq_sprod,Finset.card_product,Finset.card_erase_of_mem hi,hI,hJ] at hc
    omega

theorem rectangle_columns_full {m n : ℕ} (S : Finset (Fin m × Fin n))
    (I : Finset (Fin m)) (J : Finset (Fin n)) (hI : I.card=2) (hJ : J.card=2)
    (hS : S ⊆ I.product J) (hk : 3 ≤ S.card) : S.image Prod.snd=J := by
  apply Finset.Subset.antisymm
  · intro j hj
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_product.mp (hS hv)).2
  · intro j hj
    by_contra hno
    have hs : S ⊆ I.product (J.erase j) := by
      intro v hv
      have hp := Finset.mem_product.mp (hS hv)
      refine Finset.mem_product.mpr ⟨hp.1,Finset.mem_erase.mpr ⟨?_,hp.2⟩⟩
      intro he
      exact hno (Finset.mem_image.mpr ⟨v,hv,he⟩)
    have hc := Finset.card_le_card hs
    rw [Finset.product_eq_sprod,Finset.card_product,Finset.card_erase_of_mem hj,hI,hJ] at hc
    omega

end TStarGraph

namespace TStarGraph

theorem subset_rectangle {m n : ℕ} (S : Finset (Fin m × Fin n))
    (I : Finset (Fin m)) (J : Finset (Fin n)) (hI : I.card=2) (hJ : J.card=2)
    (hS : S ⊆ I.product J) : InRectangle (S : Set (Fin m × Fin n)) := by
  obtain ⟨i,h,hih,rfl⟩ := Finset.card_eq_two.mp hI
  obtain ⟨j,l,hjl,rfl⟩ := Finset.card_eq_two.mp hJ
  refine ⟨i,h,j,l,hih,hjl,?_⟩
  intro v hv
  have hp := Finset.mem_product.mp (hS hv)
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hp

theorem rectangle_subset {m n : ℕ} (S : Finset (Fin m × Fin n))
    (hS : InRectangle (S : Set (Fin m × Fin n))) :
    ∃ I : Finset (Fin m), ∃ J : Finset (Fin n), I.card=2 ∧ J.card=2 ∧ S ⊆ I.product J := by
  obtain ⟨i,h,j,l,hih,hjl,hr⟩ := hS
  refine ⟨{i,h},{j,l},by simp [hih],by simp [hjl],?_⟩
  intro v hv
  apply Finset.mem_product.mpr
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hr v hv

abbrev RectIndex (m n : ℕ) :=
  {I : Finset (Fin m) // I.card=2} × {J : Finset (Fin n) // J.card=2}

noncomputable def rectangleEncode (m n k : ℕ) :
    (Σ R : RectIndex m n, {S : Finset (Fin m × Fin n) // S ⊆ R.1.1.product R.2.1 ∧ S.card=k}) →
      {S : Finset (Fin m × Fin n) // S.card=k ∧ InRectangle (S : Set (Fin m × Fin n))} :=
  fun p => ⟨p.2.1,p.2.2.2,subset_rectangle p.2.1 p.1.1.1 p.1.2.1 p.1.1.2 p.1.2.2 p.2.2.1⟩

theorem rectangleEncode_injective (m n k : ℕ) (hk : 3 ≤ k) :
    Function.Injective (rectangleEncode m n k) := by
  rintro ⟨R,S⟩ ⟨Q,T⟩ he
  have hst : S.1=T.1 := congrArg Subtype.val he
  have hR := rectangle_rows_full S.1 R.1.1 R.2.1 R.1.2 R.2.2 S.2.1 (by rw [S.2.2]; exact hk)
  have hQ := rectangle_rows_full T.1 Q.1.1 Q.2.1 Q.1.2 Q.2.2 T.2.1 (by rw [T.2.2]; exact hk)
  have hR' := rectangle_columns_full S.1 R.1.1 R.2.1 R.1.2 R.2.2 S.2.1 (by rw [S.2.2]; exact hk)
  have hQ' := rectangle_columns_full T.1 Q.1.1 Q.2.1 Q.1.2 Q.2.2 T.2.1 (by rw [T.2.2]; exact hk)
  have hi : R.1.1=Q.1.1 := hR.symm.trans ((congrArg (Finset.image Prod.fst) hst).trans hQ)
  have hj : R.2.1=Q.2.1 := hR'.symm.trans ((congrArg (Finset.image Prod.snd) hst).trans hQ')
  have hrq : R=Q := Prod.ext (Subtype.ext hi) (Subtype.ext hj)
  subst Q
  have hh : S=T := Subtype.ext hst
  subst T
  rfl

theorem rectangleEncode_surjective (m n k : ℕ) : Function.Surjective (rectangleEncode m n k) := by
  intro S
  obtain ⟨I,J,hI,hJ,hS⟩ := rectangle_subset S.1 S.2.2
  exact ⟨⟨(⟨I,hI⟩,⟨J,hJ⟩),⟨S.1,hS,S.2.1⟩⟩,rfl⟩

theorem card_subsets_within {α : Type*} [Fintype α] (X : Finset α) (k : ℕ) :
    Nat.card {S : Finset α // S ⊆ X ∧ S.card=k} = X.card.choose k := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_of_subtype (X.powersetCard k) (by intro S; simp)]
  exact Finset.card_powersetCard k X

theorem count_rectangles (m n k : ℕ) (hk : 3 ≤ k) :
    Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ InRectangle (S : Set (Fin m × Fin n))} =
      m.choose 2*n.choose 2*(4 : ℕ).choose k := by
  classical
  have he := Nat.card_congr (Equiv.ofBijective (rectangleEncode m n k)
    ⟨rectangleEncode_injective m n k hk,rectangleEncode_surjective m n k⟩)
  rw [← he,Nat.card_sigma]
  have hc : ∀ R : RectIndex m n,
      Nat.card {S : Finset (Fin m × Fin n) // S ⊆ R.1.1.product R.2.1 ∧ S.card=k} = (4 : ℕ).choose k := by
    intro R
    rw [card_subsets_within,Finset.product_eq_sprod,Finset.card_product,R.1.2,R.2.2]
  simp_rw [hc]
  rw [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,← Nat.card_eq_fintype_card]
  change Nat.card ({I : Finset (Fin m) // I.card=2} × {J : Finset (Fin n) // J.card=2}) * (4 : ℕ).choose k = _
  rw [Nat.card_prod,card_fixed_subsets,card_fixed_subsets]
  simp

end TStarGraph

namespace TStarGraph

theorem overlap_row {m n : ℕ} (S : Finset (Fin m × Fin n))
    (hr : InRow (S : Set (Fin m × Fin n)))
    (ho : InColumn (S : Set (Fin m × Fin n)) ∨ IsMatching (S : Set (Fin m × Fin n)) ∨ InRectangle (S : Set (Fin m × Fin n))) :
    S.card ≤ 2 := by
  obtain ⟨i,hi⟩ := hr
  rcases ho with hc | hm | ht
  · obtain ⟨j,hj⟩ := hc
    have hs : S ⊆ {(i,j)} := by
      intro v hv
      apply Finset.mem_singleton.mpr
      exact Prod.ext (hi v hv) (hj v hv)
    have hh := Finset.card_le_card hs
    simpa using (le_trans hh (by simp : ({(i,j)} : Finset (Fin m × Fin n)).card ≤ 2))
  · have hs : S.image Prod.fst ⊆ {i} := by
      intro a ha
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_singleton.mpr (hi v hv)
    have hh := Finset.card_le_card hs
    rw [Finset.card_image_iff.mpr hm.1,Finset.card_singleton] at hh
    omega
  · obtain ⟨I,J,hI,hJ,hs⟩ := rectangle_subset S ht
    have hs' : S ⊆ ({i} : Finset (Fin m)).product J := by
      intro v hv
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr (hi v hv),(Finset.mem_product.mp (hs hv)).2⟩
    have hh := Finset.card_le_card hs'
    simpa [Finset.product_eq_sprod,hJ] using hh

theorem overlap_column {m n : ℕ} (S : Finset (Fin m × Fin n))
    (hc : InColumn (S : Set (Fin m × Fin n)))
    (ho : IsMatching (S : Set (Fin m × Fin n)) ∨ InRectangle (S : Set (Fin m × Fin n))) : S.card ≤ 2 := by
  obtain ⟨j,hj⟩ := hc
  rcases ho with hm | ht
  · have hs : S.image Prod.snd ⊆ {j} := by
      intro a ha
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_singleton.mpr (hj v hv)
    have hh := Finset.card_le_card hs
    rw [Finset.card_image_iff.mpr hm.2,Finset.card_singleton] at hh
    omega
  · obtain ⟨I,J,hI,hJ,hs⟩ := rectangle_subset S ht
    have hs' : S ⊆ I.product ({j} : Finset (Fin n)) := by
      intro v hv
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hs hv)).1,Finset.mem_singleton.mpr (hj v hv)⟩
    have hh := Finset.card_le_card hs'
    simpa [Finset.product_eq_sprod,hI] using hh

theorem overlap_matching_rectangle {m n : ℕ} (S : Finset (Fin m × Fin n))
    (hm : IsMatching (S : Set (Fin m × Fin n))) (ht : InRectangle (S : Set (Fin m × Fin n))) : S.card ≤ 2 := by
  obtain ⟨I,J,hI,hJ,hs⟩ := rectangle_subset S ht
  have hs' : S.image Prod.fst ⊆ I := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (hs hv)).1
  have hh := Finset.card_le_card hs'
  rwa [Finset.card_image_iff.mpr hm.1,hI] at hh

theorem card_disjoint_or {α : Type*} [Finite α] (p q : α → Prop)
    (h : ∀ a, p a → q a → False) :
    Nat.card {a // p a ∨ q a} = Nat.card {a // p a} + Nat.card {a // q a} := by
  classical
  letI := Fintype.ofFinite α
  have hd : Disjoint p q := by
    apply disjoint_iff.mpr
    funext a
    apply propext
    exact ⟨fun ha => h a ha.1 ha.2,False.elim⟩
  simp only [Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_or_disjoint p q hd

theorem gpCoeff_large (m n k : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    gpCoeff m n k = m*n.choose k+n*m.choose k+k.factorial*m.choose k*n.choose k+
      m.choose 2*n.choose 2*(4 : ℕ).choose k := by
  classical
  let R := fun S : Finset (Fin m × Fin n) => S.card=k ∧ InRow (S : Set (Fin m × Fin n))
  let C := fun S : Finset (Fin m × Fin n) => S.card=k ∧ InColumn (S : Set (Fin m × Fin n))
  let M := fun S : Finset (Fin m × Fin n) => S.card=k ∧ IsMatching (S : Set (Fin m × Fin n))
  let T := fun S : Finset (Fin m × Fin n) => S.card=k ∧ InRectangle (S : Set (Fin m × Fin n))
  have he : gpCoeff m n k = Nat.card {S // R S ∨ C S ∨ M S ∨ T S} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun S => by
      change (S.card=k ∧ GeneralPosition (grid m n) (S : Set (Fin m × Fin n))) ↔ _
      rw [general_position_structure m n hm hn]
      simp only [R,C,M,T,and_or_left])
  have hR : ∀ S, R S → (C S ∨ M S ∨ T S) → False := by
    intro S hr ho
    have hh : S.card ≤ 2 := overlap_row S hr.2 (by
      rcases ho with hc | hm | ht
      · exact Or.inl hc.2
      · exact Or.inr (Or.inl hm.2)
      · exact Or.inr (Or.inr ht.2))
    have := hr.1
    omega
  have hC : ∀ S, C S → (M S ∨ T S) → False := by
    intro S hc ho
    have hh : S.card ≤ 2 := overlap_column S hc.2 (by
      rcases ho with hm | ht
      · exact Or.inl hm.2
      · exact Or.inr ht.2)
    have := hc.1
    omega
  have hM : ∀ S, M S → T S → False := by
    intro S hm ht
    have hh := overlap_matching_rectangle S hm.2 ht.2
    have := hm.1
    omega
  rw [he,card_disjoint_or R (fun S => C S ∨ M S ∨ T S) hR,
    card_disjoint_or C (fun S => M S ∨ T S) hC,card_disjoint_or M T hM]
  change Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ InRow (S : Set (Fin m × Fin n))} +
    (Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ InColumn (S : Set (Fin m × Fin n))} +
    (Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ IsMatching (S : Set (Fin m × Fin n))} +
    Nat.card {S : Finset (Fin m × Fin n) // S.card=k ∧ InRectangle (S : Set (Fin m × Fin n))})) = _
  rw [count_rows m n k (by omega),count_columns m n k (by omega),count_matchings,count_rectangles m n k hk]
  omega

end TStarGraph

namespace TStarGraph

theorem gpCoeff_of_all (m n : ℕ)
    (hall : ∀ S : Finset (Fin m × Fin n), GeneralPosition (grid m n) (S : Set (Fin m × Fin n))) (k : ℕ) :
    gpCoeff m n k = (m*n).choose k := by
  classical
  have he : gpCoeff m n k = Nat.card {S : Finset (Fin m × Fin n) // S.card=k} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun S => and_iff_left (hall S))
  rw [he,card_fixed_subsets]
  simp

theorem one_all_gp (n : ℕ) (S : Set (Fin 1 × Fin n)) : GeneralPosition (grid 1 n) S := by
  have hg : grid 1 n = ⊥ := by
    ext u v
    simp [grid,Subsingleton.elim u.1 v.1]
  intro x hx y hy z hz hxy hyz hxz hfin heq
  rw [hg,SimpleGraph.edist_bot_of_ne hxz] at hfin
  exact hfin rfl

theorem two_two_two_steps (x y z : Fin 2 × Fin 2)
    (hxy : (grid 2 2).Adj x y) (hyz : (grid 2 2).Adj y z) : x=z := by
  apply Prod.ext
  · have h1 := hxy.1
    have h2 := hyz.1
    omega
  · have h1 := hxy.2
    have h2 := hyz.2
    omega

theorem two_two_reachable (x z : Fin 2 × Fin 2) (h : (grid 2 2).Reachable x z) :
    x=z ∨ (grid 2 2).Adj x z := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl rfl
  | @cons x y z hxy p ih =>
    rcases ih with he | ha
    · subst z
      exact Or.inr hxy
    · exact Or.inl (two_two_two_steps x y z hxy ha)

theorem two_two_all_gp (S : Set (Fin 2 × Fin 2)) : GeneralPosition (grid 2 2) S := by
  intro x hx y hy z hz hxy hyz hxz hfin heq
  have hr := SimpleGraph.reachable_of_edist_ne_top hfin
  have ha := (two_two_reachable x z hr).resolve_left hxz
  have hd := SimpleGraph.edist_eq_one_iff_adj.mpr ha
  have h1 : (1 : ℕ∞) ≤ (grid 2 2).edist x y := Order.one_le_iff_pos.mpr (SimpleGraph.edist_pos_of_ne hxy)
  have h2 : (1 : ℕ∞) ≤ (grid 2 2).edist y z := Order.one_le_iff_pos.mpr (SimpleGraph.edist_pos_of_ne hyz)
  have hs := add_le_add h1 h2
  rw [← heq,hd] at hs
  norm_num at hs

theorem crown_same_row_distance (n : ℕ) (hn : 3 ≤ n) (x y : Fin 2 × Fin n)
    (hrow : x.1=y.1) (hne : x≠y) : (grid 2 n).edist x y=2 := by
  obtain ⟨i,hi⟩ := exists_ne x.1
  obtain ⟨j,hjx,hjy⟩ := third_fin n hn x.2 y.2
  apply SimpleGraph.edist_eq_two_iff.mpr
  refine ⟨hne,fun h => h.1 hrow,⟨(i,j),?_⟩⟩
  exact ⟨⟨hi.symm,hjx.symm⟩,⟨by simpa only [← hrow] using hi.symm,hjy.symm⟩⟩

theorem crown_opposite_distance (n : ℕ) (hn : 3 ≤ n) (x y : Fin 2 × Fin n)
    (hrow : x.1≠y.1) (hcol : x.2=y.2) : (grid 2 n).edist x y=3 := by
  obtain ⟨c,hcx,_⟩ := third_fin n hn x.2 x.2
  obtain ⟨d,hdx,hdc⟩ := third_fin n hn x.2 c
  have h1 : (grid 2 n).Adj x (y.1,c) := ⟨hrow,hcx.symm⟩
  have h2 : (grid 2 n).Adj (y.1,c) (x.1,d) := ⟨hrow.symm,hdc.symm⟩
  have h3 : (grid 2 n).Adj (x.1,d) y := ⟨hrow,by simpa only [← hcol] using hdx⟩
  have hle := (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil))).edist_le
  have hle' : (grid 2 n).edist x y ≤ 3 := by simpa using hle
  have hgt : (2 : ℕ∞) < (grid 2 n).edist x y := by
    apply SimpleGraph.two_lt_edist_iff.mpr
    refine ⟨fun he => hrow (congrArg Prod.fst he),fun ha => ha.2 hcol,?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzx := hz.1.1
    have hzy := hz.2.1
    omega
  have hge : (3 : ℕ∞) ≤ (grid 2 n).edist x y := by
    have h := Order.add_one_le_of_lt hgt
    norm_num at h
    exact h
  exact le_antisymm hle' hge

theorem crown_row_gp (n : ℕ) (hn : 3 ≤ n) (S : Set (Fin 2 × Fin n)) (hr : InRow S) :
    GeneralPosition (grid 2 n) S := by
  obtain ⟨i,hi⟩ := hr
  intro x hx y hy z hz hxy hyz hxz hfin heq
  have h1 := crown_same_row_distance n hn x y ((hi x hx).trans (hi y hy).symm) hxy
  have h2 := crown_same_row_distance n hn y z ((hi y hy).trans (hi z hz).symm) hyz
  have h3 := crown_same_row_distance n hn x z ((hi x hx).trans (hi z hz).symm) hxz
  rw [h1,h2,h3] at heq
  norm_num at heq

theorem crown_mixed_triple (n : ℕ) (hn : 3 ≤ n) (S : Set (Fin 2 × Fin n))
    (hg : GeneralPosition (grid 2 n) S) (x y z : Fin 2 × Fin n)
    (hx : x∈S) (hy : y∈S) (hz : z∈S) (hxy : x≠y) (hrow : x.1=y.1) (hother : x.1≠z.1) : False := by
  have hyz : y≠z := by intro he; apply hother; exact hrow.trans (congrArg Prod.fst he)
  have hxz : x≠z := by intro he; exact hother (congrArg Prod.fst he)
  have hcols : x.2≠y.2 := by intro he; exact hxy (Prod.ext hrow he)
  have hxyD := crown_same_row_distance n hn x y hrow hxy
  have hother' : y.1≠z.1 := by simpa only [← hrow] using hother
  by_cases hzx : z.2=x.2
  · have hxzD := crown_opposite_distance n hn x z hother hzx.symm
    have hyzA : (grid 2 n).Adj y z := ⟨hother',by simpa only [hzx] using hcols.symm⟩
    have hyzD := SimpleGraph.edist_eq_one_iff_adj.mpr hyzA
    apply hg x hx y hy z hz hxy hyz hxz (by rw [hxzD]; simp)
    rw [hxzD,hxyD,hyzD]
    norm_num
  by_cases hzy : z.2=y.2
  · have hyzD := crown_opposite_distance n hn y z hother' hzy.symm
    have hxzA : (grid 2 n).Adj x z := ⟨hother,by simpa only [hzy] using hcols⟩
    have hxzD := SimpleGraph.edist_eq_one_iff_adj.mpr hxzA
    have hyxD := crown_same_row_distance n hn y x hrow.symm hxy.symm
    apply hg y hy x hx z hz hxy.symm hxz hyz (by rw [hyzD]; simp)
    rw [hyzD,hyxD,hxzD]
    norm_num
  · have hxzA : (grid 2 n).Adj x z := ⟨hother,Ne.symm hzx⟩
    have hzyA : (grid 2 n).Adj z y := ⟨hother'.symm,hzy⟩
    have hxzD := SimpleGraph.edist_eq_one_iff_adj.mpr hxzA
    have hzyD := SimpleGraph.edist_eq_one_iff_adj.mpr hzyA
    apply hg x hx z hz y hy hxz hyz.symm hxy (by rw [hxyD]; simp)
    rw [hxyD,hxzD,hzyD]
    norm_num

end TStarGraph

namespace TStarGraph

theorem crown_gp_row (n : ℕ) (hn : 3 ≤ n) (S : Finset (Fin 2 × Fin n))
    (hk : 3 ≤ S.card) (hg : GeneralPosition (grid 2 n) (S : Set (Fin 2 × Fin n))) :
    InRow (S : Set (Fin 2 × Fin n)) := by
  classical
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  by_cases hr : ∀ v∈S, v.1=x.1
  · exact ⟨x.1,hr⟩
  push_neg at hr
  obtain ⟨y,hy,hyx⟩ := hr
  have hxy : x≠y := by intro he; apply hyx; exact (congrArg Prod.fst he).symm
  have hns : ¬ S ⊆ {x,y} := by
    intro hs
    have hh := Finset.card_le_card hs
    have hp : ({x,y} : Finset (Fin 2 × Fin n)).card=2 := by simp [hxy]
    rw [hp] at hh
    omega
  simp only [Finset.subset_iff] at hns
  push_neg at hns
  obtain ⟨z,hz,hznot⟩ := hns
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hznot
  have hrows : z.1=x.1 ∨ z.1=y.1 := by omega
  exfalso
  rcases hrows with hzx | hzy
  · exact crown_mixed_triple n hn (S : Set (Fin 2 × Fin n)) hg x z y hx hz hy
      (Ne.symm hznot.1) hzx.symm hyx.symm
  · exact crown_mixed_triple n hn (S : Set (Fin 2 × Fin n)) hg y z x hy hz hx
      (Ne.symm hznot.2) hzy.symm hyx

theorem gpCoeff_two_large (n k : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    gpCoeff 2 n k = 2*n.choose k := by
  classical
  have he : gpCoeff 2 n k = Nat.card {S : Finset (Fin 2 × Fin n) // S.card=k ∧ InRow (S : Set (Fin 2 × Fin n))} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro S
    constructor
    · rintro ⟨hs,hg⟩
      exact ⟨hs,crown_gp_row n hn S (by omega) hg⟩
    · rintro ⟨hs,hr⟩
      exact ⟨hs,crown_row_gp n hn (S : Set (Fin 2 × Fin n)) hr⟩
  rw [he,count_rows 2 n k (by omega)]

end TStarGraph

namespace TStarGraph

theorem gpCoeff_eq (m n k : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) : gpCoeff m n k=TStarCoeff m n k := by
  by_cases hm1 : m=1
  · subst m
    rw [gpCoeff_of_all 1 n (fun S => one_all_gp n S)]
    simp [TStarCoeff]
  by_cases he : m=2 ∧ n=2
  · rcases he with ⟨rfl,rfl⟩
    rw [gpCoeff_of_all 2 2 (fun S => two_two_all_gp S)]
    simp [TStarCoeff]
  by_cases hk2 : k ≤ 2
  · rw [gpCoeff_small m n k hk2]
    interval_cases k
    · rw [TStarFormal.coeff_zero]; simp
    · rw [TStarFormal.coeff_one]; simp
    · rw [TStarFormal.coeff_two]
  by_cases hm2 : m=2
  · subst m
    rw [gpCoeff_two_large n k (by omega) (by omega),TStarFormal.two_tail n k (by omega) (by omega)]
  · rw [gpCoeff_large m n k (by omega) (by omega) (by omega),
      TStarFormal.coeff_large m n k (by omega) (by omega)]

end TStarGraph

theorem tstar_graph_classification (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    TStarFormal.Peak (TStarGraph.gpCoeff m n) ↔ ¬ TStarBad m n := by
  have he : TStarGraph.gpCoeff m n=TStarCoeff m n := by
    funext k
    exact TStarGraph.gpCoeff_eq m n k hm hmn
  rw [he]
  exact tstar_complete_classification m n hm hmn

namespace TStarGraph

def swapHom (m n : ℕ) : grid m n →g grid n m where
  toFun := Prod.swap
  map_rel' := by intro x y h; exact ⟨h.2,h.1⟩

theorem swap_distance_le (m n : ℕ) (x y : Fin m × Fin n) :
    (grid n m).edist x.swap y.swap ≤ (grid m n).edist x y := by
  change (grid n m).edist x.swap y.swap ≤ ⨅ p : (grid m n).Walk x y, (p.length : ℕ∞)
  apply le_iInf
  intro p
  have h := (p.map (swapHom m n)).edist_le
  change (grid n m).edist x.swap y.swap ≤
    ((p.map (swapHom m n)).length : ℕ∞) at h
  simpa only [SimpleGraph.Walk.length_map] using h

theorem swap_distance (m n : ℕ) (x y : Fin m × Fin n) :
    (grid n m).edist x.swap y.swap = (grid m n).edist x y := by
  apply le_antisymm (swap_distance_le m n x y)
  simpa using swap_distance_le n m x.swap y.swap

theorem gp_swap (m n : ℕ) (S : Finset (Fin m × Fin n))
    (hg : GeneralPosition (grid m n) (S : Set (Fin m × Fin n))) :
    GeneralPosition (grid n m) (S.image Prod.swap : Set (Fin n × Fin m)) := by
  intro x hx y hy z hz hxy hyz hxz hfin heq
  obtain ⟨u,hu,hux⟩ := Finset.mem_image.mp hx
  obtain ⟨v,hv,hvy⟩ := Finset.mem_image.mp hy
  obtain ⟨w,hw,hwz⟩ := Finset.mem_image.mp hz
  subst x
  subst y
  subst z
  rw [swap_distance] at hfin
  rw [swap_distance,swap_distance,swap_distance] at heq
  exact hg u hu v hv w hw (fun he => hxy (congrArg Prod.swap he))
    (fun he => hyz (congrArg Prod.swap he)) (fun he => hxz (congrArg Prod.swap he)) hfin heq


theorem gpCoeff_swap (m n k : ℕ) : gpCoeff m n k=gpCoeff n m k := by
  classical
  unfold gpCoeff
  apply Nat.card_congr
  exact
    { toFun := fun s => ⟨s.1.image Prod.swap,by rw [Finset.card_image_of_injective _ Prod.swap_injective,s.2.1],gp_swap m n s.1 s.2.2⟩
      invFun := fun s => ⟨s.1.image Prod.swap,by rw [Finset.card_image_of_injective _ Prod.swap_injective,s.2.1],gp_swap n m s.1 s.2.2⟩
      left_inv := by intro s; apply Subtype.ext; simp [Finset.image_image]
      right_inv := by intro s; apply Subtype.ext; simp [Finset.image_image] }

end TStarGraph

theorem tstar_graph_classification_all (r a : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) :
    TStarFormal.Peak (TStarGraph.gpCoeff r a) ↔ ¬ TStarBad (min r a) (max r a) := by
  by_cases h : r ≤ a
  · simpa only [min_eq_left h,max_eq_right h] using tstar_graph_classification r a hr h
  · have h' : a ≤ r := by omega
    have he : TStarGraph.gpCoeff r a=TStarGraph.gpCoeff a r := by
      funext k
      exact TStarGraph.gpCoeff_swap r a k
    rw [he]
    simpa only [min_eq_right h',max_eq_left h'] using tstar_graph_classification a r ha h'