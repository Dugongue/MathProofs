import EvenP3RecipCoverage
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Mathproof.EvenTI.OrderFour

open Filter
open Mathproof.EvenTI.Reciprocal.Coverage Mathproof.EvenTI.Reciprocal.Four
open scoped Topology

noncomputable section

private theorem tendsto_poly_div_geometric (q : ℝ) (hq : 1 < q) (d : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^d / q^n) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (d : ℝ) (Real.log q) (Real.log_pos hq)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr (fun n => ?_)
  simp only [Function.comp_apply, Real.rpow_natCast, neg_mul, Real.exp_neg]
  rw [mul_comm (Real.log q), Real.exp_nat_mul, Real.exp_log (by linarith), div_eq_mul_inv]

theorem tendsto_nat_div_const_atTop (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => n / m) atTop atTop := by
  refine tendsto_atTop_atTop.mpr (fun b => ⟨b*m, fun n hn => ?_⟩)
  exact (Nat.le_div_iff_mul_le hm).mpr hn

private theorem le_double_mul_quotient (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    n ≤ 2 * m * (n / m) := by
  have hq : 1 ≤ n / m := (Nat.le_div_iff_mul_le hm).mpr (by simp [hn])
  have hx : m ≤ m * (n / m) := by
    simpa using Nat.mul_le_mul_left m hq
  have hr := Nat.mod_lt n hm
  have hd := Nat.mod_add_div n m
  rw [two_mul, Nat.add_mul]
  omega

private theorem tendsto_sq_div_geometric_quotient (q : ℝ) (hq : 1 < q)
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 / q^(n/m)) atTop (𝓝 0) := by
  have h := ((tendsto_poly_div_geometric q hq 2).comp
    (tendsto_nat_div_const_atTop m hm)).const_mul ((2 * (m : ℝ))^2)
  simp only [mul_zero, Function.comp_apply] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall (fun n => by positivity)) ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hcast : (n : ℝ) ≤ 2 * (m : ℝ) * ((n / m : ℕ) : ℝ) := by
    exact_mod_cast le_double_mul_quotient m n hm hn
  calc
    (n : ℝ)^2 / q^(n/m) ≤ (2 * (m : ℝ) * ((n/m : ℕ) : ℝ))^2 / q^(n/m) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcast _) (by positivity)
    _ = (2 * (m : ℝ))^2 * (((n/m : ℕ) : ℝ)^2 / q^(n/m)) := by rw [mul_pow, mul_div_assoc]

private theorem tendsto_scaled_low_shear (q : ℝ) (hq : 1 < q) :
    Tendsto (fun n : ℕ => (n : ℝ)^4 *
      ((↑(highCutoff n + 1) : ℝ) * (q^(9*n-31))⁻¹)) atTop (𝓝 0) := by
  have h := (tendsto_poly_div_geometric q hq 6).const_mul (2 : ℝ)
  simp only [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall (fun n => by positivity)) ?_
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
  have hnn : 1 ≤ n^2 := (one_le_pow₀ (by omega : 1 ≤ n))
  have hcut : highCutoff n + 1 ≤ 2*n^2 := by
    have hc : highCutoff n ≤ n^2 := Nat.div_le_self _ _
    omega
  have hc : (↑(highCutoff n+1) : ℝ) ≤ 2*(n : ℝ)^2 := by exact_mod_cast hcut
  have he : (q^(9*n-31))⁻¹ ≤ (q^n)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le (by omega))
  calc
    _ ≤ (n : ℝ)^4 * ((2*(n : ℝ)^2) * (q^n)⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hc he (by positivity) (by positivity)) (by positivity)
    _ = 2 * ((n : ℝ)^6 / q^n) := by ring

private theorem tendsto_scaled_high_shear (q : ℝ) (hq : 1 < q) :
    Tendsto (fun n : ℕ => (n : ℝ)^4 *
      (q^(n^2) * (q^(4*n^2))⁻¹)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_poly_div_geometric q hq 4) (Eventually.of_forall (fun n => by positivity)) ?_
  filter_upwards with n
  have hsq : n ≤ n^2 := by nlinarith [Nat.zero_le n]
  have he : n ≤ 3*n^2 := by omega
  have hpower : q^(n^2) * (q^(4*n^2))⁻¹ = (q^(3*n^2))⁻¹ := by
    rw [show 4*n^2 = n^2 + 3*n^2 by ring, pow_add, mul_inv_rev]
    field_simp
  rw [hpower, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le he)) (by positivity)

theorem tendsto_scaled_squareReciprocalError (K : Type*) [Fintype K]
    (hq : 1 < (Fintype.card K : ℝ)) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 * squareReciprocalError K n) atTop (𝓝 0) := by
  let q := (Fintype.card K : ℝ)
  let X (n : ℕ) := (↑(highCutoff n+1) : ℝ) * (q^(9*n-31))⁻¹ +
    q^(n^2) * (q^(4*n^2))⁻¹
  have hparts := (tendsto_scaled_low_shear q hq).add (tendsto_scaled_high_shear q hq)
  simp only [← mul_add, add_zero] at hparts
  change Tendsto (fun n : ℕ => (n : ℝ)^4 * X n) atTop (𝓝 0) at hparts
  have hroot : Tendsto (fun n : ℕ => (n : ℝ)^2 * Real.sqrt (X n)) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hparts
    rw [Real.sqrt_zero] at h
    refine h.congr (fun n => ?_)
    change Real.sqrt ((n : ℝ)^4 * X n) = _
    rw [Real.sqrt_mul (by positivity), show (n : ℝ)^4 = ((n : ℝ)^2)^2 by ring,
      Real.sqrt_sq (by positivity)]
  have hdecay := ((tendsto_poly_div_geometric q hq 2).const_mul (8 : ℝ)).add
    ((tendsto_sq_div_geometric_quotient q hq 16000000 (by decide)).const_mul (16 : ℝ))
  have hout := hroot.add (hdecay.const_mul (2 : ℝ))
  simp only [mul_zero, add_zero] at hout
  refine hout.congr (fun n => ?_)
  simp only [squareReciprocalError, slicedShearError, Fintype.card_fin, highExponent]
  ring

#print axioms tendsto_nat_div_const_atTop
#print axioms tendsto_scaled_squareReciprocalError

end
end Mathproof.EvenTI.OrderFour
