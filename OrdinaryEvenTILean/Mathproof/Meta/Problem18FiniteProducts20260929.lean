import Mathlib.Tactic

/-! Uniform elementary product bounds for the normalized orders of general
linear groups over finite fields. These estimates are sufficient arithmetic
inputs for a proposed nondegenerate-image density argument; no classical-group
order or orbit formula is assumed here. -/

namespace Mathproof.Problem18FiniteProducts20260929

open Finset

noncomputable def glFactor (q : ℝ) (m : ℕ) : ℝ :=
  ∏ i ∈ range m, (1 - (q⁻¹) ^ (i + 1))

private theorem product_half_aux (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 3) (m : ℕ) :
    (1 + t ^ m) / 2 ≤ ∏ i ∈ range m, (1 - t ^ (i + 1)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have ht1 : t ≤ 1 := by linarith
    have hx0 : 0 ≤ t ^ m := pow_nonneg ht0 _
    have hx1 : t ^ m ≤ 1 := pow_le_one₀ ht0 ht1
    have hy1 : t ^ (m + 1) ≤ 1 := pow_le_one₀ ht0 ht1
    have hfactor : 0 ≤ 1 - 2 * t - t * t ^ m := by
      have htx : t * t ^ m ≤ t := by
        have h := mul_nonneg ht0 (show 0 ≤ 1 - t ^ m by linarith)
        nlinarith
      linarith
    have haux : 0 ≤ t ^ m * (1 - 2 * t - t * t ^ m) :=
      mul_nonneg hx0 hfactor
    have hstep : (1 + t ^ (m + 1)) / 2 ≤
        (1 + t ^ m) / 2 * (1 - t ^ (m + 1)) := by
      rw [pow_succ]
      nlinarith [haux]
    calc
      _ ≤ (1 + t ^ m) / 2 * (1 - t ^ (m + 1)) := hstep
      _ ≤ (∏ i ∈ range m, (1 - t ^ (i + 1))) *
          (1 - t ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right ih (by linarith)
      _ = _ := by simp [prod_range_succ]

private theorem product_twoThirds_aux
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (m : ℕ) :
    (2 + t ^ m) / 3 ≤ ∏ i ∈ range m, (1 - t ^ (i + 1)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have ht1 : t ≤ 1 := by linarith
    have hx0 : 0 ≤ t ^ m := pow_nonneg ht0 _
    have hx1 : t ^ m ≤ 1 := pow_le_one₀ ht0 ht1
    have hy1 : t ^ (m + 1) ≤ 1 := pow_le_one₀ ht0 ht1
    have hfactor : 0 ≤ 1 - 3 * t - t * t ^ m := by
      have htx : t * t ^ m ≤ t := by
        have h := mul_nonneg ht0 (show 0 ≤ 1 - t ^ m by linarith)
        nlinarith
      linarith
    have haux : 0 ≤ t ^ m * (1 - 3 * t - t * t ^ m) :=
      mul_nonneg hx0 hfactor
    have hstep : (2 + t ^ (m + 1)) / 3 ≤
        (2 + t ^ m) / 3 * (1 - t ^ (m + 1)) := by
      rw [pow_succ]
      nlinarith [haux]
    calc
      _ ≤ (2 + t ^ m) / 3 * (1 - t ^ (m + 1)) := hstep
      _ ≤ (∏ i ∈ range m, (1 - t ^ (i + 1))) *
          (1 - t ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right ih (by linarith)
      _ = _ := by simp [prod_range_succ]

/-- A field size at least three gives a uniform lower bound on every finite
general-linear normalization product. -/
theorem glFactor_lower_half (q : ℝ) (hq : 3 ≤ q) (m : ℕ) :
    1 / 2 ≤ glFactor q m := by
  have hq0 : q ≠ 0 := by linarith
  have ht0 : 0 ≤ q⁻¹ := by positivity
  have ht : q⁻¹ ≤ 1 / 3 := by
    have hmul : 0 ≤ (q - 3) * q⁻¹ := mul_nonneg (by linarith) ht0
    have hcancel : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0
    nlinarith
  have hp := product_half_aux q⁻¹ ht0 ht m
  have hpow : 0 ≤ (q⁻¹) ^ m := pow_nonneg ht0 _
  unfold glFactor
  linarith

/-- The same product is at least two thirds once the field size is four. -/
theorem glFactor_lower_twoThirds (q : ℝ) (hq : 4 ≤ q) (m : ℕ) :
    2 / 3 ≤ glFactor q m := by
  have hq0 : q ≠ 0 := by linarith
  have ht0 : 0 ≤ q⁻¹ := by positivity
  have ht : q⁻¹ ≤ 1 / 4 := by
    have hmul : 0 ≤ (q - 4) * q⁻¹ := mul_nonneg (by linarith) ht0
    have hcancel : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0
    nlinarith
  have hp := product_twoThirds_aux q⁻¹ ht0 ht m
  have hpow : 0 ≤ (q⁻¹) ^ m := pow_nonneg ht0 _
  unfold glFactor
  linarith

/-- In the unitary case the matrix entries lie in a field of size q²,
where q≥2. -/
theorem glFactor_square_lower_twoThirds (q : ℝ) (hq : 2 ≤ q) (m : ℕ) :
    2 / 3 ≤ glFactor (q ^ 2) m := by
  apply glFactor_lower_twoThirds
  nlinarith [sq_nonneg (q - 2)]

private theorem product_quarter_succ_aux
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (n : ℕ) :
    1 / 4 + t ^ (n + 2) ≤
      ∏ i ∈ range (n + 1), (1 - t ^ (i + 1)) := by
  induction n with
  | zero =>
    simp only [zero_add, pow_succ, pow_zero, one_mul, prod_range_succ,
      prod_range_zero, one_mul]
    have hsq : t ^ 2 ≤ t / 2 := by
      have h := mul_nonneg ht0 (show 0 ≤ 1 / 2 - t by linarith)
      nlinarith
    nlinarith
  | succ n ih =>
    have ht1 : t ≤ 1 := by linarith
    have hx0 : 0 ≤ t ^ (n + 2) := pow_nonneg ht0 _
    have hx1 : t ^ (n + 2) ≤ 1 / 4 := by
      calc
        t ^ (n + 2) = t ^ n * t ^ 2 := by rw [pow_add]
        _ ≤ 1 * t ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ ht0 ht1) (pow_nonneg ht0 _)
        _ ≤ 1 / 4 := by
          have h := mul_nonneg (show 0 ≤ 1 / 2 - t by linarith)
            (show 0 ≤ 1 / 2 + t by linarith)
          nlinarith
    have hfactor : 0 ≤ 1 - t ^ (n + 2) := by linarith
    have haux : 0 ≤ t ^ (n + 2) *
        (3 / 4 - t - t ^ (n + 2)) := by
      apply mul_nonneg hx0
      linarith
    have hstep : 1 / 4 + t ^ (n + 3) ≤
        (1 / 4 + t ^ (n + 2)) * (1 - t ^ (n + 2)) := by
      have hpow : t ^ (n + 3) = t ^ (n + 2) * t := by
        rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
      rw [hpow]
      nlinarith [haux]
    calc
      _ ≤ (1 / 4 + t ^ (n + 2)) * (1 - t ^ (n + 2)) := hstep
      _ ≤ (∏ i ∈ range (n + 1), (1 - t ^ (i + 1))) *
          (1 - t ^ (n + 2)) :=
        mul_le_mul_of_nonneg_right ih hfactor
      _ = _ := by simp [prod_range_succ, add_assoc]

/-- Every field size at least two gives a uniform one-quarter lower bound
for the normalized full-rank square-matrix product. -/
theorem glFactor_lower_quarter (q : ℝ) (hq : 2 ≤ q) (m : ℕ) :
    1 / 4 ≤ glFactor q m := by
  cases m with
  | zero =>
    norm_num [glFactor]
  | succ n =>
    have hq0 : q ≠ 0 := by linarith
    have ht0 : 0 ≤ q⁻¹ := by positivity
    have ht : q⁻¹ ≤ 1 / 2 := by
      have hmul : 0 ≤ (q - 2) * q⁻¹ := mul_nonneg (by linarith) ht0
      have hcancel : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0
      nlinarith
    have hp := product_quarter_succ_aux q⁻¹ ht0 ht n
    have hpow : 0 ≤ (q⁻¹) ^ (n + 2) := pow_nonneg ht0 _
    unfold glFactor
    linarith

end Mathproof.Problem18FiniteProducts20260929
