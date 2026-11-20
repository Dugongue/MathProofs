import EvenReciprocalLaw
import EvenPrimaryFourier

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Classical
open EvenTI.Primary Mathproof.Problem18FourierCore20260930

noncomputable section

abbrev marginalError {A Y : Type*} [Fintype A] [Fintype Y] (f : A → Y) : ℝ :=
  ∑ y, |weight f y - (Fintype.card Y : ℝ)⁻¹|

theorem marginalError_equiv {A Y Z : Type*} [Fintype A] [Fintype Y] [Fintype Z]
    (e : Y ≃ Z) (f : A → Y) : marginalError (e ∘ f) = marginalError f := by
  unfold marginalError
  rw [← Equiv.sum_comp e]
  have cardEq : Fintype.card Z = Fintype.card Y := (Fintype.card_congr e).symm
  simp [weight, Function.comp_apply, cardEq]

private theorem mean_const' {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    mean (fun _ : A => c) = c := by
  have h : (Fintype.card A : ℝ) ≠ 0 := by positivity
  simp [mean, mul_comm, h]

private theorem mean_sub' {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a - g a) = mean f - mean g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

private theorem abs_mean_le {A : Type*} [Fintype A] (f : A → ℝ) :
    |mean f| ≤ mean (fun a => |f a|) := by
  rw [mean, abs_div, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card A : ℝ))]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)

theorem marginalError_le_two {A Y : Type*} [Fintype A] [Nonempty A]
    [Fintype Y] (f : A → Y) : marginalError f ≤ 2 := by
  haveI : Nonempty Y := Nonempty.map f inferInstance
  unfold marginalError
  have h1 := uniform_image_average f (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id, mul_one, uniformImageWeight_eq_ofReal_weight] at h1
  have hA : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_self hA] at h1
  have hm : ∑ y, weight f y = 1 := by
    have hr := congrArg Complex.re h1
    simpa [Complex.re_sum] using hr
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ∑ y, (weight f y + (Fintype.card Y : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro y _
      apply abs_sub_le_iff.mpr
      constructor
      · linarith [inv_nonneg.mpr (show 0 ≤ (Fintype.card Y : ℝ) by positivity)]
      · have hw : 0 ≤ weight f y := by
          rw [weight, event_eq_card]
          positivity
        linarith
    _ = 2 := by simp [Finset.sum_add_distrib, hm, hY, one_add_one_eq_two]

/-- Averaging uniform shear permutations transfers the one-baseline
marginal bound. Each exceptional baseline contributes at most two in L1. -/
theorem marginalError_of_good_baselines
    {A X Y : Type*} [Fintype A] [Nonempty A] [Fintype X] [Nonempty X] [Fintype Y]
    (e : X → A ≃ A) (f : A → Y) (good : A → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hgood : ∀ a, good a → marginalError (fun x => f (e x a)) ≤ p) :
    marginalError f ≤ p + 2 * event (fun a => ¬ good a) := by
  have hweight (y : Y) :
      weight f y = mean (fun a => weight (fun x => f (e x a)) y) := by
    change mean (fun a => if f a = y then 1 else 0) =
      mean (fun a => mean (fun x => if f (e x a) = y then 1 else 0))
    exact (uniform_average_equiv e (fun a => if f a = y then 1 else 0)).symm
  let k := (Fintype.card Y : ℝ)⁻¹
  have hpoint (y : Y) : |weight f y - k| ≤
      mean (fun a => |weight (fun x => f (e x a)) y - k|) := by
    rw [hweight y, ← mean_const' (A := A) k, ← mean_sub']
    simpa only [mean_const'] using
      (abs_mean_le (fun a => weight (fun x => f (e x a)) y - k))
  calc
    marginalError f ≤ ∑ y, mean (fun a => |weight (fun x => f (e x a)) y - k|) :=
      Finset.sum_le_sum fun y _ => hpoint y
    _ = mean (fun a => marginalError (fun x => f (e x a))) := by
      rw [mean_sum]
    _ ≤ mean (fun a => p + 2 * (if ¬ good a then 1 else 0)) := by
      apply mean_mono
      intro a
      by_cases h : good a
      · simpa [h] using hgood a h
      · simpa [h] using (marginalError_le_two (fun x => f (e x a))).trans
          (le_add_of_nonneg_left hp)
    _ = p + 2 * event (fun a => ¬ good a) := by
      simp only [mean, event, Finset.sum_add_distrib, ← Finset.mul_sum, add_div,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm (Fintype.card A : ℝ) p]
      have hA : (Fintype.card A : ℝ) ≠ 0 := by positivity
      simp [hA, mul_div_assoc]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : good a <;> simp [h]

#print axioms marginalError_equiv
#print axioms marginalError_of_good_baselines

end
end Mathproof.EvenTI.Reciprocal.Coverage
