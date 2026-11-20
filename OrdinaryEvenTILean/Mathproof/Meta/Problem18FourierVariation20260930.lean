import Mathproof.Meta.Problem18FourierCore20260930

/- Exact proof-body reuse from FiniteFieldOrthogonalUnitaryTI.lean.
These are existing distribution-transfer results, not new discoveries. -/
namespace Mathproof.Problem18FourierVariation20260930
open scoped BigOperators
open Classical
open Mathproof.Problem18FourierCore20260930

theorem finite_fourier_l1_bound
    {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    (∑ x, ‖f x‖) ^ 2 ≤ ∑ χ : AddChar G ℂ, ‖∑ x, f x * χ x‖ ^ 2 := by
  rw [finite_fourier_parseval]
  simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : G => (1 : ℝ)) (fun x => ‖f x‖))

theorem uniform_image_total
    {V G : Type*} [Fintype V] [Nonempty V] [Fintype G] (P : V → G) :
    ∑ y, uniformImageWeight P y = 1 := by
  have he := uniform_image_average P (fun _ => 1)
  simpa using he

theorem uniform_sum_fourier_energy_bound
    {V G : Type*} [Fintype V] [Nonempty V] [AddCommGroup G] [Fintype G]
    (P : V → G) (m : ℕ) :
    ((∑ y, ‖uniformImageWeight (fun x : Fin m → V => ∑ j, P (x j)) y -
      (Fintype.card G : ℂ)⁻¹‖) / 2) ^ 2 ≤
      (∑ χ : AddChar G ℂ, if χ = 1 then 0 else
        (‖(∑ x, χ (P x)) / (Fintype.card V : ℂ)‖ ^ 2)^m) / 4 := by
  classical
  let S := fun x : Fin m → V => ∑ j, P (x j)
  let f := fun y => uniformImageWeight S y - (Fintype.card G : ℂ)⁻¹
  have hz : ∑ y, f y = 0 := by simp [f, Finset.sum_sub_distrib, uniform_image_total]
  have he (χ : AddChar G ℂ) : ‖∑ y, f y * χ y‖ ^ 2 =
      if χ = 1 then 0 else
        (‖(∑ x, χ (P x)) / (Fintype.card V : ℂ)‖ ^ 2)^m := by
    by_cases hχ : χ = 1
    · simp [hχ, hz]
    · rw [if_neg hχ]
      have hh : (∑ y, f y * χ y) =
          (∑ x, χ (S x)) / (Fintype.card (Fin m → V) : ℂ) := by
        simp only [f, sub_mul]
        rw [Finset.sum_sub_distrib, uniform_image_average, ← Finset.mul_sum,
          AddChar.sum_eq_zero_of_ne_one hχ, mul_zero, sub_zero]
      rw [hh]
      simp only [S, independent_quadratic_character_sum, Fintype.card_fun,
        Fintype.card_fin, Nat.cast_pow]
      rw [← div_pow, norm_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul]
  have h := finite_fourier_l1_bound f
  simp_rw [he] at h
  change ((∑ y, ‖f y‖) / 2)^2 ≤ _
  nlinarith

theorem finite_event_variation_bound
    {G : Type*} [Fintype G] (f : G → ℂ) (hf : ∑ y, f y = 0)
    (A : Finset G) :
    ‖∑ y ∈ A, f y‖ ≤ (∑ y, ‖f y‖) / 2 := by
  have he : (∑ y ∈ Aᶜ, f y) = -(∑ y ∈ A, f y) := by
    have hs := Finset.sum_compl_add_sum A f
    rw [hf] at hs
    exact eq_neg_of_add_eq_zero_left hs
  have hA := norm_sum_le A f
  have hC := norm_sum_le Aᶜ f
  rw [he, norm_neg] at hC
  have hs := Finset.sum_compl_add_sum A (fun y => ‖f y‖)
  linarith

theorem uniform_image_event_variation_bound
    {V G : Type*} [Fintype V] [Nonempty V] [Fintype G] [Nonempty G]
    (P : V → G) (A : Finset G) :
    ‖((Finset.univ.filter (fun x => P x ∈ A)).card : ℂ) / Fintype.card V -
      (A.card : ℂ) / Fintype.card G‖ ≤
      (∑ y, ‖uniformImageWeight P y - (Fintype.card G : ℂ)⁻¹‖) / 2 := by
  have h := finite_event_variation_bound
    (fun y => uniformImageWeight P y - (Fintype.card G : ℂ)⁻¹)
    (by simp [Finset.sum_sub_distrib, uniform_image_total]) A
  simpa [Finset.sum_sub_distrib, uniform_image_event_mass,
    nsmul_eq_mul, div_eq_mul_inv] using h

theorem uniform_image_event_probability_bound
    {V G : Type*} [Fintype V] [Nonempty V] [Fintype G] [Nonempty G]
    (P : V → G) (A : Finset G) :
    ((Finset.univ.filter (fun x => P x ∈ A)).card : ℝ) / Fintype.card V ≤
      (A.card : ℝ) / Fintype.card G +
        (∑ y, ‖uniformImageWeight P y - (Fintype.card G : ℂ)⁻¹‖) / 2 := by
  have he := uniform_image_event_variation_bound P A
  have hc :
      ((((Finset.univ.filter (fun x => P x ∈ A)).card : ℝ) / Fintype.card V -
        (A.card : ℝ) / Fintype.card G : ℝ) : ℂ) =
      ((Finset.univ.filter (fun x => P x ∈ A)).card : ℂ) / Fintype.card V -
        (A.card : ℂ) / Fintype.card G := by push_cast; rfl
  rw [← hc, Complex.norm_real, Real.norm_eq_abs] at he
  have hl := le_abs_self
    (((Finset.univ.filter (fun x => P x ∈ A)).card : ℝ) / Fintype.card V -
      (A.card : ℝ) / Fintype.card G)
  linarith

end Mathproof.Problem18FourierVariation20260930
