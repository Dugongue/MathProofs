import Mathproof.Meta.Problem18FourierVariation20260930

namespace Mathproof.Problem17FourierTransfer
open scoped BigOperators
open Classical
open Mathproof.Problem18FourierCore20260930 Mathproof.Problem18FourierVariation20260930

theorem single_image_fourier_energy
    {V G : Type*} [Fintype V] [Nonempty V] [AddCommGroup G] [Fintype G]
    (P : V → G) :
    ((∑ y, ‖uniformImageWeight P y - (Fintype.card G : ℂ)⁻¹‖) / 2)^2 ≤
    (∑ χ : AddChar G ℂ, if χ = 1 then 0 else
      ‖(∑ x, χ (P x)) / (Fintype.card V : ℂ)‖^2) / 4 := by
  classical
  let f := fun y => uniformImageWeight P y - (Fintype.card G : ℂ)⁻¹
  have hz : ∑ y, f y = 0 := by simp [f, Finset.sum_sub_distrib, uniform_image_total]
  have he (χ : AddChar G ℂ) : ‖∑ y, f y * χ y‖^2 = if χ = 1 then 0 else
      ‖(∑ x, χ (P x)) / (Fintype.card V : ℂ)‖^2 := by
    by_cases hχ : χ = 1
    · simp [hχ, hz]
    · rw [if_neg hχ]
      have hh : (∑ y, f y * χ y) = (∑ x, χ (P x)) / (Fintype.card V : ℂ) := by
        simp only [f, sub_mul]
        rw [Finset.sum_sub_distrib, uniform_image_average, ← Finset.mul_sum,
          AddChar.sum_eq_zero_of_ne_one hχ, mul_zero, sub_zero]
      rw [hh]
  have h := finite_fourier_l1_bound f
  simp_rw [he] at h
  change ((∑ y, ‖f y‖) / 2)^2 ≤ _
  nlinarith

/-- The upper bound holds even when the quadratic form is nonzero on its
polar radical, as can occur in characteristic two. -/
theorem quadratic_character_mean_norm_sq_le
    {G F : Type*} [AddCommGroup G] [Fintype G] [CommRing F]
    (hp : 0 < ringChar F) (ψ : AddChar F ℂ) (Q : G → F) (B : G → G → F)
    (β : G → AddChar G ℂ)
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + B x h)
    (hβ : ∀ h x, β h x = ψ (B x h)) :
    ‖(∑ x, ψ (Q x)) / (Fintype.card G : ℂ)‖ ^ 2 ≤
      (Finset.univ.filter (fun h => β h = 1)).card / (Fintype.card G : ℝ) := by
  classical
  let R := Finset.univ.filter (fun h => β h = 1)
  let S := ∑ x, ψ (Q x)
  have hn (a : F) : ψ (-a) = star (ψ a) := by
    simpa [AddChar.inv_apply] using (AddChar.starComp_apply hp (φ := ψ) a).symm
  have hunit (a : F) : ‖ψ a‖ = 1 := by
    have h : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel,
      AddChar.map_zero_eq_one]
    rw [hn] at h
    change ψ a * (starRingEnd ℂ) (ψ a) = 1 at h
    rw [Complex.mul_conj] at h
    have he := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re, Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg (ψ a)]
  have hs : ∑ x, ψ (-Q x) = star S := by
    simp_rw [hn]
    exact (map_sum (starRingEnd ℂ) (fun x => ψ (Q x)) Finset.univ).symm
  have hi (h : G) : ∑ x, ψ (B x h) =
      if β h = 1 then (Fintype.card G : ℂ) else 0 := by
    simp_rw [← hβ]
    by_cases hh : β h = 1
    · simp [hh]
    · rw [AddChar.sum_eq_zero_of_ne_one hh]
      simp [hh]
  have hpolar := quadratic_character_polarization ψ Q B hQ
  rw [hs] at hpolar
  simp_rw [hi, mul_ite, mul_zero] at hpolar
  rw [← Finset.sum_filter, ← Finset.sum_mul] at hpolar
  change S * star S = (∑ h ∈ R, ψ (Q h)) * (Fintype.card G : ℂ) at hpolar
  have hnorm : ‖S‖ ^ 2 = ‖∑ h ∈ R, ψ (Q h)‖ * (Fintype.card G : ℝ) := by
    simpa [norm_mul, pow_two] using congrArg (fun z : ℂ => ‖z‖) hpolar
  have hR : ‖∑ h ∈ R, ψ (Q h)‖ ≤ (R.card : ℝ) := by
    simpa [hunit] using norm_sum_le R (fun h => ψ (Q h))
  have hc : 0 < (Fintype.card G : ℝ) := by positivity
  rw [norm_div, div_pow, Complex.norm_natCast]
  change ‖S‖ ^ 2 / (Fintype.card G : ℝ)^2 ≤ (R.card : ℝ) / Fintype.card G
  rw [hnorm]
  calc
    _ ≤ (R.card : ℝ) * Fintype.card G / (Fintype.card G : ℝ)^2 := by gcongr
    _ = _ := by field_simp

theorem quadratic_character_rank_bound
    {V F : Type*} [AddCommGroup V] [Fintype V] [Field F] [Fintype F] [Module F V]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (Q : V → F) (B : V →ₗ[F] Module.Dual F V)
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + B h x) :
    ‖(∑ x, ψ (Q x)) / (Fintype.card V : ℂ)‖ ^ 2 ≤
      ((Fintype.card F : ℝ) ^ Module.finrank F B.range)⁻¹ := by
  classical
  let β (h : V) : AddChar V ℂ := ψ.compAddMonoidHom (B h).toAddMonoidHom
  have hb (h : V) : β h = 1 ↔ B h = 0 := by
    constructor
    · intro he
      apply (character_detects_linear_map ψ hψ (B h)).mp
      intro x
      exact congrArg (fun χ : AddChar V ℂ => χ x) he
    · intro he
      ext x
      simp [β, he, AddChar.map_zero_eq_one]
  have hc : 0 < ringChar F := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)
  have he := quadratic_character_mean_norm_sq_le hc ψ Q
    (fun x h => B h x) β hQ (fun _ _ => rfl)
  have hk : (Finset.univ.filter (fun h => B h = 0)).card =
      Fintype.card (LinearMap.ker B) := by
    symm
    exact Fintype.card_of_subtype _ (by intro x; simp)
  simp only [hb] at he
  rwa [hk, linear_kernel_fraction B] at he

theorem image_variation_of_polar_rank
    {V F G : Type*} [AddCommGroup V] [Fintype V] [Field F] [Fintype F] [Module F V]
    [AddCommGroup G] [Fintype G]
    (P : V → G) (r : ℕ)
    (h : ∀ χ : AddChar G ℂ, χ ≠ 1 →
      ∃ (ψ : AddChar F ℂ) (Q : V → F) (B : V →ₗ[F] Module.Dual F V),
        ψ ≠ 1 ∧ (∀ x, χ (P x) = ψ (Q x)) ∧
        (∀ x y, Q (x + y) = Q x + Q y + B y x) ∧ r ≤ Module.finrank F B.range) :
    ((∑ y, ‖uniformImageWeight P y - (Fintype.card G : ℂ)⁻¹‖) / 2)^2 ≤
      (Fintype.card G : ℝ) * ((Fintype.card F : ℝ) ^ r)⁻¹ / 4 := by
  classical
  refine (single_image_fourier_energy P).trans ?_
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ _ : AddChar G ℂ, ((Fintype.card F : ℝ) ^ r)⁻¹ := by
      apply Finset.sum_le_sum
      intro χ _
      split_ifs with hχ
      · positivity
      · obtain ⟨ψ, Q, B, hψ, hχQ, hQ, hr⟩ := h χ hχ
        simp_rw [hχQ]
        refine (quadratic_character_rank_bound ψ hψ Q B hQ).trans ?_
        apply inv_anti₀ (by positivity)
        apply pow_le_pow_right₀ _ hr
        exact_mod_cast Fintype.card_pos (α := F)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, AddChar.card_eq]

end Mathproof.Problem17FourierTransfer

#print axioms Mathproof.Problem17FourierTransfer.single_image_fourier_energy
#print axioms Mathproof.Problem17FourierTransfer.quadratic_character_mean_norm_sq_le
#print axioms Mathproof.Problem17FourierTransfer.quadratic_character_rank_bound
#print axioms Mathproof.Problem17FourierTransfer.image_variation_of_polar_rank

