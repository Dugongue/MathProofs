import FourierTransfer

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical
open Mathproof.Problem18FourierCore20260930 Mathproof.Problem17FourierTransfer

/-- A different polar-rank bound may be used for each Fourier label. -/
theorem variation_le_of_label_ranks
    {V K G : Type*} [AddCommGroup V] [Fintype V] [Field K] [Fintype K] [Module K V]
    [AddCommGroup G] [Fintype G] (P : V → G) (r : AddChar G ℂ → ℕ)
    (h : ∀ χ : AddChar G ℂ, χ ≠ 1 →
      ∃ (ψ : AddChar K ℂ) (Q : V → K) (B : V →ₗ[K] Module.Dual K V),
        ψ ≠ 1 ∧ (∀ x, χ (P x) = ψ (Q x)) ∧
        (∀ x y, Q (x + y) = Q x + Q y + B y x) ∧ r χ ≤ Module.finrank K B.range) :
    ((∑ y, ‖uniformImageWeight P y - (Fintype.card G : ℂ)⁻¹‖) / 2)^2 ≤
      (∑ χ : AddChar G ℂ, if χ = 1 then 0 else ((Fintype.card K : ℝ) ^ r χ)⁻¹) / 4 := by
  classical
  refine (single_image_fourier_energy P).trans ?_
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro χ _
  by_cases hχ : χ = 1
  · simp [hχ]
  · simp only [if_neg hχ]
    obtain ⟨ψ, Q, B, hψ, hχQ, hQ, hr⟩ := h χ hχ
    simp_rw [hχQ]
    refine (quadratic_character_rank_bound ψ hψ Q B hQ).trans ?_
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_right₀ _ hr
    exact_mod_cast Fintype.card_pos (α := K)

#print axioms variation_le_of_label_ranks

end Mathproof.EvenTI.OrderFour
