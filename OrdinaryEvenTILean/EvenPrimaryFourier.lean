import EvenPrimaryMarginal
import Mathproof.Meta.Problem18FourierCore20260930
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators Classical

namespace EvenTI.Primary

open Mathproof.Problem18FourierCore20260930
noncomputable section

theorem uniformImageWeight_eq_ofReal_weight {Ω A : Type*} [Fintype Ω]
    (a : Ω → A) (y : A) :
    uniformImageWeight a y = (weight a y : ℂ) := by
  classical
  rw [weight, event_eq_card, uniformImageWeight]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  push_cast <;> rfl

theorem weight_L1_eq_fourier {Ω A : Type*} [Fintype Ω] [Fintype A] (a : Ω → A) :
    (∑ y, |weight a y - (Fintype.card A:ℝ)⁻¹|) =
      ∑ y, ‖uniformImageWeight a y - (Fintype.card A:ℂ)⁻¹‖ := by
  apply Finset.sum_congr rfl
  intro y _
  rw [uniformImageWeight_eq_ofReal_weight, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem weight_L1_le_of_fourier_sq {Ω A : Type*} [Fintype Ω] [Fintype A]
    (a : Ω → A) (B : ℝ)
    (h : ((∑ y, ‖uniformImageWeight a y - (Fintype.card A:ℂ)⁻¹‖) / 2)^2 ≤ B) :
    (∑ y, |weight a y - (Fintype.card A:ℝ)⁻¹|) ≤ 2 * Real.sqrt B := by
  rw [weight_L1_eq_fourier]
  have hB : 0 ≤ B := (sq_nonneg _).trans h
  have hs := Real.sq_sqrt hB
  have hn : 0 ≤ ∑ y, ‖uniformImageWeight a y - (Fintype.card A:ℂ)⁻¹‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have he := (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg B)).mp (h.trans_eq hs.symm)
  linarith

#print axioms weight_L1_le_of_fourier_sq

end
end EvenTI.Primary
