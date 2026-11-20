import EvenP3FourierBudget
import EvenReciprocalFourier

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical
open Mathproof.Problem18FourierCore20260930 Mathproof.Problem17TraceCharacters
open Mathproof.EvenTI.Reciprocal

noncomputable section

variable {K : Type*} [Field K] [Fintype K]

/-- Once a nontrivial field character is fixed, each linear label is counted
exactly once in the Fourier sum. -/
def linearCharacterEquiv {W : Type*} [AddCommGroup W] [Module K W]
    [Fintype W] (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) :
    Module.Dual K W ≃ AddChar W ℂ := by
  let g (l : Module.Dual K W) : AddChar W ℂ := ψ.compAddMonoidHom l.toAddMonoidHom
  refine Equiv.ofBijective g ⟨?_, ?_⟩
  · intro l m h
    apply sub_eq_zero.mp
    apply (character_detects_linear_map ψ hψ (l - m)).mp
    intro v
    have hv : ψ (l v) = ψ (m v) := congrArg (fun f : AddChar W ℂ => f v) h
    change ψ (l v - m v) = 1
    rw [AddChar.map_sub_eq_div, hv, div_self (ψ.val_isUnit (m v)).ne_zero]
  · intro χ
    obtain ⟨l, hl⟩ := every_character_is_linear ψ hψ χ
    refine ⟨l, ?_⟩
    ext v
    exact (hl v).symm

theorem centeredSquare_variation_sq_of_linear_label_ranks
    {V R G : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    [Ring R] [Algebra K R] [AddCommGroup G] [Module K G]
    (S : Submodule K G) [Fintype S] [Fintype (Module.Dual K S)]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (C : R) (D : V →ₗ[K] R) (l : R →ₗ[K] G)
    (hS : ∀ x, centeredSquare C D l x ∈ S) (r : Module.Dual K S → ℕ)
    (hr : ∀ m : Module.Dual K S, m ≠ 0 → ∃ c : Module.Dual K G,
      c.comp S.subtype = m ∧ r m ≤ Module.finrank K (squarePolar D (c.comp l)).range) :
    ((∑ y, ‖uniformImageWeight (centeredSquareIn S C D l hS) y -
      (Fintype.card S : ℂ)⁻¹‖) / 2)^2 ≤
      (∑ m : Module.Dual K S, if m = 0 then 0 else ((Fintype.card K : ℝ)^r m)⁻¹) / 4 := by
  let e : Module.Dual K S ≃ AddChar S ℂ := linearCharacterEquiv ψ hψ
  have he (m : Module.Dual K S) (v : S) : e m v = ψ (m v) := rfl
  have h0 : e 0 = 1 := by ext v; simp [he]
  refine (variation_le_of_label_ranks (K := K) (centeredSquareIn S C D l hS)
    (r ∘ e.symm) ?_).trans_eq ?_
  · intro χ hχ
    let m := e.symm χ
    have hm : m ≠ 0 := by
      intro h
      apply hχ
      calc
        χ = e m := (e.apply_symm_apply χ).symm
        _ = 1 := by rw [h, h0]
    obtain ⟨c, hc, hc'⟩ := hr m hm
    refine ⟨ψ, centeredSquare C D (c.comp l), squarePolar D (c.comp l), hψ, ?_,
      centeredSquare_polar C D (c.comp l), hc'⟩
    intro x
    rw [← e.apply_symm_apply χ, he]
    change ψ (m (centeredSquareIn S C D l hS x)) = _
    rw [← hc]
    rfl
  · congr 1
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro m _
    simp only [Function.comp_apply, Equiv.symm_apply_apply, ← h0, e.injective.eq_iff]

#print axioms centeredSquare_variation_sq_of_linear_label_ranks

end
end Mathproof.EvenTI.OrderFour
