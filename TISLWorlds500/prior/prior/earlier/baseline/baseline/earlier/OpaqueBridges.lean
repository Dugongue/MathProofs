import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

namespace TwoWorlds

theorem inversion_by_order_three_forces_fix {G : Type*} [Group G]
    (σ : G ≃* G) (a : G) (h : σ a = a⁻¹)
    (h₃ : σ (σ (σ a)) = a) : σ a = a := by
  have h₂ : σ (σ a) = a := by rw [h, map_inv, h, inv_inv]
  rwa [h₂] at h₃

theorem common_transcript_gap {p q r ε δ : ℚ}
    (hp : |p - r| ≤ δ) (hq : |q - r| ≤ δ)
    (hpos : 1 - ε ≤ p) (hneg : q ≤ ε) : 1 - 2 * ε ≤ 2 * δ := by
  have hpr : p - r ≤ δ := (le_abs_self _).trans hp
  have hrq : r - q ≤ δ := by
    have hn : -(q - r) ≤ δ := (neg_le_abs _).trans hq
    linarith
  linarith

end TwoWorlds
