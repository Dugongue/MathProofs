import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Group.Action.Basic

namespace OrientationBridge

theorem permutation_sign_of_odd_power {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) {n : ℕ} (hn : n % 2 = 1) (hσ : σ ^ n = 1) :
    Equiv.Perm.sign σ = 1 := by
  have hs : Equiv.Perm.sign σ ^ n = 1 := by
    simpa only [map_pow, map_one] using
      congrArg (Equiv.Perm.sign : Equiv.Perm α → ℤˣ) hσ
  rwa [Int.units_pow_eq_pow_mod_two, hn, pow_one] at hs

theorem oriented_transporter_iff_stabilizer_correction
    {G H X : Type*} [Group G] [Group H] [MulAction G X]
    (χ : G →* H) {x y : X} {g₀ : G} (hg₀ : g₀ • x = y) :
    (∃ g : G, g • x = y ∧ χ g = 1) ↔
      ∃ a : G, a • x = x ∧ χ a = (χ g₀)⁻¹ := by
  constructor
  · rintro ⟨g, hg, hd⟩
    refine ⟨g₀⁻¹ * g, ?_, ?_⟩
    · rw [mul_smul, hg, ← hg₀, inv_smul_smul]
    · simp [hd]
  · rintro ⟨a, ha, hd⟩
    refine ⟨g₀ * a, ?_, ?_⟩
    · rw [mul_smul, ha, hg₀]
    · simp [hd]

end OrientationBridge
