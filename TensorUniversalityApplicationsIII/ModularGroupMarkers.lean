import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Nat.Choose.Basic

namespace ModularGroupMarkers

/-- Doubling the central coefficient makes the collected exponent a multiple of the modulus. -/
theorem double_choose_two (M : ℕ) : 2 * M.choose 2 = M * (M - 1) := by
  rw [mul_comm 2, Nat.choose_two_right,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self M)]

/-- At an odd modulus, no enlargement of the center is needed. -/
theorem odd_choose_two_dvd (M : ℕ) (hM : Odd M) : M ∣ M.choose 2 := by
  obtain ⟨k, hk⟩ := hM
  have hpred : M - 1 = 2 * k := by simp [hk]
  refine ⟨k, ?_⟩
  rw [Nat.choose_two_right, hpred, mul_comm 2, ← Nat.mul_assoc]
  exact Nat.mul_div_cancel _ (by decide)

/-- Intersection of a unit-marked pair with the old carrier recovers just one mode. -/
theorem unit_marked_core {R X Y : Type*} [CommRing R] [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R Y] (u : Rˣ) (B : Y →ₗ[R] X) (C : X →ₗ[R] Y) (x : X) (y : Y) :
    (∃ a : X, ∃ b : Y, ∃ c : X, u • c + B b = x ∧ C a = y ∧ u • a = 0) ↔ y = 0 := by
  constructor
  · rintro ⟨a, _, _, _, hy, hp⟩
    have ha : a = 0 := by
      calc
        a = u⁻¹ • (u • a) := by rw [smul_smul, inv_mul_cancel, one_smul]
        _ = 0 := by rw [hp, smul_zero]
    simpa [ha] using hy.symm
  · intro hy
    refine ⟨0, 0, u⁻¹ • x, ?_, ?_, ?_⟩
    · simp [smul_smul]
    · simp [hy]
    · simp

end ModularGroupMarkers
