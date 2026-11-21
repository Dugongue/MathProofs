import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas

namespace PermanentalCauchy

theorem cubicWronskian (x a b c d : ℚ) :
    (3 * x ^ 2 + a) * (x ^ 2 + c * x + d) -
      (x ^ 3 + a * x + b) * (2 * x + c) =
    x ^ 4 + (2 * c) * x ^ 3 + (3 * d - a) * x ^ 2 -
      (2 * b) * x + (a * d - b * c) := by
  ring

theorem pencilDiscriminant (a b c d s₁ s₂ s₃ s₄ : ℚ)
    (h₁ : 2 * c = s₁) (h₂ : 3 * d - a = s₂)
    (h₃ : -(2 * b) = s₃) (h₄ : a * d - b * c = s₄) :
    (6 * d - s₂) ^ 2 = s₂ ^ 2 + 12 * s₄ - 3 * s₁ * s₃ := by
  rw [← h₁, ← h₂, ← h₃, ← h₄]
  ring

theorem noRationalPencilCoefficients (a b c d : ℚ)
    (h₁ : 2 * c = -6) (h₂ : 3 * d - a = 11)
    (h₃ : -(2 * b) = -6) (h₄ : a * d - b * c = 0) : False := by
  have h := pencilDiscriminant a b c d (-6) 11 (-6) 0 h₁ h₂ h₃ h₄
  norm_num at h
  have hs : IsSquare (13 : ℚ) := ⟨6 * d - 11, by simpa [pow_two] using h.symm⟩
  have hn := Rat.isSquare_natCast_iff.mp
    (show IsSquare ((13 : ℕ) : ℚ) from hs)
  obtain ⟨k, hk⟩ := hn
  have hlt : k < 4 := by
    by_contra! hge
    have hmul : 16 ≤ k * k := Nat.mul_le_mul hge hge
    omega
  interval_cases k <;> norm_num at hk

theorem realWitnessResidues (z : ℚ) :
    let A := z ^ 6 - 4 * z ^ 4 + 4 * z ^ 2 - 1
    let A₁ := 6 * z ^ 5 - 16 * z ^ 3 + 8 * z
    let A₂ := 30 * z ^ 4 - 48 * z ^ 2 + 8
    let B := z ^ 6 - 9 * z ^ 4 + 18 * z ^ 2 - 8
    let B₁ := 6 * z ^ 5 - 36 * z ^ 3 + 36 * z
    let H := z ^ 4 + 7 * z ^ 2 + 1
    let H₁ := 4 * z ^ 3 + 14 * z
    let J := z ^ 3 + z
    let J₁ := 3 * z ^ 2 + 1
    A₁ * (B₁ * H + B * H₁) - A₂ * B * H =
      A * (30 * z ^ 8 - 28 * z ^ 6 - 264 * z ^ 4 + 432 * z ^ 2 - 64) ∧
    A₁ * (B₁ * J + B * J₁) - A₂ * B * J =
      A * (24 * z ^ 7 - 96 * z ^ 5 + 96 * z ^ 3) := by
  dsimp
  constructor <;> ring

end PermanentalCauchy
