import Mathlib.Algebra.Algebra.Basic

namespace FinalDigitFour

theorem regular_commutant {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    (B : Submodule R A) (f : A →ₗ[R] A)
    (span : ∀ x : A, ∃ (r : R) (b : B), x = r • (1 : A) + b) :
    (∀ (b : B) (x : A), f ((1 + (b : A)) * x) = (1 + (b : A)) * f x) ↔
      (∀ x : A, f x = x * f 1) := by
  constructor
  · intro h x
    obtain ⟨r, b, rfl⟩ := span x
    have hb : f (b : A) = (b : A) * f 1 := by
      have hu := h b 1
      simp only [mul_one, add_mul, one_mul, map_add] at hu
      exact add_left_cancel hu
    rw [map_add, map_smul, hb, add_mul, smul_mul_assoc, one_mul]
  · intro h b x
    calc
      f ((1 + (b : A)) * x) = ((1 + (b : A)) * x) * f 1 := h _
      _ = (1 + (b : A)) * (x * f 1) := mul_assoc ..
      _ = (1 + (b : A)) * f x := by rw [← h x]

end FinalDigitFour
