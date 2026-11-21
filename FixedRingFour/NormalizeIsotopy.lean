import Mathlib.Algebra.Group.Units.Basic

namespace FixedRingFour

theorem normalize_isotopy {A B : Type*} [Monoid A] [Monoid B]
    (f g h : A → B) (a b : Bˣ) (ha : f 1 = ↑a) (hb : g 1 = ↑b)
    (hmul : ∀ x y, h (x * y) = f x * g y) :
    let c : B := ↑((a * b)⁻¹)
    (∀ x y, h (x * y) * c = (h x * c) * (h y * c)) ∧ h 1 * c = 1 := by
  have hf (x : A) : f x = h x * ↑(b⁻¹) := by
    have hx : h x = f x * ↑b := by simpa [hb] using hmul x 1
    rw [hx]
    simp [mul_assoc]
  have hg (y : A) : g y = ↑(a⁻¹) * h y := by
    have hy : h y = ↑a * g y := by simpa [ha] using hmul 1 y
    rw [hy]
    simp [← mul_assoc]
  have hunit : h 1 = (↑(a * b) : B) := by
    simpa [ha, hb] using hmul 1 1
  dsimp only
  constructor
  · intro x y
    rw [hmul, hf, hg, mul_inv_rev]
    simp only [Units.val_mul, mul_assoc]
  · rw [hunit]
    exact Units.mul_inv (a * b)

end FixedRingFour
