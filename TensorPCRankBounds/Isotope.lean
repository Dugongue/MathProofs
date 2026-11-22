import Mathlib.Algebra.Group.Units.Basic

theorem isotopeMultiplicative
    {A B : Type*} [Monoid A] [Mul B]
    (rInv pInv qInv : B → A) (u v : Aˣ)
    (leftIdentity : ∀ z, rInv z = (u : A) * qInv z)
    (rightIdentity : ∀ z, rInv z = pInv z * (v : A))
    (productIdentity : ∀ z w, rInv (z * w) = pInv z * qInv w) :
    ∀ z w,
      ((↑u⁻¹ : A) * rInv (z * w) * (↑v⁻¹ : A)) =
        ((↑u⁻¹ : A) * rInv z * (↑v⁻¹ : A)) *
          ((↑u⁻¹ : A) * rInv w * (↑v⁻¹ : A)) := by
  intro z w
  have hp : pInv z = rInv z * (↑v⁻¹ : A) := by
    rw [rightIdentity z]
    simp [mul_assoc]
  have hq : qInv w = (↑u⁻¹ : A) * rInv w := by
    rw [leftIdentity w]
    simp [← mul_assoc]
  rw [productIdentity z w, hp, hq]
  simp only [mul_assoc]
