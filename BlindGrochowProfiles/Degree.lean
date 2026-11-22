import Mathlib

namespace DegreeDescent

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B]

/-- An isotopy between unital commutative algebra multiplication tensors yields
an algebra equivalence over the same scalar semiring. -/
theorem equiv_of_isotopy (X Y Z : A ≃ₗ[R] B)
    (h : ∀ x y : A, Z (x * y) = X x * Y y) : Nonempty (A ≃ₐ[R] B) := by
  have hx (x : A) : Z x = X x * Y 1 := by simpa using h x 1
  have hy (y : A) : Z y = X 1 * Y y := by simpa using h 1 y
  have hn (x y : A) : Z 1 * Z (x * y) = Z x * Z y := by
    calc
      Z 1 * Z (x * y) = (X 1 * Y 1) * (X x * Y y) := by rw [hx 1, h x y]
      _ = (X x * Y 1) * (X 1 * Y y) := by ac_rfl
      _ = Z x * Z y := by rw [← hx x, ← hy y]
  obtain ⟨t, ht⟩ := Z.surjective 1
  have hu : IsUnit (Z 1) := isUnit_iff_exists_inv.mpr
    ⟨Z (t * t), by rw [hn, ht, one_mul]⟩
  obtain ⟨u, hu⟩ := hu
  let L := Z.trans (Units.mulLeftLinearEquiv R B u⁻¹)
  have hL (x : A) : L x = (↑(u⁻¹) : B) * Z x := rfl
  have hi : (↑(u⁻¹) : B) * Z 1 = 1 := by rw [← hu]; simp
  refine ⟨AlgEquiv.ofLinearEquiv L ((hL 1).trans hi) ?_⟩
  intro x y
  simp only [hL]
  calc
    (↑(u⁻¹) : B) * Z (x * y)
        = ((↑(u⁻¹) : B) * Z 1) * ((↑(u⁻¹) : B) * Z (x * y)) := by rw [hi, one_mul]
    _ = ((↑(u⁻¹) : B) * (↑(u⁻¹) : B)) * (Z 1 * Z (x * y)) := by ac_rfl
    _ = ((↑(u⁻¹) : B) * Z x) * ((↑(u⁻¹) : B) * Z y) := by rw [hn]; ac_rfl

end DegreeDescent
