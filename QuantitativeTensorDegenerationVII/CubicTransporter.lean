import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Data.Fin.Basic

namespace CubicTransporter

/-- Moving coefficients in either input forces the third slot to kill
right multiples of commutators. -/
theorem balanced_vanishes_on_commutator_multiple
    {R M N G : Type*} [Ring R] [AddCommGroup G]
    (rightM : M → R → M) (rightN : N → R → N)
    (T : M → N → R → G)
    (left_balance : ∀ x y a r, T (rightM x a) y r = T x y (a * r))
    (right_balance : ∀ x y a r, T x (rightN y a) r = T x y (a * r))
    (subtract : ∀ x y u v, T x y (u - v) = T x y u - T x y v)
    (x : M) (y : N) (a b r : R) :
    T x y ((a * b - b * a) * r) = 0 := by
  have commute : T x y ((a * b) * r) = T x y ((b * a) * r) := by
    calc
      T x y ((a * b) * r) = T x y (a * (b * r)) := by rw [mul_assoc]
      _ = T (rightM x a) y (b * r) := (left_balance x y a (b * r)).symm
      _ = T (rightM x a) (rightN y b) r := (right_balance _ y b r).symm
      _ = T x (rightN y b) (a * r) := left_balance x _ a r
      _ = T x y (b * (a * r)) := right_balance x y b (a * r)
      _ = T x y ((b * a) * r) := by rw [mul_assoc]
  rw [sub_mul, subtract, commute, sub_self]

/-- An idempotent whose complement is a unit vanishes. This is the
coordinate test used in lifting the pinned idempotents. -/
theorem idempotent_eq_zero_of_complement_unit {R : Type*} [Ring R]
    (e : R) (he : e * e = e) (hu : IsUnit (1 - e)) : e = 0 := by
  have hz : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  obtain ⟨u, hu⟩ := hu
  calc
    e = e * ((u : R) * ((u⁻¹ : Rˣ) : R)) := by rw [Units.mul_inv, mul_one]
    _ = (e * (u : R)) * ((u⁻¹ : Rˣ) : R) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hu, hz, zero_mul]

/-- Three selector columns are enough to make the first graph component
vanish if two separate selector slots satisfy the isotropic relation. -/
theorem graph_column_selector {A : Type*} [AddMonoid A]
    (i j : Fin 3) (h : Fin 3 → A)
    (correction : Fin 3 → Fin 3 → A)
    (isotropic : ∀ a b : Fin 3, h a + (if b = j then correction a b else 0) = 0) :
    h i = 0 := by
  have distinct : ∃ b : Fin 3, b ≠ j := by
    by_cases hj : j = 0
    · exact ⟨1, by rw [hj]; decide⟩
    · exact ⟨0, Ne.symm hj⟩
  obtain ⟨b, hb⟩ := distinct
  simpa [hb] using isotropic i b
end CubicTransporter
