import Mathlib.Algebra.Group.Basic

namespace QPFFallout

theorem normalized_mul {A B : Type*} [Monoid A] [Monoid B]
    (F G H : A → B) (ia ib : B)
    (ha : ia * F 1 = 1) (hb : G 1 * ib = 1)
    (h : ∀ x y, F x * G y = H (x * y)) (x y : A) :
    ia * H (x * y) * ib = (ia * H x * ib) * (ia * H y * ib) := by
  have hx : F x * G 1 = H x := by simpa only [mul_one] using h x 1
  have hy : F 1 * G y = H y := by simpa only [one_mul] using h 1 y
  have lx : ia * H x * ib = ia * F x := by
    rw [← hx]
    calc
      ia * (F x * G 1) * ib = (ia * F x) * (G 1 * ib) := by
        simp only [mul_assoc]
      _ = ia * F x := by rw [hb, mul_one]
  have ry : ia * H y * ib = G y * ib := by
    rw [← hy, ← mul_assoc ia (F 1) (G y), ha, one_mul]
  rw [lx, ry, ← h x y]
  simp only [mul_assoc]

end QPFFallout
