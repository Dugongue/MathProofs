import Mathlib.Tactic.Ring

theorem tied_bilinear_transport {R : Type*} [CommRing R]
    (a b ai bi p q m m' : R) (ha : a * ai = 1) (hb : b * bi = 1)
    (tie : b * p = a * q) (transport : p * q * m' = (a * b) * m) :
    (ai * p) * (ai * p) * m' = m := by
  have q_eq : b * (ai * p) = q := by
    calc
      b * (ai * p) = ai * (b * p) := by ring
      _ = ai * (a * q) := by rw [tie]
      _ = (a * ai) * q := by ring
      _ = q := by rw [ha, one_mul]
  calc
    (ai * p) * (ai * p) * m'
        = (ai * bi) * (p * (b * (ai * p)) * m') := by
            calc
              _ = (b * bi) * ((ai * p) * (ai * p) * m') := by rw [hb, one_mul]
              _ = _ := by ring
    _ = (ai * bi) * (p * q * m') := by rw [q_eq]
    _ = (ai * bi) * ((a * b) * m) := by rw [transport]
    _ = (a * ai) * (b * bi) * m := by ring
    _ = m := by rw [ha, hb, one_mul, one_mul]

theorem project_peirce_corner {R : Type*} [Semigroup R] (e f a x b : R)
    (left_support : e * x = x) (right_support : x * f = x) :
    e * (a * x * b) * f = (e * a * e) * x * (f * b * f) := by
  have supported : e * x * f = x := by rw [left_support, right_support]
  calc
    e * (a * x * b) * f = e * (a * (e * x * f) * b) * f := by rw [supported]
    _ = (e * a * e) * x * (f * b * f) := by simp only [mul_assoc]
