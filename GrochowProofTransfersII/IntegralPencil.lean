import Mathlib.RingTheory.Coprime.Basic

namespace IntegralPencil

theorem scaled_fractional_det_nonunit {R : Type*} [CommRing R]
    (M a b c A B C D : R) (hM : ¬ IsUnit M) (hcop : IsCoprime M c)
    (ha : c * A = M * (a * C))
    (hb : c * B = M * (b * C)) :
    ¬ IsUnit (A * D - B * C) := by
  have hA : M ∣ A := hcop.dvd_of_dvd_mul_left ⟨a * C, ha⟩
  have hB : M ∣ B := hcop.dvd_of_dvd_mul_left ⟨b * C, hb⟩
  exact fun h => hM (isUnit_of_dvd_unit
    (dvd_sub (dvd_mul_of_dvd_left hA D) (dvd_mul_of_dvd_left hB C)) h)

end IntegralPencil
