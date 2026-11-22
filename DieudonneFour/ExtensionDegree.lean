import Mathlib.Data.Nat.GCD.Basic

namespace DieudonneFour

theorem coprime_quotient_dvd {a b d : ℕ} (h : Nat.Coprime b a) :
    b ∣ d / Nat.gcd d a ↔ b ∣ d := by
  have hg : Nat.Coprime b (Nat.gcd d a) :=
    h.of_dvd_right (Nat.gcd_dvd_right d a)
  have hm : d / Nat.gcd d a * Nat.gcd d a = d :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left d a)
  simpa only [hm] using (hg.dvd_mul_right (m := d / Nat.gcd d a)).symm

end DieudonneFour
