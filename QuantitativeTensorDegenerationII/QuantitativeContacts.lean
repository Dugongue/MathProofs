import Mathlib.Algebra.Order.Ring.Int

namespace QuantitativeContacts

theorem twice_anchor (z : ℤ) (lower : 1 ≤ z) (upper : 2 * z ≤ 2) :
    z = 1 := by omega

theorem contact_box (a b c : ℤ)
    (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2) :
    (1 ≤ a + b + c - 3 ∧ a + b + c - 3 ≤ 2) ↔ ¬ (a = b ∧ b = c) := by
  omega

theorem literal_complement (x : ℤ) (bounds : 1 ≤ x ∧ x ≤ 2) :
    (1 ≤ 3 - x ∧ 3 - x ≤ 2) ∧ (3 - x - 1 = 1 - (x - 1)) := by omega

theorem two_power_positive_multiple (m e : ℕ) (positive : 0 < e)
    (divisible : 2 ^ m ∣ e) : 2 ^ m ≤ e :=
  Nat.le_of_dvd positive divisible

end QuantitativeContacts
