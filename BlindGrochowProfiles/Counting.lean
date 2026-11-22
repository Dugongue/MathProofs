import Mathlib.Tactic

namespace BlindGrochowCounting

/-- Forgetting the p-primary cycle length commutes with restriction of cycles. -/
theorem collapse_restriction (p t b g : ℕ) :
    p ^ min t b * g * p ^ (t - b) = p ^ t * g := by
  have h : min t b + (t - b) = t := by omega
  calc
    p ^ min t b * g * p ^ (t - b) =
        (p ^ min t b * p ^ (t - b)) * g := by ac_rfl
    _ = p ^ t * g := by rw [← pow_add, h]

/-- The largest surviving p-layer must be balanced by the other layers. -/
theorem balanced_mass {rest layer p L : ℕ} (balance : layer ≤ rest)
    (large : p * L ≤ layer) : 2 * p * L ≤ rest + layer := by
  calc
    2 * p * L = p * L + p * L := by ring
    _ ≤ layer + layer := Nat.add_le_add large large
    _ ≤ rest + layer := Nat.add_le_add_right balance layer

end BlindGrochowCounting

#print axioms BlindGrochowCounting.collapse_restriction
#print axioms BlindGrochowCounting.balanced_mass
