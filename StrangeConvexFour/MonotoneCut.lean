import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Order.Lattice

namespace StrangeConvexFour

theorem least_minimizer_antitone_of_cross {α : Type*} [Lattice α]
    (f g : α → ℚ) (x y : α)
    (hx : ∀ u, f x ≤ f u) (hy : ∀ u, g y ≤ g u)
    (least : ∀ u, g u = g y → y ≤ u)
    (cross : f (x ⊔ y) + g (x ⊓ y) ≤ f x + g y) : y ≤ x := by
  have he : g (x ⊓ y) = g y := by
    have hsup := hx (x ⊔ y)
    have hinf := hy (x ⊓ y)
    linarith
  exact (least (x ⊓ y) he).trans inf_le_left

end StrangeConvexFour
