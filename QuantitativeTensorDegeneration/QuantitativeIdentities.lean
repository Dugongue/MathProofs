import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Abel

namespace QuantitativeDegeneration

theorem isotopy_recovery {G : Type*} [Group G] (a f g h : G)
    (hleft : h = a * g) :
    g * h⁻¹ * f = a⁻¹ * f := by
  rw [hleft, mul_inv_rev]
  simp

theorem inverse_middle_cost {G : Type*} [Group G] (cost : G → ℕ)
    (hInv : ∀ a, cost a⁻¹ = cost a)
    (hMul : ∀ a b, cost (a * b) ≤ cost a + cost b)
    {f g h : G} {b : ℕ}
    (hf : cost f ≤ b) (hg : cost g ≤ b) (hh : cost h ≤ b) :
    cost (g * h⁻¹ * f) ≤ 3 * b := by
  have hgh := hMul g h⁻¹
  have htotal := hMul (g * h⁻¹) f
  rw [hInv] at hgh
  omega

theorem quotient_cycle_cost {G : Type*} [Group G] (cost : G → ℕ)
    (hInv : ∀ a, cost a⁻¹ = cost a)
    (hMul : ∀ a b, cost (a * b) ≤ cost a + cost b)
    {scale cycle : G} {b : ℕ}
    (hs : cost scale ≤ 3 * b) (hc : cost cycle ≤ 3 * b) :
    cost (scale⁻¹ * cycle) ≤ 6 * b := by
  have h := hMul scale⁻¹ cycle
  rw [hInv] at h
  omega

theorem doubling_lower_bound (w : ℕ → ℤ) (h0 : 1 ≤ w 0)
    (hstep : ∀ n, 2 * w n ≤ w (n + 1)) (n : ℕ) :
    (2 : ℤ) ^ n ≤ w n := by
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      have h := hstep n
      rw [pow_succ]
      omega

theorem determinant_fiber_coordinates {G : Type*} [AddCommGroup G]
    (x y z : G) :
    let d := x + y - z
    let a := z - y
    let b := z - x
    d + a = x ∧ d + b = y ∧ d + a + b = z := by
  dsimp
  constructor
  · abel
  constructor
  · abel
  · abel

end QuantitativeDegeneration
