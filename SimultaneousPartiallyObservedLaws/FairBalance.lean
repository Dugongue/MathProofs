import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

theorem two_fair_observations_balance (r x y : ℤ)
    (baseline : r + x - y = 0) (flipped : r - x + y = 0) : x = y := by
  omega
