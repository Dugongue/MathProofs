import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Tactic.Abel

theorem fixedDifferenceAdditive {G V : Type*} [Group G] [AddCommGroup V]
    [DistribMulAction G V] (g h : G) (v : V)
    (hfix : g • (h • v - v) = h • v - v) :
    (g * h) • v - v = (g • v - v) + (h • v - v) := by
  rw [mul_smul]
  calc
    g • (h • v) - v = g • (h • v - v) + (g • v - v) := by
      rw [smul_sub]
      abel
    _ = (g • v - v) + (h • v - v) := by
      rw [hfix, add_comm]
