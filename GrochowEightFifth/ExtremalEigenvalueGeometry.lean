import Mathlib.Tactic

namespace ExtremalEigenvalueGeometry

theorem shiftedModulusDeficit (r rho u v x y : ℝ)
    (unit : u^2 + v^2 = 1) :
    (r + rho)^2 - ((r + u*x + v*y)^2 + (u*y - v*x)^2) =
      (rho^2 - (x^2 + y^2)) + 2*r*(rho - (u*x + v*y)) := by
  have rotation : (u*x + v*y)^2 + (u*y - v*x)^2 = x^2 + y^2 := by
    calc
      (u*x + v*y)^2 + (u*y - v*x)^2 = (u^2 + v^2) * (x^2 + y^2) := by ring
      _ = x^2 + y^2 := by rw [unit, one_mul]
  linarith only [rotation,
    show (r + u*x + v*y)^2 = r^2 + 2*r*(u*x + v*y) + (u*x + v*y)^2 by ring,
    show (r + rho)^2 = r^2 + 2*r*rho + rho^2 by ring]

theorem approximateDirection (rho u v x y : ℝ)
    (unit : u^2 + v^2 = 1) (radial : x^2 + y^2 ≤ rho^2) :
    (rho*u - x)^2 + (rho*v - y)^2 ≤ 2*rho*(rho - (u*x + v*y)) := by
  calc
    (rho*u - x)^2 + (rho*v - y)^2 =
        rho^2*(u^2 + v^2) - 2*rho*(u*x + v*y) + (x^2 + y^2) := by ring
    _ ≤ 2*rho*(rho - (u*x + v*y)) := by rw [unit]; linarith

#print axioms shiftedModulusDeficit
#print axioms approximateDirection

end ExtremalEigenvalueGeometry
