import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Group

namespace ClosedOrbitGauges

/-- Normalizing by the inverse induced change leaves unit determinant. -/
theorem det_gauge {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (h inducedInverse : Matrix ι ι R) (hh : h.det = 1) (hi : inducedInverse.det = 1) :
    (h * inducedInverse).det = 1 := by
  rw [Matrix.det_mul, hh, hi, mul_one]

/-- A change of basis on the intermediate product input cancels in a composite. -/
theorem normalize_comp {R ι κ τ : Type*} [CommRing R]
    [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]
    (output : Matrix ι κ R) (basis basisInverse : Matrix κ κ R)
    (input : Matrix κ τ R) (inverse_law : basis * basisInverse = 1) :
    (output * basis) * (basisInverse * input) = output * input := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc basis, inverse_law, Matrix.one_mul]

/-- Fibers of the left-oriented Lang map are right cosets of the fixed subgroup. -/
theorem lang_fiber {G : Type*} [Group G] (F : G →* G) (x y : G) :
    F x * x⁻¹ = F y * y⁻¹ ↔ F (y⁻¹ * x) = y⁻¹ * x := by
  rw [map_mul, map_inv]
  constructor
  · intro h
    calc
      (F y)⁻¹ * F x = (F y)⁻¹ * (F x * x⁻¹) * x := by group
      _ = (F y)⁻¹ * (F y * y⁻¹) * x := by rw [h]
      _ = y⁻¹ * x := by group
  · intro h
    calc
      F x * x⁻¹ = F y * ((F y)⁻¹ * F x) * x⁻¹ := by group
      _ = F y * (y⁻¹ * x) * x⁻¹ := by rw [h]
      _ = F y * y⁻¹ := by group

end ClosedOrbitGauges
