import EvenP12CompareRightKernel
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
namespace EvenTI.P18Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The already-paid right-kernel rank is an exact dispatch predicate for
the reciprocal-trial path. -/
theorem reciprocal_iff_rightNullity_zero {d n : ℕ} (T : Tensor K (d+d) n) :
    Module.finrank K (flatten T).mulVecLin.ker = 0 ↔ IsUnit (flatten T) := by
  rw [Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]
  exact Matrix.mulVec_injective_iff_isUnit

#print axioms reciprocal_iff_rightNullity_zero
end EvenTI.P18Execution

