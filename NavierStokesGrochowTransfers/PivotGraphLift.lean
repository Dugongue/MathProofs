import Mathlib.LinearAlgebra.Matrix.Adjugate

open Matrix

namespace BoundedModeTensorPC

theorem denominatorClearedGraphLift
    {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (pivot : Matrix ι ι R) (remaining : Matrix ι κ R)
    (x : ι → R) (v : κ → R)
    (h : pivot *ᵥ x + remaining *ᵥ v = 0) :
    pivot.det • x = -(pivot.adjugate *ᵥ (remaining *ᵥ v)) := by
  have h' := congrArg (fun y => pivot.adjugate *ᵥ y) h
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_zero] at h'
  rw [← Matrix.mulVec_mulVec] at h'
  exact eq_neg_of_add_eq_zero_left h'

end BoundedModeTensorPC

#print axioms BoundedModeTensorPC.denominatorClearedGraphLift