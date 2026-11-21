import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Module.Equiv.Basic

namespace AffineJet

/-- Mixed products force the three sorts of constants to vanish over any base ring. -/
theorem mixed_relations_kill_constants {R ι V : Type*} [CommRing R] [DecidableEq ι]
    [AddCommGroup V] [Module R V]
    (F : ((ι ⊕ Bool) → R) ≃ₗ[R] V) (t : ι) (c : ι → R) (a b : R)
    (mixed : ∀ i, a • F (Pi.single (Sum.inl i) 1) +
      c i • F (Pi.single (Sum.inr false) 1) = 0)
    (chart : b • (F (Pi.single (Sum.inl t) 1) -
      F (Pi.single (Sum.inr false) 1)) = 0) :
    a = 0 ∧ b = 0 ∧ ∀ i, c i = 0 := by
  have coeff (i : ι) :
      a • (Pi.single (Sum.inl i) 1 : (ι ⊕ Bool) → R) +
      c i • Pi.single (Sum.inr false) 1 = 0 := by
    simpa only [map_add, map_smul, map_zero, LinearEquiv.symm_apply_apply] using
      congrArg (fun v => F.symm v) (mixed i)
  have chartCoeff :
      b • ((Pi.single (Sum.inl t) 1 : (ι ⊕ Bool) → R) -
        Pi.single (Sum.inr false) 1) = 0 := by
    simpa only [map_sub, map_smul, map_zero, LinearEquiv.symm_apply_apply] using
      congrArg (fun v => F.symm v) chart
  refine ⟨?_, ?_, fun i => ?_⟩
  · simpa [Pi.single_apply] using congrFun (coeff t) (Sum.inl t)
  · simpa [Pi.single_apply] using congrFun chartCoeff (Sum.inl t)
  · simpa [Pi.single_apply] using congrFun (coeff i) (Sum.inr false)

end AffineJet
