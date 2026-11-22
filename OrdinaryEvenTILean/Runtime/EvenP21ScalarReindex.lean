import Mathlib.Data.Matrix.Mul

set_option autoImplicit false

namespace EvenTI.P21Scalar

variable {R I J I' J' : Type} [Semiring R] [Fintype J] [Fintype J']

/-- A simultaneous change of the physical equation and word addresses preserves
the exact collection of feasible probe words. -/
theorem probeKernel_reindex (A : Matrix I J R) (rows : I' ≃ I) (words : J' ≃ J)
    (z : J' → R) :
    (A.submatrix rows words).mulVec z = 0 ↔ A.mulVec (z ∘ words.symm) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  constructor
  · intro h
    funext i
    simpa using congrFun h (rows.symm i)
  · intro h
    simpa [h]

/-- Every feasible probe satisfies the same verdict in either address order.
The consumer must relabel its sites by the very same word equivalence. -/
theorem forall_probeKernel_reindex (A : Matrix I J R) (rows : I' ≃ I) (words : J' ≃ J)
    (test : (J → R) → Prop) :
    (∀ z, (A.submatrix rows words).mulVec z = 0 → test (z ∘ words.symm)) ↔
      ∀ z, A.mulVec z = 0 → test z := by
  constructor
  · intro h z hz
    have e : (z ∘ words) ∘ words.symm = z := by funext i; simp
    have t := h (z ∘ words) ((probeKernel_reindex A rows words _).mpr (by rwa [e]))
    rwa [e] at t
  · intro h z hz
    exact h _ ((probeKernel_reindex A rows words z).mp hz)

/-- The scalar comparison, including a support mask, reads the same words
after both the blocks and their physical site addresses have been relabeled. -/
theorem supportedSites_reindex {B B' : Type} (blocks : B' ≃ B) (words : J' ≃ J)
    (site : B → J) (active : B → Prop) (z : J' → R) :
    (∀ i j : B', active (blocks i) → active (blocks j) →
      z (words.symm (site (blocks i))) = z (words.symm (site (blocks j)))) ↔
      ∀ i j : B, active i → active j →
        (z ∘ words.symm) (site i) = (z ∘ words.symm) (site j) := by
  constructor
  · intro h i j hi hj
    simpa [Function.comp_def] using
      h (blocks.symm i) (blocks.symm j) (by simpa using hi) (by simpa using hj)
  · intro h i j hi hj
    exact h (blocks i) (blocks j) hi hj

#print axioms probeKernel_reindex
#print axioms forall_probeKernel_reindex
#print axioms supportedSites_reindex
end EvenTI.P21Scalar

