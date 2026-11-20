import EvenP6LiveCellsAction
import EvenP6LiveAlgebraDual

/-! The actual mode matrix applies the coordinate table separately to each
of its field blocks. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellPreparation

open EvenTI.CellProducer EvenTI.LiveAlgebra Matrix

variable {K : Type} [Field K] {d : ℕ} {width : Fin d → ℕ}
  {D : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Fintype (D i v)] [∀ i v, DecidableEq (D i v)]
  {X : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
  (t : ∀ i v, WordTable K (D i v))
  (P : ∀ i v, (D i v → K) ≃ₗ[K] X i v)
  (hOne : ∀ i v, P i v (t i v).one = 1)
  (hMul : ∀ i v a b, P i v ((t i v).multiply a b) = P i v a * P i v b)

include hOne hMul in
theorem liveActionMatrix_mulVec (i : Fin d) (a : ∀ v, X i v)
    (x : LiveModeIndex D i → K) (p : LiveModeIndex D i) :
    ((liveActionMatrix t P i a).mulVec x) p =
      (t i p.1).multiply ((P i p.1).symm (a p.1)) (fun j => x ⟨p.1,j⟩) p.2 := by
  let E := EvenTI.CellPreparation.blockDecode (P i)
  have h := blockTable_model (t i) (P i) (hOne i) (hMul i)
  letI : WordTable.Laws (blockTable (t i)) := WordTable.laws_of_model _ E h.1 h.2
  exact congrFun (wordMulMatrix_mulVec (blockTable (t i))
    (fun z => (P i z.1).symm (a z.1) z.2) x) p

#print axioms liveActionMatrix_mulVec

end EvenTI.CellPreparation
