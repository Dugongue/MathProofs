import EvenP6LiveCellsAction
import EvenP6LiveCellsRows
import EvenP6SignedRows

/-! The signed cell equations, including the shared variable and its dual
copies, are exact for the literal transported dense coefficient arrays. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenTI.CellProducer EvenOrdinaryTI.LiveRows Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d s N : ℕ}
  {width : Fin (d + 2) → ℕ}
  {D : (i : Fin (d + 2)) → Fin (width i) → Type}
  [∀ i v, Fintype (D i v)] [∀ i v, DecidableEq (D i v)]
  (t : ∀ i v, WordTable K (D i v)) [WordTable.Laws (liveJointTable t)] [IsReduced (LiveJoint t)]
  (enum : Fin (Fintype.card K) ≃ K) (e : Fin N ≃ LiveJointIndex D)
  {X : (i : Fin (d + 2)) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
  (P : ∀ i v, (D i v → K) ≃ₗ[K] X i v)
  (hOne : ∀ i v, P i v (t i v).one = 1)
  (hMul : ∀ i v a b, P i v ((t i v).multiply a b) = P i v a * P i v b)
  (U : Fin s → Type) [∀ v, Field (U v)] [∀ v, Algebra K (U v)]
  (key : ∀ i, Fin (width i) → Option (Fin s))
  (link : ∀ i v, withBase (K := K) U (key i v) →ₐ[K] X i v)
  (negative : ∀ i, Fin (width i) → Bool)

local instance signedLiveFields :
    ∀ i : Fin (rawCells enum (liveCoordinates t e)).length,
      CellFieldCertificate (liveCoordinates t e) ((rawCells enum (liveCoordinates t e)).get i) :=
  liveCellCertificate t enum e

/-- Execute the signed dense action with the actual scalar fill and
inverse copies. The same unit is reused at every occurrence of its label. -/
def liveSignedAction (source : Fin N → K) (x : ∀ v, (U v)ˣ) : Fin N → K :=
  fun j => wordAction (fun i =>
    liveActionMatrix t P i (fun v => (sharedUnits U key link negative x i v : X i v)))
    (fun p => source (e.symm p)) (e j)

theorem liveSignedAction_eq_table (source : Fin N → K) (x : ∀ v, (U v)ˣ) :
    liveOperand t e (liveSignedAction t e P U key link negative source x) =
      (∏ i : Fin (d + 2), liveMode t P hOne hMul i
        (fun v => (sharedUnits U key link negative x i v : X i v))) * liveOperand t e source := by
  rw [liveTableAction_eq t P hOne hMul]
  apply (TableWord.wordEquiv _).injective
  funext p
  change wordAction _ (fun p => source (e.symm p)) (e (e.symm p)) = _
  rw [e.apply_symm_apply] <;> rfl

theorem liveSignedCells_iff (source target : Fin N → K) (x : ∀ v, (U v)ˣ) :
    liveSignedAction t e P U key link negative source x = target ↔
    ∃ c : ∀ r : LiveActive t enum e source, (LiveActiveField t enum e source r)ˣ,
      liveCellRatios t enum e source target = some c ∧
      ∀ r, (∏ i : Fin (d + 2), signedFactor U (LiveActiveField t enum e source)
        (joinedOrigin enum (liveCoordinates t e) (liveMode t P hOne hMul) key (liveOperand t e source))
        (joinedEmbedding enum (liveCoordinates t e) (liveMode t P hOne hMul) U key link (liveOperand t e source))
        (joinedNegative enum (liveCoordinates t e) (liveMode t P hOne hMul) negative (liveOperand t e source))
        x r i) = c r := by
  have h := rawSignedRows_iff enum (liveCoordinates t e) (liveMode t P hOne hMul) U key link negative
    (liveOperand t e source) (liveOperand t e target) x
  rw [← liveSignedAction_eq_table t e P hOne hMul] at h
  exact ((liveCoordinates t e).symm.injective.eq_iff).symm.trans h

#print axioms liveSignedAction_eq_table
#print axioms liveSignedCells_iff

end EvenTI.CellPreparation
