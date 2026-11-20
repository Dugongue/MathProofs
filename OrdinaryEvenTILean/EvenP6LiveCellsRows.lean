import EvenP6LiveCells
import EvenP6RawRows

/-! Run the checked cell equational form from actual primary coefficient
tables. Raw tensor entries enter in their input coordinate slots. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenTI.CellProducer EvenOrdinaryTI.LiveRows Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {d : ℕ} {width : Fin d → ℕ} {D : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Fintype (D i v)] [∀ i v, DecidableEq (D i v)]
  (t : ∀ i v, WordTable K (D i v)) [WordTable.Laws (liveJointTable t)]
  (enum : Fin (Fintype.card K) ≃ K) {N : ℕ} (e : Fin N ≃ LiveJointIndex D)

def liveOperand (coeff : Fin N → K) : LiveJoint t :=
  (liveCoordinates t e).symm coeff

variable [IsReduced (LiveJoint t)]

local instance liveRowsFields :
    ∀ i : Fin (rawCells enum (liveCoordinates t e)).length,
      CellFieldCertificate (liveCoordinates t e) ((rawCells enum (liveCoordinates t e)).get i) :=
  liveCellCertificate t enum e

abbrev LiveActive (coeff : Fin N → K) :=
  Fin (activeCells (compactProductPack enum (liveCoordinates t e) (liveOperand t e coeff))).card

abbrev LiveActiveField (coeff : Fin N → K) (r : LiveActive t enum e coeff) :=
  ProducedCell enum (liveCoordinates t e)
    (activeIndex (compactProductPack enum (liveCoordinates t e) (liveOperand t e coeff)) r)
/-- Reject exactly unequal support; otherwise emit all exact compact ratios. -/
def liveCellRatios (source target : Fin N → K) :
    Option (∀ r : LiveActive t enum e source, (LiveActiveField t enum e source r)ˣ) :=
  rawRatios enum (liveCoordinates t e) (liveOperand t e source) (liveOperand t e target)

theorem liveCellRatios_none_iff (source target : Fin N → K) :
    liveCellRatios t enum e source target = none ↔
      ¬ ∀ j, compactProductPack enum (liveCoordinates t e) (liveOperand t e source) j = 0 ↔
        compactProductPack enum (liveCoordinates t e) (liveOperand t e target) j = 0 := by
  exact liveRatios_none_iff _ _

theorem liveActive_card_le (source : Fin N → K) :
    (activeCells (compactProductPack enum (liveCoordinates t e) (liveOperand t e source))).card ≤ N :=
  (activeCells_card_le _).trans (liveCells_length_le t enum e)

/-- The field sizes written by the driver use the actual pivot counts. -/
def liveActiveDegree (source : Fin N → K) (r : LiveActive t enum e source) : ℕ :=
  rawCellDegree (liveCoordinates t e) ((rawCells enum (liveCoordinates t e)).get
    (activeIndex (compactProductPack enum (liveCoordinates t e) (liveOperand t e source)) r))

theorem liveActive_degree_le (source : Fin N → K) (r : LiveActive t enum e source) :
    liveActiveDegree t enum e source r ≤ N :=
  rawCellDegree_le _ _

theorem liveActive_card (source : Fin N → K) (r : LiveActive t enum e source) :
    Fintype.card (LiveActiveField t enum e source r) = Fintype.card K ^ liveActiveDegree t enum e source r :=
  compact_card _ _

theorem liveActive_degree_pos (source : Fin N → K) (r : LiveActive t enum e source) :
    0 < liveActiveDegree t enum e source r := by
  by_contra! h
  have hz : (0 : LiveActiveField t enum e source r) = 1 := by
    apply (TableWord.wordEquiv _).injective
    funext i
    have hi : i.val < liveActiveDegree t enum e source r := i.isLt
    omega
  exact zero_ne_one hz

section Equations

variable {X : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
  (P : ∀ i v, (D i v → K) ≃ₗ[K] X i v)
  (hOne : ∀ i v, P i v (t i v).one = 1)
  (hMul : ∀ i v a b, P i v ((t i v).multiply a b) = P i v a * P i v b)

/-- The same source-mode variables act in every emitted live field cell. -/
theorem liveCellRatios_iff (source target : Fin N → K) (x : ∀ i v, (X i v)ˣ) :
    (∏ i : Fin d, liveMode t P hOne hMul i (fun v => (x i v : X i v))) *
        liveOperand t e source = liveOperand t e target ↔
      ∃ c : ∀ r : LiveActive t enum e source, (LiveActiveField t enum e source r)ˣ,
        liveCellRatios t enum e source target = some c ∧
        ∀ r, (∏ i : Fin d, selectedValue (rawModeIncidence enum (liveCoordinates t e)
          (liveMode t P hOne hMul)) x
          (activeIndex (compactProductPack enum (liveCoordinates t e) (liveOperand t e source)) r) i) = c r :=
  rawRows_iff enum (liveCoordinates t e) (liveMode t P hOne hMul) _ _ x

end Equations

#print axioms liveCellRatios
#print axioms liveCellRatios_none_iff
#print axioms liveActive_degree_le
#print axioms liveActive_degree_pos
#print axioms liveCellRatios_iff

end EvenTI.CellPreparation
