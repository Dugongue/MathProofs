import Mathproof.MinimumGenerationCayleyPrefixPrepared
import Mathproof.MinimumGenerationCayleyQueryDispatchInstall

namespace Mathproof.MinimumGeneration.CayleyPrefixLeaf

open SearchTransducer
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

private def copyOne {W : Nat} (dst src : Fin W) (i : Fin W) : Option (Fin W) :=
  if i = dst then some src else none

private def sameBanks (W : Nat) : Fin W ↪ Fin W := Function.Embedding.refl _

variable {W : Nat} (e : Fin 18 ↪ Fin W) (leftSource rightSource : Fin W)

private abbrev copyRow := TapeInstall.machine (e 11) (copyOne (e 12) leftSource)
private abbrev copyTarget := TapeInstall.machine (e 14) (copyOne (e 15) rightSource)

abbrev endpointsMachine :=
  thenMachine (copyRow e leftSource) (copyTarget e rightSource) (sameBanks W) (sameBanks W)

private def afterRow (n : Nat) (cells : Fin W → Int → Option Bool) :=
  TapeInstall.installed (copyOne (e 12) leftSource) cells (2 * TableIO.width n)

def endpointsInstalled (n : Nat) (cells : Fin W → Int → Option Bool) :=
  TapeInstall.installed (copyOne (e 15) rightSource) (afterRow e leftSource n cells) (TableIO.width n)

def endpointsStart (n : Nat) (cells : Fin W → Int → Option Bool) (prior : List Bool) :
    (endpointsMachine e leftSource rightSource).Config :=
  let c := TapeInstall.start (e 11) (copyOne (e 12) leftSource) (↑(n+1 : Nat)) cells prior
  thenLeft (copyRow e leftSource) (copyTarget e rightSource) (sameBanks W) (sameBanks W)
    ((copyRow e leftSource).bankConfig (sameBanks W) c c.workHead c.workCell)

private theorem configs {M : SearchTransducer} (c d : M.Config)
    (s : c.state = d.state) (i : c.inputHead = d.inputHead) (h : c.workHead = d.workHead)
    (t : c.workCell = d.workCell) (o : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem freezeRow (n : Nat) (cells : Fin W → Int → Option Bool)
    {i : Fin W} (hne : i ≠ e 12) : afterRow e leftSource n cells i = cells i :=
  TapeInstall.installed_source _ _ _ _ (by simp [copyOne, hne])

theorem endpointsOutside (n : Nat) (cells : Fin W → Int → Option Bool)
    {i : Fin W} (rowNe : i ≠ e 12) (targetNe : i ≠ e 15) :
    endpointsInstalled e leftSource rightSource n cells i = cells i :=
  (TapeInstall.installed_source _ _ _ _ (by simp [copyOne, targetNe])).trans
    (freezeRow e leftSource n cells rowNe)

private theorem port_ne {i j : Fin 18} (h : i ≠ j) : e i ≠ e j := fun eq => h (e.injective eq)

private theorem interval {n : Nat} (M : Mul (Fin n)) :
    (-1 : Int) ≤ (↑(n+1 : Nat) : Int) ∧ (↑(n+1 : Nat) : Int) ≤ (@encodeCayley n M).length := by
  refine ⟨by omega, ?_⟩
  have h : n+1 ≤ (@encodeCayley n M).length := by
    rw [@length_encodeCayley n M]
    omega
  exact_mod_cast h

/-- Install the wide row and narrow target from the live endpoint banks. -/
theorem executeEndpointCopies {n : Nat} (M : Mul (Fin n))
    (width x y : Nat) (wide : 2 * TableIO.width n ≤ width)
    (cells : Fin W → Int → Option Bool) (prior : List Bool)
    (clockRow : cells (e 11) = work (encodeLabel (2 * TableIO.width n) 0))
    (clockTarget : cells (e 14) = work (encodeLabel (TableIO.width n) 0))
    (rowValue : cells leftSource = work (encodeLabel width x))
    (targetValue : cells rightSource = work (encodeLabel width y))
    (targetOutsideRow : rightSource ≠ e 12)
    (cleanRow : ∀ p : Int, p < 1 ∨ (2 * TableIO.width n : Nat) < p → cells (e 12) p = none)
    (cleanTarget : ∀ p : Int, p < 1 ∨ (TableIO.width n : Nat) < p → cells (e 15) p = none) :
    let word := @encodeCayley n M
    let P := endpointsMachine e leftSource rightSource
    ∃ k d, P.BoundedSegment word (2 * TableIO.width n+1)
      (endpointsStart e leftSource rightSource n cells prior) d k ∧
      P.step word d = none ∧ d.inputHead = (↑(n+1 : Nat) : Int) ∧ d.outputReversed = prior ∧
      d.workHead = (fun _ => 0) ∧ d.workCell = endpointsInstalled e leftSource rightSource n cells ∧
      d.workCell (e 12) = work (encodeLabel (2 * TableIO.width n) x) ∧
      d.workCell (e 15) = work (encodeLabel (TableIO.width n) y) := by
  let word := @encodeCayley n M
  let p : Int := ↑(n+1 : Nat)
  let w := TableIO.width n
  let A := copyRow e leftSource
  let B := copyTarget e rightSource
  let E := sameBanks W
  let rowMap := copyOne (e 12) leftSource
  let targetMap := copyOne (e 15) rightSource
  let rowCells := afterRow e leftSource n cells
  let newCells := endpointsInstalled e leftSource rightSource n cells
  have rowClockFixed : rowMap (e 11) = none :=
    by simp [rowMap, copyOne, port_ne e (by decide : (11 : Fin 18) ≠ 12)]
  have targetClockFixed : targetMap (e 14) = none :=
    by simp [targetMap, copyOne, port_ne e (by decide : (14 : Fin 18) ≠ 15)]
  have ctl : rowCells (e 14) = work (encodeLabel w 0) :=
    (freezeRow e leftSource n cells (port_ne e (by decide : (14 : Fin 18) ≠ 12))).trans clockTarget
  obtain ⟨hA, stopA⟩ := TapeInstall.execute (e 11) rowMap rowClockFixed word
    (encodeLabel (2*w) 0) prior p cells clockRow (interval M)
  obtain ⟨hB, stopB⟩ := TapeInstall.execute (e 14) targetMap targetClockFixed word
    (encodeLabel w 0) prior p rowCells ctl (interval M)
  rw [length_encodeLabel] at hA stopA hB stopB
  let c := TapeInstall.start (e 11) rowMap p cells prior
  let m := TapeInstall.stop (e 11) rowMap p cells prior (2*w)
  let v := TapeInstall.start (e 14) targetMap p rowCells prior
  let z := TapeInstall.stop (e 14) targetMap p rowCells prior w
  let parked : Fin W → Int := fun _ => 0
  let mid := A.bankConfig E m parked cells
  let next := B.bankConfig E v parked rowCells
  let last := B.bankConfig E z parked rowCells
  have relocatedA := A.relocateBanks_segment E hA (heads := parked) (cells := cells) (by simp [parked])
  have relStopA : (A.relocateBanks E).step word mid = none := by
    unfold mid
    rw [relocateBanks_step, stopA]
    rfl
  have widened := PhysicalEntry.segment_mono hB (show w+1 ≤ 2*w+1 by omega)
  have relocatedB := B.relocateBanks_segment E widened (heads := parked) (cells := rowCells)
    (by simp [parked])
  have joined : thenEntry A B E E mid = next := by
    apply configs (thenEntry A B E E mid) next rfl rfl _ _ rfl
    · funext j
      exact (A.bankConfig_head_image E m parked cells j).trans
        (B.bankConfig_head_image E v parked rowCells j).symm
    · funext j
      exact (A.bankConfig_cell_image E m parked cells j).trans
        (B.bankConfig_cell_image E v parked rowCells j).symm
  change (B.relocateBanks E).BoundedSegment word (2*w+1) next last _ at relocatedB
  rw [← joined] at relocatedB
  let d := thenRight A B E E last
  have hCells : d.workCell = newCells := by
    funext j
    exact B.bankConfig_cell_image E z parked rowCells j
  refine ⟨_, d, thenSegment A B E E relocatedA relStopA relocatedB, ?_, rfl, rfl, ?_, hCells, ?_, ?_⟩
  · change (endpointsMachine e leftSource rightSource).step word (thenRight A B E E last) = none
    rw [thenStep_right]
    unfold last
    rw [relocateBanks_step, stopB]
    rfl
  · funext j
    exact B.bankConfig_head_image E z parked rowCells j
  · rw [hCells]
    have h := TapeInstall.installed_source targetMap rowCells w (e 12)
      (by simp [targetMap, copyOne, port_ne e (by decide : (12 : Fin 18) ≠ 15)])
    refine h.trans ?_
    exact CayleyQueryDispatch.installedLabel rowMap cells (e 12) leftSource wide rowValue
      (by simp [rowMap, copyOne]) cleanRow
  · rw [hCells]
    have hValue := (freezeRow e leftSource n cells targetOutsideRow).trans targetValue
    have hClean : ∀ p, p < 1 ∨ (w : Int) < p → rowCells (e 15) p = none := by
      change ∀ p, p < 1 ∨ (w : Int) < p → afterRow e leftSource n cells (e 15) p = none
      rw [freezeRow e leftSource n cells (port_ne e (by decide : (15 : Fin 18) ≠ 12))]
      exact cleanTarget
    exact CayleyQueryDispatch.installedLabel targetMap rowCells (e 15) rightSource
      (by omega : w ≤ width) hValue (by simp [targetMap, copyOne]) hClean

end Mathproof.MinimumGeneration.CayleyPrefixLeaf
