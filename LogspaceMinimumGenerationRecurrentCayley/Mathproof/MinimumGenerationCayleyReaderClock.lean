import Mathproof.MinimumGenerationPhysicalGreedyTemplateWidth
import Mathproof.MinimumGenerationCayleyReaderRestore

namespace Mathproof.MinimumGeneration.CayleyReaderClock

open SearchTransducer InputScan
open CayleyQueryPrefixModel (width rawSpace)

abbrev T := PhysicalGreedyTemplateWidth.machine

def bits (n : Nat) : List Bool := encodeLabel (16 * TableIO.width n) 0

abbrev machine {W : Nat} (banks : Fin 3 ↪ Fin W) := T.relocateBanks banks

def start {W : Nat} (banks : Fin 3 ↪ Fin W) (p : Int) (prior : List Bool)
    (cells : Fin W → Int → Option Bool) : (machine banks).Config :=
  ⟨T.initialState,p,fun _ => 0,cells,prior⟩

/-- Create the common reset clock in its final bank, from a preserved four-label
source, a four-label zero bank, and a blank destination. The remaining banks
are untouched. -/
theorem execute {W n : Nat} (G : Group (Fin n)) (banks : Fin 3 ↪ Fin W)
    (p : Int) (prior src : List Bool) (cells : Fin W → Int → Option Bool)
    (pBound : (-1 : Int) ≤ p ∧ p ≤ (@encodeCayley n G.toMul).length)
    (hLen : src.length = width n)
    (hSrc : cells (banks 0) = InputPosition.work src)
    (hMid : cells (banks 1) = InputPosition.work (encodeLabel (width n) 0))
    (hDst : cells (banks 2) = fun _ => none) :
    ∃ k d, (machine banks).BoundedSegment (@encodeCayley n G.toMul)
      ((bits n).length + 1) (start banks p prior cells) d k ∧
      (machine banks).step (@encodeCayley n G.toMul) d = none ∧
      d.inputHead = p ∧ d.outputReversed = prior ∧ d.workHead = (fun _ => 0) ∧
      d.workCell (banks 0) = cells (banks 0) ∧
      d.workCell (banks 1) = InputPosition.work (encodeLabel (8 * TableIO.width n) 0) ∧
      d.workCell (banks 2) = InputPosition.work (bits n) ∧
      (∀ j ∉ Set.range banks, d.workCell j = cells j) ∧
      rawSpace (@encodeCayley n G.toMul) ≤ (bits n).length := by
  let w := width n
  let a := PhysicalGreedyTemplateWidth.start p src prior w
  have h8 : 2*w = 8 * TableIO.width n := by unfold w width; omega
  have h16 : 4*w = 16 * TableIO.width n := by unfold w width; omega
  obtain ⟨k,b,run,halt,heads,inp,out,res⟩ :=
    PhysicalGreedyTemplateWidth.execute (@encodeCayley n G.toMul) src prior p w hLen pBound
  change T.BoundedSegment _ _ a b k at run
  let lift := fun q : T.Config => T.bankConfig banks q (fun _ => 0) cells
  have input : lift a = start banks p prior cells := by
    have aHead : a.workHead = (fun _ => 0) := rfl
    have aCell : a.workCell = PhysicalGreedyTemplateWidth.content src (encodeLabel w 0) [] := rfl
    have fullHeads : (lift a).workHead = (fun _ => 0) := by
      funext i
      by_cases part : i ∈ Set.range banks
      · obtain ⟨j,rfl⟩ := part
        rw [T.bankConfig_head_image,aHead]
      · exact (T.bankConfig_frame banks a _ cells part).1
    have fullCells : (lift a).workCell = cells := by
      funext i
      by_cases part : i ∈ Set.range banks
      · obtain ⟨j,rfl⟩ := part
        rw [T.bankConfig_cell_image,aCell]
        fin_cases j
        · change counterTape 0 src = cells (banks 0)
          rw [hSrc]; exact HeaderSetup.counterTape_eq_marked _
        · change counterTape 0 (encodeLabel w 0) = cells (banks 1)
          rw [hMid]; exact HeaderSetup.counterTape_eq_marked _
        · change counterTape 0 [] = cells (banks 2)
          rw [hDst, HeaderSetup.counterTape_eq_marked]
          funext z
          simp [InputPosition.work]
      · exact (T.bankConfig_frame banks a _ cells part).2
    change lift a = ⟨(lift a).state,(lift a).inputHead,(fun _ => 0),cells,(lift a).outputReversed⟩
    conv_rhs => rw [← fullHeads, ← fullCells]
  have runLift := T.relocateBanks_segment banks run
    (heads := fun _ => 0) (cells := cells) (by simp)
  change (machine banks).BoundedSegment _ _ (lift a) (lift b) k at runLift
  rw [input,h16,← show (bits n).length = 16 * TableIO.width n from length_encodeLabel _ _] at runLift
  refine ⟨k,lift b,runLift,?_,inp,out,?_,?_,?_,?_,?_,?_⟩
  · change (T.relocateBanks banks).step _ (T.bankConfig banks b _ _) = _
    rw [T.relocateBanks_step,halt]
    rfl
  · funext i
    by_cases part : i ∈ Set.range banks
    · obtain ⟨j,rfl⟩ := part
      rw [T.bankConfig_head_image,heads]
    · exact (T.bankConfig_frame banks b _ cells part).1
  · rw [T.bankConfig_cell_image,res,hSrc]
    exact HeaderSetup.counterTape_eq_marked _
  · rw [T.bankConfig_cell_image,res,← h8]
    exact HeaderSetup.counterTape_eq_marked _
  · rw [T.bankConfig_cell_image,res]
    change counterTape 0 (encodeLabel (4*w) 0) = InputPosition.work (bits n)
    rw [h16]
    exact HeaderSetup.counterTape_eq_marked _
  · intro j part
    exact (T.bankConfig_frame banks b _ cells part).2
  · rw [show (bits n).length = 16 * TableIO.width n from length_encodeLabel _ _]
    exact CayleyReaderRestore.resetClockEnough G

end Mathproof.MinimumGeneration.CayleyReaderClock
