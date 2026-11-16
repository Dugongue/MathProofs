import Mathproof.MinimumGenerationOuterCayleyQuery
import Mathproof.MinimumGenerationTrialInstall

namespace Mathproof.MinimumGeneration.OuterCayleyQuery

open SearchTransducer

set_option backward.isDefEq.respectTransparency false

def solverLayout : Fin solver.workTapes ↪ Fin 16 :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun i : Fin 16 => i.val) h)⟩

private def signedIndex (i : Fin solver.workTapes) :
    Fin ReingoldLiveInput.signedTrialMachine.workTapes := Fin.castLE (by decide) i

private theorem signedIndex_cells (n x y label : Nat) (prior : List Bool)
    (i : Fin solver.workTapes) :
    (ReingoldLiveInput.signedTrialStart n x y label prior).workCell (signedIndex i) =
      (LiveInverse.start n x y prior).workCell i := by
  let e : Fin solver.workTapes ↪ Fin 10 :=
    ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun z : Fin 10 => z.val) h)⟩
  change (solver.bankConfig e (LiveInverse.start n x y prior) (fun _ => 0)
    (fun _ => InputPosition.work (encodeLabel (TableIO.width n) label))).workCell (e i) = _
  exact solver.bankConfig_cell_image e _ _ _ i

/-- The existing signed-trial installer also prepares exactly the nine live
quotient banks. Its spare trial label stays available to the later predicate. -/
theorem preparedEntry {n : Nat} (G : Group (Fin n)) (x y label : Fin n) (p : Nat)
    (P : SearchTransducer) (testBanks : Fin P.workTapes ↪ Fin 16)
    (prior : List Bool) (cells : Fin 16 → Int → Option Bool)
    (hCells : TrialInstall.Prepared n x.val y.val label.val cells)
    (hInput : p ≤ (@encodeCayley n G.toMul).length) :
    let I := TrialInstall.prepareMachine
    let M := machine P solverLayout testBanks
    let id : Fin 16 ↪ Fin 16 := Function.Embedding.refl _
    let raw := @encodeCayley n G.toMul
    ∃ (k : Nat) (d : I.Config),
      I.BoundedSegment raw (2 * TableIO.width n + 1) (TrialInstall.prepareStart p cells prior) d k ∧
      I.step raw d = none ∧
      thenEntry I M id id (I.bankConfig id d d.workHead d.workCell) =
        M.bankConfig id (entry P solverLayout testBanks n x.val y.val prior d.workHead d.workCell)
          d.workHead d.workCell ∧
      d.workHead = (fun _ => 0) ∧
      ∀ i : Fin 16, 10 ≤ i.val → d.workCell i = cells i := by
  let I := TrialInstall.prepareMachine
  let M := machine P solverLayout testBanks
  let id : Fin 16 ↪ Fin 16 := Function.Embedding.refl _
  obtain ⟨d, segment, halt, input, heads, output, layout, frame⟩ :=
    TrialInstall.prepare G.toMul x y label p prior cells hCells hInput
  refine ⟨_, d, segment, halt, ?_, heads, frame⟩
  let c := entry P solverLayout testBanks n x.val y.val prior d.workHead d.workCell
  let lifted := M.bankConfig id c d.workHead d.workCell
  have hc : c.workCell = d.workCell := by
    funext j
    by_cases hj : j ∈ Set.range solverLayout
    · obtain ⟨i,rfl⟩ := hj
      change (solver.bankConfig solverLayout (LiveInverse.start n x.val y.val prior)
        d.workHead d.workCell).workCell (solverLayout i) = d.workCell (solverLayout i)
      rw [bankConfig_cell_image]
      have ix : solverLayout i = TrialInstall.trialBanks (signedIndex i) := rfl
      rw [ix, layout, signedIndex_cells]
    · exact (solver.bankConfig_frame solverLayout _ d.workHead d.workCell hj).2
  have hh : c.workHead = d.workHead := by
    funext j
    by_cases hj : j ∈ Set.range solverLayout
    · obtain ⟨i,rfl⟩ := hj
      change (solver.bankConfig solverLayout (LiveInverse.start n x.val y.val prior)
        d.workHead d.workCell).workHead (solverLayout i) = d.workHead (solverLayout i)
      rw [bankConfig_head_image, heads]
      fin_cases i <;> rfl
    · exact (solver.bankConfig_frame solverLayout _ d.workHead d.workCell hj).1
  have hLiftCells : lifted.workCell = d.workCell := by
    funext i
    exact (M.bankConfig_cell_image id c d.workHead d.workCell i).trans (congrFun hc i)
  have hLiftHeads : lifted.workHead = d.workHead := by
    funext i
    exact (M.bankConfig_head_image id c d.workHead d.workCell i).trans (congrFun hh i)
  let left := I.bankConfig id d d.workHead d.workCell
  have hLeftCells : left.workCell = d.workCell := by
    funext i
    exact I.bankConfig_cell_image id d d.workHead d.workCell i
  have hLeftHeads : left.workHead = d.workHead := by
    funext i
    exact I.bankConfig_head_image id d d.workHead d.workCell i
  change ⟨M.initialState, d.inputHead, left.workHead, left.workCell, d.outputReversed⟩ = lifted
  rw [hLeftCells, hLeftHeads, ← hLiftCells, ← hLiftHeads, output, input]
  rfl

end Mathproof.MinimumGeneration.OuterCayleyQuery
