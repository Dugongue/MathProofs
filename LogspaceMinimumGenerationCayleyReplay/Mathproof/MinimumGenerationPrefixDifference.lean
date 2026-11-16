import Mathproof.MinimumGenerationReingoldLiveInput
import Mathproof.MinimumGenerationRankPhysicalSubtract

namespace Mathproof.MinimumGeneration.PrefixDifference

open SearchTransducer
open InputPosition (work)
open ReingoldLiveInput (difference liveDifference)

set_option backward.isDefEq.respectTransparency false

private abbrev solver := LiveInverse.machine
private abbrev subtractor := RankPhysicalSubtract.machine

private def solveBanks : Fin solver.workTapes ↪ Fin 10 :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun i : Fin 10 => i.val) h)⟩

private def subBanks : Fin subtractor.workTapes ↪ Fin 10 where
  toFun i := if i = 0 then 9 else 8
  inj' i j h := by
    change Fin 2 at i j
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction

abbrev machine := thenMachine solver subtractor solveBanks subBanks

private def parked : Fin 10 → Int := fun _ => 0

def start (n x y cut : Nat) (prior : List Bool) : machine.Config :=
  let frame : Fin 10 → Int → Option Bool := fun _ => work (encodeLabel (TableIO.width n) cut)
  thenLeft solver subtractor solveBanks subBanks
    (solver.bankConfig solveBanks (LiveInverse.start n x y prior) parked frame)

def below (c : machine.Config) : Bool :=
  decide (c.state.val = solver.states + (RankPhysicalSubtract.done true).val)

private theorem config_eq {M : SearchTransducer} (a b : M.Config)
    (s : a.state = b.state) (p : a.inputHead = b.inputHead) (h : a.workHead = b.workHead)
    (z : a.workCell = b.workCell) (o : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

private theorem thresholdOut : (9 : Fin 10) ∉ Set.range solveBanks := by
  rintro ⟨v,h⟩
  have e := congrArg (fun i : Fin 10 => i.val) h
  change v.val = 9 at e
  have hlt : v.val < 9 := v.isLt
  omega

/-- Compute the live right quotient, then return whether it is below the
supplied prefix threshold. Only the disposable quotient bank is subtracted into.
The cutoff remains available for a reversed-endpoint query. -/
theorem execute {n : Nat} (G : Group (Fin n)) (x y : Fin n) (cut : Nat) (hCut : cut ≤ n)
    (prior : List Bool) :
    let word := @encodeCayley n G.toMul
    let B := 3 * (Nat.log2 (word.length + 1) + 1)
    ∃ (k : Nat) (d : machine.Config),
      machine.BoundedSegment word B (start n x.val y.val cut prior) d k ∧
      machine.step word d = none ∧
      (below d = true ↔ (difference G x y).val < cut) ∧
      d.workHead = (fun _ => 0) ∧ d.outputReversed = prior ∧
      d.workCell 9 = work (encodeLabel (TableIO.width n) cut) := by
  let word := @encodeCayley n G.toMul
  let w := TableIO.width n
  let B := 3 * (Nat.log2 (word.length + 1) + 1)
  let p := encodeLabel w (difference G x y).val
  let q := encodeLabel w cut
  let initial : Fin 10 → Int → Option Bool := fun _ => work q
  obtain ⟨a, raw, hRun, hStop, hLabel, hOut, hHeads⟩ := liveDifference n G x y prior
  let mid := solver.bankConfig solveBanks raw parked initial
  have hLeft := solver.relocateBanks_segment solveBanks hRun (heads := parked) (cells := initial) (by simp [parked])
  have hLeftStop : (solver.relocateBanks solveBanks).step word mid = none := by
    unfold mid
    rw [solver.relocateBanks_step, hStop]
    rfl
  have hx : mid.workCell (8 : Fin 10) = work p :=
    (solver.bankConfig_cell_image solveBanks raw parked initial ⟨8,by decide⟩).trans hLabel
  have hy : mid.workCell (9 : Fin 10) = work q :=
    (solver.bankConfig_frame solveBanks raw parked initial thresholdOut).2
  have hMid : mid.workHead = parked := by
    funext i
    by_cases hi : i ∈ Set.range solveBanks
    · obtain ⟨j,rfl⟩ := hi
      exact (solver.bankConfig_head_image solveBanks raw parked initial j).trans (congrFun hHeads j)
    · exact (solver.bankConfig_frame solveBanks raw parked initial hi).1
  have hi : (-1 : Int) ≤ mid.inputHead ∧ mid.inputHead ≤ word.length :=
    ⟨(hRun.2 a le_rfl raw hRun.1).1, (hRun.2 a le_rfl raw hRun.1).2.1⟩
  have hn : n ≤ word.length := by
    change n ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have hlog : n.log2 ≤ (word.length + 1).log2 :=
    (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le (by have := x.isLt; omega)).trans (by omega))
  have hWidth : w+1 ≤ B := by dsimp [w, B, TableIO.width]; omega
  have hFit : n < 2^w := Nat.lt_log2_self
  obtain ⟨subtract, subtractStop⟩ :=
    RankPhysicalSubtract.execute_encoded word mid.outputReversed mid.inputHead w (difference G x y).val cut hi
      ((difference G x y).isLt.trans hFit) (hCut.trans_lt hFit)
  let entry := RankPhysicalSubtract.cfg 0 0 p q mid.outputReversed mid.inputHead
  let nativeEnd := RankPhysicalSubtract.cfg (RankPhysicalSubtract.done (decide ((difference G x y).val < cut)))
    0 (Lax51Proofs.RamToTM.subBits p q false) q mid.outputReversed mid.inputHead
  let subEntry := subtractor.bankConfig subBanks entry mid.workHead mid.workCell
  let subExit := subtractor.bankConfig subBanks nativeEnd mid.workHead mid.workCell
  have lifted := subtractor.relocateBanks_segment subBanks (PhysicalEntry.segment_mono subtract hWidth)
    (heads := mid.workHead) (cells := mid.workCell) (by simp [hMid, parked])
  have hJoin : thenEntry solver subtractor solveBanks subBanks mid = subEntry := by
    apply config_eq
    · rfl
    · rfl
    · funext i
      by_cases hh : i ∈ Set.range subBanks
      · obtain ⟨j,rfl⟩ := hh
        change mid.workHead (subBanks j) = _
        rw [hMid, show subEntry.workHead (subBanks j) = 0 from
          subtractor.bankConfig_head_image subBanks entry mid.workHead mid.workCell j]
        rfl
      · exact (subtractor.bankConfig_frame subBanks entry mid.workHead mid.workCell hh).1.symm
    · funext i
      by_cases hh : i ∈ Set.range subBanks
      · obtain ⟨j,rfl⟩ := hh
        change mid.workCell (subBanks j) = _
        rw [show subEntry.workCell (subBanks j) = entry.workCell j from
          subtractor.bankConfig_cell_image subBanks entry mid.workHead mid.workCell j]
        change Fin 2 at j
        fin_cases j
        · exact hy
        · exact hx
      · exact (subtractor.bankConfig_frame subBanks entry mid.workHead mid.workCell hh).2.symm
    · rfl
  change (subtractor.relocateBanks subBanks).BoundedSegment word B subEntry subExit _ at lifted
  rw [← hJoin] at lifted
  have srStop : (subtractor.relocateBanks subBanks).step word subExit = none := by
    unfold subExit nativeEnd
    rw [subtractor.relocateBanks_step, subtractStop]
    rfl
  let d := thenRight solver subtractor solveBanks subBanks subExit
  refine ⟨_, d, thenSegment solver subtractor solveBanks subBanks hLeft hLeftStop lifted,
    ?_, ?_, ?_, hOut, ?_⟩
  · change machine.step word (thenRight solver subtractor solveBanks subBanks subExit) = none
    rw [thenStep_right, srStop]
    rfl
  · have h : d.state.val =
        solver.states + (RankPhysicalSubtract.done (decide ((difference G x y).val < cut))).val := rfl
    change decide (d.state.val = solver.states + (RankPhysicalSubtract.done true).val) = true ↔ _
    rw [h]
    by_cases ha : (difference G x y).val < cut <;> simp [ha, RankPhysicalSubtract.done]
  · funext i
    change subExit.workHead i = 0
    by_cases hh : i ∈ Set.range subBanks
    · obtain ⟨j,rfl⟩ := hh
      exact subtractor.bankConfig_head_image subBanks nativeEnd mid.workHead mid.workCell j
    · exact ((subtractor.bankConfig_frame subBanks nativeEnd mid.workHead mid.workCell hh).1).trans
        (congrFun hMid i)
  · change subExit.workCell (subBanks 0) = _
    exact subtractor.bankConfig_cell_image subBanks nativeEnd mid.workHead mid.workCell 0

end Mathproof.MinimumGeneration.PrefixDifference
