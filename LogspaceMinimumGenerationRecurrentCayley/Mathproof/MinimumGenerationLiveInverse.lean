import Mathproof.MinimumGenerationPhysicalInverse
import Mathproof.MinimumGenerationStrideSkip
import Mathproof.MinimumGenerationTapeMultiply

namespace Mathproof.MinimumGeneration.LiveInverse

open SearchTransducer
open InputPosition (cfg digits work)
open StrideSkip (strideSkip liftedConfig)
open PhysicalEntry (segment_mono)

private def strideBanks : Fin strideSkip.workTapes ↪ Fin 4 :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun x : Fin 4 => x.val) h)⟩

private def scanBanks : Fin PhysicalInverse.machine.workTapes ↪ Fin 4 :=
  ⟨Fin.succ, fun _ _ h => Fin.ext (Nat.add_right_cancel (congrArg (fun x : Fin 4 => x.val) h))⟩

private def positionMachine : SearchTransducer :=
  thenMachine strideSkip PhysicalInverse.machine strideBanks scanBanks

private def frame (identity candidate : List Bool) (i : Fin 4) : Int → Option Bool :=
  if i = 2 then work identity else work candidate

private def padStride (c : strideSkip.Config) (identity candidate : List Bool) :
    (strideSkip.relocateBanks strideBanks).Config :=
  strideSkip.bankConfig strideBanks c (fun _ => 0) (frame identity candidate)

private def positionStart (n : ℕ) (count identity : List Bool) (prior : List Bool) :
    positionMachine.Config :=
  let w := TableIO.width n
  let zeros := List.replicate w false
  thenLeft strideSkip PhysicalInverse.machine strideBanks scanBanks
    (padStride (liftedConfig (n + 1 : ℕ) zeros (cfg count 0 0 0 prior))
      identity (encodeLabel w 0))

private theorem bankConfig_heads_zero (P : SearchTransducer) {W : Nat}
    (e : Fin P.workTapes ↪ Fin W) (c : P.Config) (heads : Fin W → Int)
    (cells : Fin W → Int → Option Bool) (hc : c.workHead = (fun _ => 0))
    (hf : heads = (fun _ => 0)) :
    (P.bankConfig e c heads cells).workHead = (fun _ => 0) := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    rw [bankConfig_head_image, hc]
  · rw [(bankConfig_frame P e c heads cells hj).1, hf]
private theorem rowCount_lt (n : ℕ) (row : Fin n) :
    row.val * n < 2 ^ (2 * TableIO.width n) := by
  have positive : 0 < n := Nat.zero_lt_of_lt row.isLt
  have cap : n < 2 ^ TableIO.width n := Nat.lt_log2_self
  rw [Nat.mul_comm 2, Nat.pow_mul, Nat.pow_two]
  exact (Nat.mul_lt_mul_of_pos_right row.isLt positive).trans_le
    (Nat.mul_le_mul (Nat.le_of_lt cap) (Nat.le_of_lt cap))

private theorem positionAndScan (n : ℕ) (G : Group (Fin n)) (row target goal : Fin n)
    (mulGoal : G.toMul.mul row goal = target) (prior : List Bool) :
    let w := TableIO.width n
    let word := @encodeCayley n G.toMul
    let count := encodeLabel (2 * w) (row.val * n)
    let identity := encodeLabel w target.val
    ∃ (k : ℕ) (result : positionMachine.Config),
      positionMachine.BoundedSegment word (2 * w + 1) (positionStart n count identity prior) result k ∧
      positionMachine.step word result = none ∧
      result.workCell ⟨3, by decide⟩ = work (encodeLabel w goal.val) ∧
      result.outputReversed = prior ∧ result.workHead = (fun _ => 0) := by
  let w := TableIO.width n
  let word := @encodeCayley n G.toMul
  let count := encodeLabel (2 * w) (row.val * n)
  let identity := encodeLabel w target.val
  let zeros := List.replicate w false
  let candidate := encodeLabel w 0
  let rowCursor := TableIO.offset n row.val 0
  have hCount : digits count = row.val * n := InputPosition.digits_encodeLabel _ _ (rowCount_lt n row)
  have hWidth : count.length = 2 * w := length_encodeLabel _ _
  have hZero : zeros.length = w := List.length_replicate
  have hOff : n + 1 + zeros.length * digits count = rowCursor := by
    rw [hZero, hCount]
    simp [rowCursor, TableIO.offset, w, Nat.mul_comm]
  have hReach : n + 1 + zeros.length * digits count ≤ word.length := by
    rw [hOff]
    have h := @TableIO.tableAddress_lt_inputLength n G.toMul row
      ⟨0, Nat.zero_lt_of_lt row.isLt⟩ 0 (by simp [TableIO.width])
    exact Nat.le_of_lt h
  obtain ⟨k, done, _, hStride, stopStride⟩ :=
    StrideSkip.skipStride_bounded word count zeros prior (n + 1) hReach
  let s := liftedConfig (n + 1 : ℕ) zeros (cfg count 0 0 0 prior)
  let d := StrideSkip.config (5 : Fin 13)
    ((↑(n + 1) : Int) + (zeros.length : Int) * (digits count : Int))
    0 0 (work done) zeros prior
  have hBound : max count.length zeros.length + 1 ≤ 2 * w + 1 := by
    rw [hWidth, hZero, max_eq_left (by omega : w ≤ 2 * w)]
  change strideSkip.BoundedSegment word (max count.length zeros.length + 1) s d k at hStride
  change strideSkip.step word d = none at stopStride
  have hSeg : (strideSkip.relocateBanks strideBanks).BoundedSegment word (2 * w + 1)
      (padStride s identity candidate) (padStride d identity candidate) k :=
    relocateBanks_segment strideSkip strideBanks (segment_mono hStride hBound)
      (heads := fun _ => 0) (cells := frame identity candidate) (by simp)
  let mid := padStride d identity candidate
  have hStop : (strideSkip.relocateBanks strideBanks).step word mid = none := by
    unfold mid padStride
    rw [relocateBanks_step, stopStride]
    rfl
  let scan := PhysicalInverse.machine
  let scanStart := PhysicalInverse.stages.tag 0
    (PhysicalInverse.entry rowCursor zeros identity candidate prior)
  obtain ⟨i, scanEnd, hScan, scanStop, hResult, hOut, hScanHeads⟩ := PhysicalInverse.physicalRightSolve_layout n G row target goal mulGoal prior
  have hScan' : scan.BoundedSegment word (2 * w + 1) scanStart scanEnd i :=
    segment_mono hScan (by omega : w + 1 ≤ 2 * w + 1)
  have hScanLift := relocateBanks_segment scan scanBanks hScan'
    (heads := fun _ => 0) (cells := fun _ => work done) (by simp)
  let scanIn := scan.bankConfig scanBanks scanStart (fun _ => 0) (fun _ => work done)
  let scanOut := scan.bankConfig scanBanks scanEnd (fun _ => 0) (fun _ => work done)
  have hHandoff : thenEntry strideSkip scan strideBanks scanBanks mid = scanIn := by
    have hh : mid.workHead = scanIn.workHead := by
      funext t
      fin_cases t <;> rfl
    have hc : mid.workCell = scanIn.workCell := by
      funext t
      fin_cases t <;> rfl
    have hi : mid.inputHead = (rowCursor : Int) := by
      change ((↑(n + 1) : Int) + (zeros.length : Int) * (digits count : Int)) = (rowCursor : Int)
      exact_mod_cast hOff
    change (⟨scan.initialState, mid.inputHead, mid.workHead, mid.workCell, prior⟩ :
      (scan.relocateBanks scanBanks).Config) = scanIn
    rw [hi, hh, hc]
    rfl
  change (scan.relocateBanks scanBanks).BoundedSegment word (2 * w + 1) scanIn scanOut i at hScanLift
  rw [← hHandoff] at hScanLift
  have hScanStop : (scan.relocateBanks scanBanks).step word scanOut = none := by
    unfold scanOut
    rw [relocateBanks_step, scanStop]
    rfl
  let result := thenRight strideSkip scan strideBanks scanBanks scanOut
  refine ⟨k + 1 + i, result, thenSegment strideSkip scan strideBanks scanBanks hSeg hStop hScanLift,
    ?_, ?_, hOut, ?_⟩
  · change (thenMachine strideSkip scan strideBanks scanBanks).step word
      (thenRight strideSkip scan strideBanks scanBanks scanOut) = none
    rw [thenStep_right, hScanStop]
    rfl
  · exact (bankConfig_cell_image scan scanBanks scanEnd (fun _ => 0) (fun _ => work done)
      ⟨2, by decide⟩).trans hResult
  · exact bankConfig_heads_zero scan scanBanks scanEnd (fun _ => 0) (fun _ => work done) hScanHeads rfl


private def mulBanks : Fin TapeMultiply.machine.workTapes ↪ Fin 9 :=
  ⟨Fin.castLE (by decide), fun i j h => Fin.ext (congrArg (fun x : Fin 9 => x.val) h)⟩

private def positionBanks : Fin positionMachine.workTapes ↪ Fin 9 := by
  change Fin 4 ↪ Fin 9
  refine ⟨fun i => ⟨if i.val = 0 then 0 else i.val + 5, ?_⟩, ?_⟩
  · have hi := i.isLt
    split <;> omega
  · intro i j h
    have hval := congrArg (fun k : Fin 9 => k.val) h
    change (if i.val = 0 then 0 else i.val + 5) = (if j.val = 0 then 0 else j.val + 5) at hval
    exact Fin.ext (by split at hval <;> split at hval <;> omega)

/-- Compute a row cursor from live labels, then scan the corresponding row
for the inverse. All components execute on the same physical input. -/
def machine : SearchTransducer :=
  thenMachine TapeMultiply.machine positionMachine mulBanks positionBanks

private def mulFrame (w : ℕ) (identity : List Bool) (i : Fin 9) : Int → Option Bool :=
  if i = 6 then work (List.replicate w false)
  else if i = 7 then work identity else work (encodeLabel w 0)

private def padMul (c : TapeMultiply.machine.Config) (w : ℕ) (identity : List Bool) :
    (TapeMultiply.machine.relocateBanks mulBanks).Config :=
  TapeMultiply.machine.bankConfig mulBanks c (fun _ => 0) (mulFrame w identity)

/-- Prepared live data at the payload boundary. The row and order are in
fixed-width arithmetic banks, and the identity is in the saved label bank.
No row address or table slice is supplied. -/
def start (n row identity : ℕ) (prior : List Bool) : machine.Config :=
  let w := TableIO.width n
  thenLeft TapeMultiply.machine positionMachine mulBanks positionBanks
    (padMul (TapeMultiply.startConfig (2 * w) 0 row n 0 (↑(n + 1) : Int) prior) w
      (encodeLabel w identity))

private theorem register_eq_work (w value : ℕ) :
    TapeAddition.register w value = work (encodeLabel w value) := by
  funext p
  by_cases h : p ≤ 0
  · simp [TapeAddition.register, work, h, show p < 1 by omega]
  · simp [TapeAddition.register, work, h, show ¬ p < 1 by omega]

/-- From the live row, order and saved target registers, find the unique
right solution in bank eight with a logarithmic work bound in the raw input length. -/
theorem executeRightSolve (n : ℕ) (G : Group (Fin n)) (row target goal : Fin n)
    (mulGoal : G.toMul.mul row goal = target) (prior : List Bool) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    ∃ (k : ℕ) (result : machine.Config),
      machine.BoundedSegment word (3 * (Nat.log2 (word.length + 1) + 1))
        (start n row.val target.val prior) result k ∧
      machine.step word result = none ∧
      result.workCell ⟨8, by decide⟩ = work (encodeLabel w goal.val) ∧
      result.outputReversed = prior ∧ result.workHead = (fun _ => 0) := by
  let word := @encodeCayley n G.toMul
  let w := TableIO.width n
  let cap := Nat.log2 (word.length + 1) + 1
  let B := 3 * cap
  let identity := encodeLabel w target.val
  let count := encodeLabel (2 * w) (row.val * n)
  let A := (↑(n + 1) : Int)
  let midNative := TapeMultiply.stopConfig (2 * w) (0 + row.val * n) row.val n A prior
  let mid := padMul midNative w identity
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt row.isLt)
  have hlen : n + 1 ≤ word.length := by
    change n + 1 ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have hlog : n.log2 ≤ (word.length + 1).log2 := (Nat.le_log2 (by omega)).mpr
    ((Nat.log2_self_le hn).trans (by omega))
  have hwcap : w ≤ cap := Nat.add_le_add_right hlog 1
  have hwidth : 1 ≤ w := by simp [w, TableIO.width]
  have hw : 2 * w + 1 ≤ B := by dsimp only [B]; omega
  have hn2 : n < 2 ^ (2 * w) := (show n < 2 ^ w from Nat.lt_log2_self).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨hMultiply, stopMultiply⟩ := TapeMultiply.executeMultiply word prior A
    (2 * w) 0 row.val n 0 (by dsimp only [A]; omega) (row.isLt.trans hn2) hn2
  have multiplySeg : (TapeMultiply.machine.relocateBanks mulBanks).BoundedSegment word B
      (padMul (TapeMultiply.startConfig (2 * w) 0 row.val n 0 A prior) w identity)
      mid (TapeMultiply.multiplicationSteps (2 * w) row.val n) :=
    relocateBanks_segment TapeMultiply.machine mulBanks (segment_mono hMultiply hw)
      (heads := fun _ => 0) (cells := mulFrame w identity) (by simp)
  have multiplyStop : (TapeMultiply.machine.relocateBanks mulBanks).step word mid = none := by
    unfold mid padMul
    rw [relocateBanks_step, stopMultiply]
    rfl
  obtain ⟨k, c, hPosition, stopPosition, bits, output, hPositionHeads⟩ := positionAndScan n G row target goal mulGoal prior
  have hPositionLift := relocateBanks_segment positionMachine positionBanks
    (segment_mono hPosition hw) (heads := mid.workHead) (cells := mid.workCell) (by
      intro i _
      have hh : mid.workHead i = 0 := by fin_cases i <;> rfl
      simp [hh])
  let rightStart := positionMachine.bankConfig positionBanks (positionStart n count identity prior)
    mid.workHead mid.workCell
  let rightEnd := positionMachine.bankConfig positionBanks c mid.workHead mid.workCell
  have handoff : thenEntry TapeMultiply.machine positionMachine mulBanks positionBanks mid = rightStart := by
    have hh : mid.workHead = rightStart.workHead := by
      funext t
      fin_cases t <;> rfl
    have hc : mid.workCell = rightStart.workCell := by
      funext t
      fin_cases t
      · change TapeAddition.register (2 * w) (0 + row.val * n) = work count
        simp only [Nat.zero_add, count, register_eq_work]
      all_goals rfl
    exact congrArg₂ (fun h c => (⟨positionMachine.initialState, A, h, c, prior⟩ :
      (positionMachine.relocateBanks positionBanks).Config)) hh hc
  change (positionMachine.relocateBanks positionBanks).BoundedSegment word B rightStart rightEnd k at hPositionLift
  rw [← handoff] at hPositionLift
  have rightEndStop : (positionMachine.relocateBanks positionBanks).step word rightEnd = none := by
    unfold rightEnd
    rw [relocateBanks_step, stopPosition]
    rfl
  let result := thenRight TapeMultiply.machine positionMachine mulBanks positionBanks rightEnd
  refine ⟨_, result, thenSegment TapeMultiply.machine positionMachine mulBanks positionBanks
    multiplySeg multiplyStop hPositionLift, ?_, ?_, output, ?_⟩
  · change (thenMachine TapeMultiply.machine positionMachine mulBanks positionBanks).step word
      (thenRight TapeMultiply.machine positionMachine mulBanks positionBanks rightEnd) = none
    rw [thenStep_right, rightEndStop]
    rfl
  · exact (bankConfig_cell_image positionMachine positionBanks c mid.workHead mid.workCell
      ⟨3, by decide⟩).trans bits
  · have hMidHeads : mid.workHead = (fun _ => 0) := by
      funext i
      fin_cases i <;> rfl
    exact bankConfig_heads_zero positionMachine positionBanks c mid.workHead mid.workCell hPositionHeads hMidHeads

/-- From the live row, order and saved identity registers, compute the exact
inverse in bank eight with a logarithmic work bound in the raw input length. -/
theorem execute (n : ℕ) (G : Group (Fin n)) (row : Fin n) (prior : List Bool) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    ∃ (k : ℕ) (result : machine.Config),
      machine.BoundedSegment word (3 * (Nat.log2 (word.length + 1) + 1))
        (start n row.val G.toOne.one.val prior) result k ∧
      machine.step word result = none ∧
      result.workCell ⟨8, by decide⟩ = work (encodeLabel w (G.toInv.inv row).val) ∧
      result.outputReversed = prior := by
  let _ : Group (Fin n) := G
  obtain ⟨k, result, run, stop, bits, output, _⟩ :=
    executeRightSolve n G row G.toOne.one (G.toInv.inv row) (mul_inv_cancel row) prior
  exact ⟨k, result, run, stop, bits, output⟩

end Mathproof.MinimumGeneration.LiveInverse
