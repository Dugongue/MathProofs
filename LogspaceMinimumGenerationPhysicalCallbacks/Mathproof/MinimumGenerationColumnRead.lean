import Mathproof.MinimumGenerationCountedRead
import Mathproof.MinimumGenerationTapeMultiply

namespace Mathproof.MinimumGeneration.ColumnRead

open SearchTransducer
open InputPosition (work)

private def mulBanks : Fin TapeMultiply.machine.workTapes ↪ Fin 7 :=
  ⟨Fin.castLE (by decide), fun i j h => Fin.ext (congrArg (fun z : Fin 7 => z.val) h)⟩

private def readBanks : Fin CountedRead.machine.workTapes ↪ Fin 7 where
  toFun i := if i.val = 0 then 0 else 6
  inj' i j h := by
    change Fin 2 at i j
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction

def machine : SearchTransducer :=
  thenMachine TapeMultiply.machine CountedRead.machine mulBanks readBanks

private def padMul (c : TapeMultiply.machine.Config) (template : List Bool) :
    (TapeMultiply.machine.relocateBanks mulBanks).Config :=
  TapeMultiply.machine.bankConfig mulBanks c (fun _ => 0) (fun _ => work template)

def start (n row col : ℕ) (prior : List Bool) : machine.Config :=
  let w := TableIO.width n
  thenLeft TapeMultiply.machine CountedRead.machine mulBanks readBanks
    (padMul (TapeMultiply.startConfig (2*w) col row n 0 (↑(n+1) : Int) prior)
      (List.replicate w false))

private theorem register_eq_work (w a : ℕ) :
    TapeAddition.register w a = work (encodeLabel w a) := by
  funext p
  by_cases h : p ≤ 0
  · simp [TapeAddition.register, work, h, show p < 1 by omega]
  · simp [TapeAddition.register, work, h, show ¬ p < 1 by omega]

/-- Read a multiplication-table entry directly from the live row, column and
order registers. The finite controller computes the row-major count on its
own work tape. It then advances by that count times the template width and
captures the product label in bank six. -/
theorem execute (n : ℕ) (M : Mul (Fin n)) (row col : Fin n) (prior : List Bool) :
    let word := @encodeCayley n M
    ∃ (t : ℕ) (c : machine.Config),
      machine.BoundedSegment word (3*(Nat.log2 (word.length + 1) + 1))
        (start n row.val col.val prior) c t ∧
      machine.step word c = none ∧ c.workCell ⟨6, by decide⟩ =
        work (encodeLabel (TableIO.width n) (M.mul row col).val) ∧
      c.outputReversed = prior := by
  let word := @encodeCayley n M
  let w := TableIO.width n
  let cap := Nat.log2 (word.length + 1) + 1
  let bound := 3*cap
  let template := List.replicate w false
  let addr := encodeLabel (2*w) (row.val*n+col.val)
  let C := TapeMultiply.stopConfig (2*w) (col.val+row.val*n) row.val n (↑(n+1) : Int) prior
  let mid := padMul C template
  have hlen : n + 1 ≤ word.length := by
    change n+1 ≤ (@encodeCayley n M).length
    rw [@length_encodeCayley n M]
    omega
  have hn : n ≠ 0 := by have h := row.isLt; omega
  have hw : 1 ≤ w := by simp [w, TableIO.width]
  have hlog : n.log2 ≤ (word.length+1).log2 := (Nat.le_log2 (by omega)).mpr
    ((Nat.log2_self_le hn).trans (by omega))
  have hwcap : w ≤ cap := Nat.add_le_add_right hlog 1
  have hwsmall : 2*w+1 ≤ bound := by
    dsimp only [bound]
    omega
  have hn2 : n < 2^(2*w) := (show n < 2^w from Nat.lt_log2_self).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hinput : (-1 : Int) ≤ (↑(n+1) : Int) ∧
      (↑(n+1) : Int) ≤ (word.length : Int) := by
    constructor
    · omega
    · exact_mod_cast hlen
  obtain ⟨hm, hmStop⟩ := TapeMultiply.executeMultiply word prior (↑(n+1) : Int)
    (2*w) col.val row.val n 0 hinput (row.isLt.trans hn2) hn2
  have h12 : (TapeMultiply.machine.relocateBanks mulBanks).BoundedSegment word bound
      (padMul (TapeMultiply.startConfig (2*w) col.val row.val n 0 (↑(n+1) : Int) prior) template)
      mid (TapeMultiply.multiplicationSteps (2*w) row.val n) :=
    relocateBanks_segment TapeMultiply.machine mulBanks (PhysicalEntry.segment_mono hm hwsmall)
      (heads := fun _ => 0) (cells := fun _ => work template) (by simp)
  have hhalt12 : (TapeMultiply.machine.relocateBanks mulBanks).step word mid = none := by
    unfold mid padMul
    rw [relocateBanks_step, hmStop]
    rfl
  obtain ⟨k,c,hc,hcStop,hr,hout⟩ := CountedRead.counted_cayley n M row col prior
  have h23 := relocateBanks_segment CountedRead.machine readBanks hc
    (heads := mid.workHead) (cells := mid.workCell) (by
      intro i _; change (mid.workHead i).natAbs ≤ bound
      have hh : mid.workHead i = 0 := by
        fin_cases i <;> rfl
      simp [hh])
  let readerIn := CountedRead.machine.bankConfig readBanks (CountedRead.start (n+1) addr template prior)
    mid.workHead mid.workCell
  have hhandoff : thenEntry TapeMultiply.machine CountedRead.machine mulBanks readBanks mid = readerIn := by
    have hheads : mid.workHead = readerIn.workHead := by
      funext i
      fin_cases i <;> rfl
    have hcells : mid.workCell = readerIn.workCell := by
      funext i
      fin_cases i
      · change TapeAddition.register (2*w) (col.val+row.val*n) = work addr
        rw [register_eq_work, Nat.add_comm]
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    exact congrArg₂ (fun h c => (⟨CountedRead.machine.initialState, (↑(n+1) : Int), h, c, prior⟩ :
      (CountedRead.machine.relocateBanks readBanks).Config)) hheads hcells
  change (CountedRead.machine.relocateBanks readBanks).BoundedSegment word bound readerIn _ k at h23
  rw [← hhandoff] at h23
  let finish := CountedRead.machine.bankConfig readBanks c mid.workHead mid.workCell
  have hfinish : (CountedRead.machine.relocateBanks readBanks).step word finish = none := by
    unfold finish
    rw [relocateBanks_step, hcStop]
    rfl
  let result := thenRight TapeMultiply.machine CountedRead.machine mulBanks readBanks finish
  have hrun := thenSegment TapeMultiply.machine CountedRead.machine mulBanks readBanks h12 hhalt12 h23
  refine ⟨_, result, hrun, ?_, ?_, hout⟩
  · change (thenMachine TapeMultiply.machine CountedRead.machine mulBanks readBanks).step word result = none
    unfold result
    rw [thenStep_right, hfinish]
    rfl
  · exact (bankConfig_cell_image CountedRead.machine readBanks c mid.workHead mid.workCell
      ⟨1, by decide⟩).trans hr

end Mathproof.MinimumGeneration.ColumnRead
