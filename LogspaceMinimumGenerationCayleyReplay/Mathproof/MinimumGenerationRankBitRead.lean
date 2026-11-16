import Mathproof.MinimumGenerationLocalInput
import Mathproof.MinimumGenerationCountedRead

namespace Mathproof.MinimumGeneration.RankLiveEntry

open SearchTransducer

abbrev preparedBitReader := CountedRead.machine.inputOnBanks

private def nativeAnswer : Fin CountedRead.machine.workTapes := ⟨1, by decide⟩

abbrev answerBank : Fin preparedBitReader.workTapes :=
  Fin.castAdd 2 nativeAnswer

/-- A fixed physical reader obtains a requested bit from a field word in
work storage. It leaves the raw input head and write-only output parked. -/
theorem readPreparedBit (outer localWord prior : List Bool) (parked : Int)
    (offset : Fin localWord.length) (indexWidth : Nat)
    (hIndex : offset.val < 2 ^ indexWidth)
    (hLeft : -1 ≤ parked) (hRight : parked ≤ (outer.length : Int)) :
    let start := CountedRead.machine.inputBankConfig localWord parked
      (CountedRead.start 0 (encodeLabel indexWidth offset.val) [false] prior)
    let cap := max (max indexWidth 1 + 1) (localWord.length + 1)
    ∃ (steps : Nat) (d : preparedBitReader.Config),
      preparedBitReader.BoundedSegment outer cap start d steps ∧
      preparedBitReader.step outer d = none ∧
      d.workCell answerBank 1 = some localWord[offset.val] ∧
      d.workHead answerBank = 0 ∧ d.inputHead = parked ∧ d.outputReversed = prior := by
  let count := encodeLabel indexWidth offset.val
  have hd : InputPosition.digits count = offset.val := InputPosition.digits_encodeLabel _ _ hIndex
  have hs : 0 + [false].length * InputPosition.digits count + [false].length ≤ localWord.length := by
    simpa only [hd, List.length_singleton, Nat.one_mul, Nat.zero_add] using Nat.succ_le_of_lt offset.isLt
  obtain ⟨steps, d, hRun, hStop, hWord, _, hOutput, hHead⟩ :=
    CountedRead.run localWord count [false] prior 0 hs
  have hBound := CountedRead.machine.inputOnBanks_segment outer localWord parked hRun hLeft hRight
  have hBank : d.workCell nativeAnswer 1 =
      some localWord[offset.val] := by
    change d.workCell nativeAnswer = _ at hWord
    rw [hWord]
    simp only [InputPosition.work, InputPosition.window, hd, List.length_singleton,
      Nat.one_mul, Nat.zero_add]
    have clean : (1 : Int) - 1 = 0 := rfl
    rw [if_neg (by decide : ¬ (1 : Int) ≤ 0), clean, Int.toNat_zero, List.getElem?_take,
      if_pos (by decide : (0 : Nat) < 1), List.getElem?_drop, Nat.add_zero,
      List.getElem?_eq_getElem offset.isLt]
  refine ⟨steps, CountedRead.machine.inputBankConfig localWord parked d, ?_,
    CountedRead.machine.inputOnBanks_halt outer localWord parked (hRun.2 steps le_rfl d hRun.1).1 hStop,
    ?_, ?_, rfl, hOutput⟩
  · simpa only [count, length_encodeLabel, List.length_singleton] using hBound
  · simpa only [answerBank, inputBankConfig, Fin.addCases_left] using hBank
  · simpa only [answerBank, inputBankConfig, Fin.addCases_left] using hHead nativeAnswer

end Mathproof.MinimumGeneration.RankLiveEntry
