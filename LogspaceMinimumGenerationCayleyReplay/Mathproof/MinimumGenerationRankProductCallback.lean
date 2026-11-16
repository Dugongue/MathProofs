import Mathproof.MinimumGenerationRankBitRead
import Mathproof.MinimumGenerationRankBerkowitzColumnCursor

namespace Mathproof.MinimumGeneration.RankBerkowitz.ColumnProduct

open SearchTransducer RankLiveEntry

/-- Run the physical operand reader for one multiplication-cursor request.
The captured bit makes the resumed cursor valid and decreases its countdown. -/
theorem executePreparedRequest (x y target width : Nat) (hw : target < width)
    (s : Cursor) (hs : s.valid x.testBit y.testBit target)
    (side : Bool) (index : Nat) (hRequest : s.request = some (side,index))
    (outer prior : List Bool) (parked : Int)
    (hLeft : -1 ≤ parked) (hRight : parked ≤ (outer.length : Int)) :
    let word := encodeLabel width (if side then y else x)
    let indexWidth := (target + 1).size
    let entry := CountedRead.machine.inputBankConfig word parked
      (CountedRead.start 0 (encodeLabel indexWidth index) [false] prior)
    let next := s.reply target ((if side then y else x).testBit index)
    ∃ (k : Nat) (d : preparedBitReader.Config),
      preparedBitReader.BoundedSegment outer (max (max indexWidth 1 + 1) (word.length + 1))
        entry d k ∧
      preparedBitReader.step outer d = none ∧
      d.workCell answerBank 1 = some ((if side then y else x).testBit index) ∧
      d.inputHead = parked ∧ d.outputReversed = prior ∧
      step x.testBit y.testBit target s = some next ∧
      next.valid x.testBit y.testBit target ∧ countdown target next < countdown target s := by
  let value := if side then y else x
  let word := encodeLabel width value
  have hIndex : index ≤ target := by
    have hcol := hs.1
    have hrow := hs.2.1
    cases hTag : s.phase <;>
      simp only [Cursor.request, hTag, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq] at hRequest
    · omega
    · omega
  have hAt : index < word.length := by
    rw [show word.length = width from length_encodeLabel _ _]
    omega
  obtain ⟨k, d, hSegment, hStop, hBit, _, hPark, hPrior⟩ :=
    readPreparedBit outer word prior parked ⟨index,hAt⟩ (target+1).size
      ((show index < target+1 by omega).trans (Nat.lt_size_self _)) hLeft hRight
  have hVal : word[index] = value.testBit index := by
    simp [word, encodeLabel, List.getElem_range]
  rw [hVal] at hBit
  have hNext : step x.testBit y.testBit target s = some (s.reply target (value.testBit index)) := by
    cases side <;> simp [step, hRequest, value]
  exact ⟨k, d, hSegment, hStop, hBit, hPark, hPrior, hNext,
    step_valid hs hNext, step_decreases hs hNext⟩

end Mathproof.MinimumGeneration.RankBerkowitz.ColumnProduct
