import Mathproof.MinimumGenerationGreedyTapeScan

namespace Mathproof.MinimumGeneration.PhysicalGreedyRegisters

open SearchTransducer
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

variable {W B w : Nat} {word : List Bool}

structure Parked {P : SearchTransducer} (word : List Bool) (c : P.Config) : Prop where
  lo : (-1 : Int) ≤ c.inputHead
  hi : c.inputHead ≤ word.length
  heads : c.workHead = fun _ => 0

private theorem work_right (xs : List Bool) :
    work xs ((xs.length : Int) + 1) = none := by
  simp [work, show ¬ ((xs.length : Int) + 1 ≤ 0) by omega]

private theorem work_block (xs : List Bool) : TapeArithmetic.block (work xs) 1 xs := by
  intro i
  simp [work, show ¬ (1 + (i.val : Int) ≤ 0) by omega,
    show 1 + (i.val : Int) - 1 = (i.val : Int) by omega]

private theorem update_exact (old new : List Bool) (len : old.length = new.length)
    (cell : Int → Option Bool) (bits : TapeArithmetic.block cell 1 new)
    (outside : ∀ p, p < 1 ∨ (old.length : Int) + 1 ≤ p → cell p = work old p) :
    cell = work new := by
  funext p
  by_cases low : p < 1
  · simp [outside p (.inl low), work, show p ≤ 0 by omega]
  by_cases high : (old.length : Int) + 1 ≤ p
  · rw [outside p (.inr high)]
    have pos : ¬ p ≤ 0 := by omega
    simp only [work, if_neg pos, List.getElem?_eq_none (show old.length ≤ (p - 1).toNat by omega),
      List.getElem?_eq_none (show new.length ≤ (p - 1).toNat by omega)]
  let i : Fin new.length := ⟨(p - 1).toNat, by omega⟩
  have eq : (1 : Int) + i.val = p := by dsimp [i]; omega
  rw [← eq]
  exact (bits i).trans ((work_block new) i).symm

private theorem registerWindow {src dst : Fin W} {op : TapeRegisters.Operation}
    (c : (TapeRegisters.machine src dst op).Config) (parked : Parked word c)
    (bound : w + 1 ≤ B) :
    ∀ i j, c.workHead i ≤ j → j ≤ TapeRegisters.finish c.workHead src dst (w+1 : Nat) i →
      j.natAbs ≤ B := by
  intro i j hlo hhi
  have low : 0 ≤ j := by simpa [parked.heads] using hlo
  have high : j ≤ (w : Int) + 1 := by
    unfold TapeRegisters.finish at hhi
    split at hhi
    · simpa [parked.heads] using hhi
    · simp [parked.heads] at hhi
      omega
  have := Int.natAbs_of_nonneg low
  omega

theorem compareZero (counter zero : Fin W)
    (c : (TapeRegisters.machine counter zero .compare).Config) (state : c.state = 0)
    (parked : Parked word c) (value : Nat) (fits : value < 2^w)
    (data : c.workCell counter = work (encodeLabel w value))
    (saved : c.workCell zero = work (encodeLabel w 0)) (bound : w+1 ≤ B) :
    let P := TapeRegisters.machine counter zero .compare
    ∃ d : P.Config, P.BoundedSegment word B c d (2*w+3) ∧ P.step word d = none ∧
      (d.state = TapeRegisters.done true ↔ value = 0) ∧ d.inputHead = c.inputHead ∧
      d.workHead = c.workHead ∧ d.workCell = c.workCell ∧ d.outputReversed = c.outputReversed := by
  let a := encodeLabel w value
  let z := encodeLabel w 0
  have ha : a.length = w := length_encodeLabel _ _
  have hz : z.length = w := length_encodeLabel _ _
  obtain ⟨d, yes, run, terminal, verdict, heads, cells, input, output⟩ :=
    TapeRegisters.executeCompare word c a z (ha.trans hz.symm) state
      (by simp [parked.heads, saved, work])
      (by simpa [parked.heads, data, ha] using work_right a)
      (by simpa [parked.heads, saved, ha, hz] using work_right z)
      (by simpa [parked.heads, data] using work_block a)
      (by simpa [parked.heads, saved] using work_block z)
  have bounded := run.boundedSegment (B := B) ⟨parked.lo, parked.hi⟩
    (by simpa [ha] using registerWindow c parked bound)
  rw [ha] at bounded
  refine ⟨d, bounded, TapeRegisters.step_done word d yes terminal, ?_, input, heads, cells, output⟩
  have eq : a = z ↔ value = 0 := by
    constructor
    · intro h
      have hh := congrArg InputPosition.digits h
      simp only [a, z, InputPosition.digits_encodeLabel _ _ fits,
        InputPosition.digits_encodeLabel _ _ (Nat.two_pow_pos _)] at hh
      exact hh
    · intro h
      simp [a,z,h]
  have flag : TapeRegisters.done yes = TapeRegisters.done true ↔ yes = true := by
    cases yes <;> decide
  rw [terminal, flag, verdict, eq]

def nextValue (op : TapeArithmetic.Operation) (value : Nat) : Nat :=
  match op with | .increment => value+1 | .decrement => value-1

/-- Increment one bank or decrement a positive bank, preserving the rest of
the live working frame and returning all work heads to their original positions. -/
theorem change (bank : Fin W) (op : TapeArithmetic.Operation)
    (c : (TapeArithmetic.machine bank op).Config) (state : c.state = 0)
    (parked : Parked word c) (value : Nat)
    (positive : op = .decrement → 0 < value)
    (data : c.workCell bank = work (encodeLabel w value)) (bound : w+1 ≤ B) :
    let P := TapeArithmetic.machine bank op
    let v := nextValue op value
    ∃ d : P.Config, P.BoundedSegment word B c d (2*w+3) ∧ P.step word d = none ∧
      d.inputHead = c.inputHead ∧ d.workHead = c.workHead ∧
      d.workCell bank = work (encodeLabel w v) ∧ d.outputReversed = c.outputReversed ∧
      ∀ j, j ≠ bank → d.workCell j = c.workCell j := by
  let a := encodeLabel w value
  let v := nextValue op value
  let b := encodeLabel w v
  have ha : a.length = w := length_encodeLabel _ _
  have hb : b.length = w := length_encodeLabel _ _
  have left : c.workCell bank (c.workHead bank) = none := by simp [parked.heads, data, work]
  have right : c.workCell bank (c.workHead bank + w + 1) = none := by
    simpa [parked.heads, data, ha] using work_right a
  have bits : TapeArithmetic.block (c.workCell bank) (c.workHead bank+1) a := by
    simpa [parked.heads, data] using work_block a
  have actual : ∃ d, TapeArithmetic.Runs word (c.workHead bank) (c.workHead bank+w+1)
    (2*w+3) c d ∧ d.state = 4 ∧ d.workHead bank = c.workHead bank ∧
    TapeArithmetic.block (d.workCell bank) (c.workHead bank+1) b ∧
    TapeArithmetic.Framed c d (c.workHead bank+1) (c.workHead bank+w+1) := by
    cases op with
    | increment => exact TapeArithmetic.executeIncrement word c w value state left right bits
    | decrement => exact TapeArithmetic.executeDecrement word c w value (positive rfl) state left right bits
  obtain ⟨d, run, terminal, head, result, frame⟩ := actual
  have bounded := TapeRegisters.arithmeticBoundedSegment (B := B) run ⟨parked.lo, parked.hi⟩
    (by
      intro j hlo hhi
      have lo : 0 ≤ j := by simpa [parked.heads] using hlo
      have hi : j ≤ (w : Int) + 1 := by simpa [parked.heads] using hhi
      have := Int.natAbs_of_nonneg lo
      omega)
    (by simp [parked.heads])
  refine ⟨d, bounded, TapeArithmetic.step_done word d terminal, frame.input, ?_, ?_,
    frame.output, fun j h => funext fun p => frame.cells j p (.inl h)⟩
  · funext j
    by_cases h : j = bank
    · subst j
      exact head
    · exact frame.heads j h
  · apply update_exact a b (ha.trans hb.symm)
    · simpa [parked.heads] using result
    · intro j hj
      rw [← data]
      exact frame.cells bank j (.inr (by simpa [parked.heads, ha] using hj))

/-- Physically initialize the live label cursor from any same-width payload. -/
theorem clear (bank : Fin W)
    (c : (TapeRegisters.machine bank bank .zero).Config) (state : c.state = 0)
    (parked : Parked word c) (xs : List Bool) (len : xs.length = w)
    (data : c.workCell bank = work xs) (bound : w+1 ≤ B) :
    let P := TapeRegisters.machine bank bank .zero
    ∃ d : P.Config, P.BoundedSegment word B c d (2*w+3) ∧ P.step word d = none ∧
      d.inputHead = c.inputHead ∧ d.workHead = c.workHead ∧
      d.workCell bank = work (encodeLabel w 0) ∧ d.outputReversed = c.outputReversed ∧
      ∀ j, j ≠ bank → d.workCell j = c.workCell j := by
  obtain ⟨d, run, terminal, heads, result, frame⟩ :=
    TapeRegisters.executeZero word c xs state
      (by simp [parked.heads, data, work])
      (by simpa [parked.heads, data] using work_right xs)
      (by simpa [parked.heads, data] using work_block xs)
  have bounded := run.boundedSegment (B := B) ⟨parked.lo, parked.hi⟩
    (by simpa [len] using registerWindow c parked bound)
  rw [len] at bounded
  refine ⟨d, bounded, TapeRegisters.step_done word d true terminal, frame.input, heads, ?_,
    frame.output, fun j h => funext fun p => frame.cell j p (.inl h)⟩
  apply update_exact xs (encodeLabel w 0) (by simpa using len)
  · have hz : encodeLabel w 0 = List.replicate xs.length false := by
      have zeroBit : Nat.testBit 0 = fun _ => false := funext Nat.zero_testBit
      simp [encodeLabel, zeroBit, len]
    simpa [parked.heads, hz] using result
  · intro j hj
    rw [← data]
    exact frame.cell bank j (.inr (by simpa [parked.heads] using hj))

end Mathproof.MinimumGeneration.PhysicalGreedyRegisters
