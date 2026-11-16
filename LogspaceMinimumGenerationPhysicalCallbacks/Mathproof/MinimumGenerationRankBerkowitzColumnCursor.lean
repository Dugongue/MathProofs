import Mathproof.MinimumGenerationRankBerkowitzColumnProduct

/-!
A digit-column multiplier suspended explicitly at each operand-bit query.
One transition accepts one Boolean answer. The complete execution has bounded
cursor registers and returns the requested bit of the exact natural product.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.ColumnProduct

inductive Phase
  | askLeft
  | askRight (leftBit : Bool)
  | done (answer : Bool)

structure Cursor where
  column : Nat
  row : Nat
  runningCarry : Nat
  runningCount : Nat
  phase : Phase

def start : Cursor := ⟨0, 0, 0, 0, .askLeft⟩

/-- The first component selects the right operand when true. -/
def Cursor.request (state : Cursor) : Option (Bool × Nat) :=
  match state.phase with
  | .askLeft => some (false, state.row)
  | .askRight _ => some (true, state.column - state.row)
  | .done _ => none

/-- Consume the one-bit response to the current request. -/
def Cursor.reply (target : Nat) (state : Cursor) (bit : Bool) : Cursor :=
  match state.phase with
  | .askLeft => {state with phase := .askRight bit}
  | .askRight leftBit =>
    let count := state.runningCount + (leftBit && bit).toNat
    if state.row < state.column then
      {state with row := state.row + 1, runningCount := count, phase := .askLeft}
    else if state.column < target then
      ⟨state.column + 1, 0, (state.runningCarry + count) / 2, 0, .askLeft⟩
    else {state with phase := .done (decide ((state.runningCarry + count) % 2 = 1))}
  | .done _ => state

def step (left right : Nat → Bool) (target : Nat) (state : Cursor) : Option Cursor :=
  state.request.map fun query => state.reply target
    (if query.1 then right query.2 else left query.2)

def Cursor.valid (left right : Nat → Bool) (target : Nat) (state : Cursor) : Prop :=
  state.column ≤ target ∧ state.row ≤ state.column ∧
    state.runningCarry = carry left right state.column ∧
    state.runningCount = partialCount left right state.column state.row ∧
    match state.phase with
    | .askLeft => True
    | .askRight bit => bit = left state.row
    | .done bit => bit = outputBit left right target

theorem start_valid (left right : Nat → Bool) (target : Nat) :
    start.valid left right target := by
  simp [start, Cursor.valid]

theorem step_valid {left right : Nat → Bool} {target : Nat} {s t : Cursor}
    (hValid : s.valid left right target) (hStep : step left right target s = some t) :
    t.valid left right target := by
  rcases hValid with ⟨hColumn, hRow, hCarry, hCount, hPhase⟩
  cases hTag : s.phase with
  | askLeft =>
    simp [step, Cursor.request, Cursor.reply, hTag] at hStep
    subst t
    exact ⟨hColumn, hRow, hCarry, hCount, rfl⟩
  | askRight bit =>
    rw [hTag] at hPhase
    change bit = left s.row at hPhase
    have hCountNext :
        s.runningCount + (bit && right (s.column - s.row)).toNat =
          partialCount left right s.column (s.row + 1) := by
      rw [partialCount_succ, hCount, hPhase]
    simp only [step, Cursor.request, Cursor.reply, hTag, Option.map_some, if_true] at hStep
    by_cases hMoreRow : s.row < s.column
    · simp only [hMoreRow, if_true, Option.some.injEq] at hStep
      subst t
      exact ⟨hColumn, Nat.succ_le_of_lt hMoreRow, hCarry, hCountNext, trivial⟩
    · have hRowEq : s.row = s.column := by omega
      have hWholeCount :
          s.runningCount + (bit && right (s.column - s.row)).toNat =
            columnCount left right s.column := by
        rw [hCountNext, hRowEq, columnCount]
      by_cases hMoreColumn : s.column < target
      · simp only [hMoreRow, hMoreColumn, if_false, if_true, Option.some.injEq] at hStep
        subst t
        refine ⟨Nat.succ_le_of_lt hMoreColumn, Nat.zero_le _, ?_, partialCount_zero _ _ _ |>.symm, trivial⟩
        change (s.runningCarry + (s.runningCount + (bit && right (s.column - s.row)).toNat)) / 2 =
          carry left right (s.column + 1)
        rw [hWholeCount, hCarry, carry_succ]
      · simp only [hMoreRow, hMoreColumn, if_false, Option.some.injEq] at hStep
        subst t
        refine ⟨hColumn, hRow, hCarry, hCount, ?_⟩
        have hColumnEq : s.column = target := by omega
        change decide ((s.runningCarry + (s.runningCount +
          (bit && right (s.column - s.row)).toNat)) % 2 = 1) = outputBit left right target
        rw [hWholeCount, hCarry, hColumnEq, outputBit]
  | done bit => simp [step, Cursor.request, hTag] at hStep

def countdown (target : Nat) (s : Cursor) : Nat :=
  let span := target + 1
  let cells := span * span - (span * s.column + s.row)
  match s.phase with
  | .askLeft => 2 * cells + 1
  | .askRight _ => 2 * cells
  | .done _ => 0

private theorem position_lt {target : Nat} {s : Cursor}
    (hColumn : s.column ≤ target) (hRow : s.row ≤ s.column) :
    (target + 1) * s.column + s.row < (target + 1) * (target + 1) := by
  have hBound := Nat.mul_le_mul_left (target + 1) hColumn
  rw [Nat.mul_succ (target + 1) target]
  omega

theorem step_decreases {left right : Nat → Bool} {target : Nat} {s t : Cursor}
    (hValid : s.valid left right target) (hStep : step left right target s = some t) :
    countdown target t < countdown target s := by
  have hPos := position_lt hValid.1 hValid.2.1
  cases hTag : s.phase with
  | askLeft =>
    simp [step, Cursor.request, Cursor.reply, hTag] at hStep
    subst t
    simp [countdown, hTag]
  | askRight bit =>
    simp only [step, Cursor.request, Cursor.reply, hTag, Option.map_some, if_true] at hStep
    by_cases hMoreRow : s.row < s.column
    · simp only [hMoreRow, if_true, Option.some.injEq] at hStep
      subst t
      simp only [countdown, hTag]
      omega
    · by_cases hMoreColumn : s.column < target
      · simp only [hMoreRow, hMoreColumn, if_false, if_true, Option.some.injEq] at hStep
        subst t
        simp only [countdown, hTag, Nat.add_zero]
        rw [Nat.mul_succ (target + 1) s.column]
        have hR := hValid.2.1.trans hValid.1
        omega
      · simp only [hMoreRow, hMoreColumn, if_false, Option.some.injEq] at hStep
        subst t
        simp only [countdown, hTag]
        omega
  | done bit => simp [step, Cursor.request, hTag] at hStep

/-- A run recording validity at every callback and at its terminal state. -/
inductive Runs (left right : Nat → Bool) (target : Nat) : Cursor → Cursor → Prop
  | done {s : Cursor} (valid : s.valid left right target) : Runs left right target s s
  | next {s t e : Cursor} (valid : s.valid left right target)
      (transition : step left right target s = some t) (tail : Runs left right target t e) :
      Runs left right target s e

theorem execute_from (left right : Nat → Bool) (target : Nat) (s : Cursor)
    (hValid : s.valid left right target) :
    ∃ e, Runs left right target s e ∧ e.phase = .done (outputBit left right target) := by
  cases hStep : step left right target s with
  | none =>
    cases hTag : s.phase with
    | askLeft => simp [step, Cursor.request, hTag] at hStep
    | askRight bit => simp [step, Cursor.request, hTag] at hStep
    | done bit =>
      have hBit := hValid.2.2.2.2
      rw [hTag] at hBit
      change bit = outputBit left right target at hBit
      exact ⟨s, .done hValid, by rw [hTag, hBit]⟩
  | some t =>
    obtain ⟨e, hRun, hEnd⟩ := execute_from left right target t (step_valid hValid hStep)
    exact ⟨e, .next hValid hStep hRun, hEnd⟩
termination_by countdown target s
decreasing_by exact step_decreases hValid hStep

theorem execute (x y target : Nat) :
    ∃ e, Runs x.testBit y.testBit target start e ∧ e.phase = .done ((x*y).testBit target) := by
  rw [← outputBit_eq x y target]
  exact execute_from _ _ _ _ (start_valid _ _ _)

theorem valid_cursor_registers_fit {left right : Nat → Bool} {target : Nat} {s : Cursor}
    (h : s.valid left right target) :
    let w := (target + 1).size
    target < 2^w ∧ s.column < 2^w ∧ s.row < 2^w ∧
      s.runningCarry < 2^w ∧ s.runningCount < 2^w := by
  rw [h.2.2.1, h.2.2.2.1]
  exact suspended_registers_fit left right target s.column s.row h.1 (h.2.1.trans (Nat.le_succ _))

end Mathproof.MinimumGeneration.RankBerkowitz.ColumnProduct
