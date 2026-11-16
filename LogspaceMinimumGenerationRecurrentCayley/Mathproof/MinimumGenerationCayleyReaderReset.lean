import Mathproof.MinimumGenerationTapeInstall
import Mathproof.MinimumGenerationMacroDispatch

namespace Mathproof.MinimumGeneration.CayleyReaderReset

open SearchTransducer Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

private def opposite : Move → Move
  | .left => .right
  | .right => .left
  | .stay => .stay

private theorem opposite_offset (m : Move) : moveOffset (opposite m) = -(moveOffset m) := by
  cases m <;> simp [opposite, moveOffset]

private def coord {W : ℕ} (clock i : Fin W) (p : Int) : Int :=
  if i = clock then p else -p

private theorem coord_twice {W : ℕ} (clock i : Fin W) (p : Int) :
    coord clock i (coord clock i p) = p := by by_cases h : i = clock <;> simp [coord,h]

private theorem coord_abs {W : ℕ} (clock i : Fin W) (p : Int) :
    (coord clock i p).natAbs = p.natAbs := by by_cases h : i = clock <;> simp [coord,h]

private theorem coord_zero {W : ℕ} (clock i : Fin W) : coord clock i 0 = 0 := by simp [coord]

private def mirrorCells {W : ℕ} (clock : Fin W) (cells : Fin W → Int → Option Bool) :
    Fin W → Int → Option Bool := fun i p => cells i (coord clock i p)

private theorem mirrorCells_twice {W : ℕ} (clock : Fin W) (cells : Fin W → Int → Option Bool) :
    mirrorCells clock (mirrorCells clock cells) = cells := by
  funext i p
  exact congrArg (cells i) (coord_twice clock i p)

/-- Reverse all work moves except on the one unreflected tape. The physical
reader and the output operation are unchanged. -/
abbrev mirror (P : SearchTransducer) (clock : Fin P.workTapes) : SearchTransducer where
  states := P.states
  workTapes := P.workTapes
  initialState := P.initialState
  transition q inp read := (P.transition q inp read).map fun (r, m, act, bit) =>
    (r, m, fun i => ⟨(act i).write, if i = clock then (act i).move else opposite (act i).move⟩, bit)

def mirrorConfig (P : SearchTransducer) (clock : Fin P.workTapes) (c : P.Config) :
    (mirror P clock).Config :=
  ⟨c.state,c.inputHead,fun i => coord clock i (c.workHead i),
    mirrorCells clock c.workCell,c.outputReversed⟩

theorem mirrorStep (P : SearchTransducer) (clock : Fin P.workTapes) (word : List Bool)
    (c : P.Config) :
    (mirror P clock).step word (mirrorConfig P clock c) =
      (P.step word c).map (mirrorConfig P clock) := by
  unfold SearchTransducer.step
  have reads : (fun i => (mirrorConfig P clock c).workCell i
      ((mirrorConfig P clock c).workHead i)) = fun i => c.workCell i (c.workHead i) := by
    funext i
    exact congrArg (c.workCell i) (coord_twice clock i (c.workHead i))
  have input : (mirrorConfig P clock c).inputHead = c.inputHead := rfl
  rw [reads,input]
  change Option.map _ ((P.transition c.state _ _).map _) =
    Option.map _ (Option.map _ _)
  cases trans : P.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => rfl
  | some a =>
    obtain ⟨q,m,acts,out⟩ := a
    simp only [Option.map_some,Option.some.injEq]
    congr 1
    · funext i
      by_cases h : i = clock
      · simp [mirrorConfig,coord,h]
      · simp [mirrorConfig,coord,h,opposite_offset]
        omega
    · funext i p
      by_cases h : i = clock
      · simp [mirrorConfig,mirrorCells,coord,h]
      · simp only [mirrorConfig,mirrorCells,coord,if_neg h]
        have hEq : p = -c.workHead i ↔ -p = c.workHead i := by omega
        simp only [hEq]

theorem mirrorRun (P : SearchTransducer) (clock : Fin P.workTapes) (word : List Bool)
    (c : P.Config) (k : ℕ) :
    (mirror P clock).runFrom word (mirrorConfig P clock c) k =
      (P.runFrom word c k).map (mirrorConfig P clock) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runFrom,ih]
    cases h : P.runFrom word c k with
    | none => rfl
    | some x => exact mirrorStep P clock word x

theorem mirrorSegment (P : SearchTransducer) (clock : Fin P.workTapes)
    {word : List Bool} {B k : ℕ} {c d : P.Config} (h : P.BoundedSegment word B c d k) :
    (mirror P clock).BoundedSegment word B (mirrorConfig P clock c) (mirrorConfig P clock d) k := by
  refine ⟨by rw [mirrorRun,h.1]; rfl,?_⟩
  intro j hj x hx
  rw [mirrorRun] at hx
  obtain ⟨e,he,rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨lo,hi,bound⟩ := h.2 j hj e he
  exact ⟨lo,hi,fun i => (coord_abs clock i _).trans_le (bound i)⟩

section Reset

variable {W : ℕ} (clock : Fin W) (source : Fin W → Option (Fin W))

private def originCells (old : Fin W → Int → Option Bool) (i : Fin W) (p : Int) : Option Bool :=
  if p = 0 then (source i).elim (old i p) (fun k => old k p) else old i p

private theorem originFixed (old : Fin W → Int → Option Bool) {i : Fin W}
    (hi : source i = none) : originCells source old i = old i := by
  funext p
  simp [originCells,hi]

private abbrev origin : SearchTransducer where
  states := 4
  workTapes := W
  initialState := 0
  transition q _ vals :=
    if q = 0 then some (3, .stay, fun i => ⟨(source i).map vals,.stay⟩,none) else none

private abbrev positive := TapeInstall.machine clock source

private def negativeCells (old : Fin W → Int → Option Bool) (w : ℕ) : Fin W → Int → Option Bool :=
  mirrorCells clock (TapeInstall.installed source (mirrorCells clock (originCells source old)) w)

abbrev stages : Stages 3 4 W where
  first := 0
  entry _ := 0
  transition i := if i=0 then (origin source).transition
    else if i=1 then (mirror (positive clock source) clock).transition else (positive clock source).transition
  next i _ := if i=0 then some 1 else if i=1 then some 2 else none

abbrev machine := (stages clock source).machine

def start (input : Int) (out : List Bool) (old : Fin W → Int → Option Bool) :
    (machine clock source).Config :=
  (stages clock source).tag 0 ⟨0,input,fun _ => 0,old,out⟩

def finish (input : Int) (out : List Bool) (old : Fin W → Int → Option Bool) (w : ℕ) :
    (machine clock source).Config :=
  (stages clock source).tag 2 (TapeInstall.stop clock source input (negativeCells clock source old w) out w)

private theorem singleton {P : SearchTransducer} {raw : List Bool} {B : ℕ} {c d : P.Config}
    (step : P.step raw c = some d) (a : P.Bounded raw B c) (b : P.Bounded raw B d) :
    P.BoundedSegment raw B c d 1 := by
  refine ⟨step,?_⟩
  intro t ht x hx
  have either : t=0 ∨ t=1 := by omega
  rcases either with rfl | rfl
  · cases hx
    exact a
  · change P.step raw c = some x at hx
    rw [step] at hx
    cases hx
    exact b

private theorem writeOrigin {raw out : List Bool} {input : Int} {B : ℕ}
    (old : Fin W → Int → Option Bool)
    (legal : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    let a : (origin source).Config := ⟨0,input,fun _ => 0,old,out⟩
    let b : (origin source).Config := ⟨3,input,fun _ => 0,originCells source old,out⟩
    (origin source).BoundedSegment raw B a b 1 ∧ (origin source).step raw b = none := by
  intro a b
  have side : (origin source).step raw a = some b := by
    change (origin source).step raw ⟨0,input,fun _ => 0,old,out⟩ = _
    simp only [SearchTransducer.step, origin, moveOffset, Int.add_zero, eq_self, if_true,
      Option.map_some, Option.some.injEq]
    unfold b
    congr 1
    funext i p
    by_cases hp : p=0
    · subst p
      cases h : source i <;> simp [originCells,h]
    · simp [originCells,hp]
  exact ⟨singleton side ⟨legal.1,legal.2,fun _ => Nat.zero_le _⟩
    ⟨legal.1,legal.2,fun _ => Nat.zero_le _⟩,rfl⟩

/-- From parked heads, run the actual origin copy and both physical sweeps.
The same positive clock controls both sides of the reset. -/
theorem run (raw out ticks : List Bool) (input : Int) (old : Fin W → Int → Option Bool)
    (clockFixed : source clock = none) (clockWord : old clock = work ticks)
    (legal : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    (machine clock source).BoundedSegment raw (ticks.length+1)
      (start clock source input out old) (finish clock source input out old ticks.length)
      (1+1+(ticks.length+2+ticks.length+1)+1+(ticks.length+2+ticks.length+1)) ∧
    (machine clock source).step raw (finish clock source input out old ticks.length) = none := by
  let T := stages clock source
  let seeded := originCells source old
  let middle := mirrorCells clock seeded
  have clockBefore : middle clock = work ticks := by
    funext p
    change seeded clock (coord clock clock p) = work ticks p
    simp only [coord,if_true,eq_self,seeded,originFixed source old clockFixed,clockWord]
  obtain ⟨ori,oriStop⟩ := writeOrigin (source := source) (out := out) (B := ticks.length+1) old legal
  obtain ⟨reverse,reverseStop⟩ := TapeInstall.execute clock source clockFixed raw ticks out input
    middle clockBefore legal
  have neg := mirrorSegment (positive clock source) clock reverse
  have negStop := mirrorStep (positive clock source) clock raw
    (TapeInstall.stop clock source input middle out ticks.length)
  rw [reverseStop] at negStop
  let oriEnd : (T.component 0).Config := ⟨3,input,fun _ => 0,seeded,out⟩
  have e₁ : T.enter (i := 0) 1 oriEnd =
      mirrorConfig (positive clock source) clock (TapeInstall.start clock source input middle out) := by
    change (⟨0,input,fun _ => 0,seeded,out⟩ : (T.component 1).Config) =
      ⟨0,input,fun i => coord clock i 0,mirrorCells clock middle,out⟩
    rw [show mirrorCells clock middle = seeded from mirrorCells_twice clock seeded]
    simp [coord_zero]
  have j₁ := T.segment_handoff (i := 0) (j := 1) oriStop rfl (ori.2 _ le_rfl _ ori.1)
  rw [e₁] at j₁
  let negEnd := mirrorConfig (positive clock source) clock
    (TapeInstall.stop clock source input middle out ticks.length)
  have clockAfter : negativeCells clock source old ticks.length clock = work ticks := by
    funext p
    change TapeInstall.installed source middle ticks.length clock (coord clock clock p) = _
    rw [TapeInstall.installed_source source middle ticks.length clock clockFixed,clockBefore]
    simp [coord]
  obtain ⟨forward,forwardStop⟩ := TapeInstall.execute clock source clockFixed raw ticks out input
    (negativeCells clock source old ticks.length) clockAfter legal
  have e₂ : T.enter (i := 1) 2 negEnd =
      TapeInstall.start clock source input (negativeCells clock source old ticks.length) out := by
    change
      (⟨0,input,fun i => coord clock i 0,negativeCells clock source old ticks.length,out⟩ :
        (T.component 2).Config) = ⟨0,input,fun _ => 0,negativeCells clock source old ticks.length,out⟩
    simp [coord_zero]
  have j₂ := T.segment_handoff (i := 1) (j := 2) (word := raw)
    (c := negEnd) (by exact negStop) rfl (neg.2 _ le_rfl _ neg.1)
  rw [e₂] at j₂
  have total := BoundedSegment.append _
    (BoundedSegment.append _ (BoundedSegment.append _
      (BoundedSegment.append _ (T.segment_component 0 ori) j₁) (T.segment_component 1 neg)) j₂)
    (T.segment_component 2 forward)
  have halt := T.step_halt 2 forwardStop
  refine ⟨total,?_⟩
  exact halt

private theorem negativeFixed (old : Fin W → Int → Option Bool) (w : ℕ) (i : Fin W)
    (fixed : source i = none) : negativeCells clock source old w i = old i := by
  funext p
  change TapeInstall.installed source (mirrorCells clock (originCells source old)) w i
    (coord clock i p) = _
  rw [TapeInstall.installed_source source _ w i fixed]
  change originCells source old i (coord clock i (coord clock i p)) = _
  rw [coord_twice, originFixed source old fixed]

/-- Copy exactly the chosen tapes. Scratch outside the swept interval must
already agree with the corresponding source. Sources and clock stay read-only. -/
theorem finishCells (input : Int) (out : List Bool) (old : Fin W → Int → Option Bool) (w : ℕ)
    (clockFixed : source clock = none)
    (ready : ∀ i j, source i = some j → source j = none ∧ j ≠ clock ∧
      ∀ p, w < p.natAbs → old i p = old j p) :
    let d := finish clock source input out old w
    d.inputHead = input ∧ d.outputReversed = out ∧ (∀ i, d.workHead i = 0) ∧
      ∀ i, d.workCell i = (source i).elim (old i) (fun j => old j) := by
  refine ⟨rfl,rfl,fun _ => rfl,?_⟩
  intro i
  let mid := negativeCells clock source old w
  change TapeInstall.installed source mid w i = _
  cases map : source i with
  | none =>
    exact (TapeInstall.installed_source source mid w i map).trans (negativeFixed clock source old w i map)
  | some j =>
    obtain ⟨readOnly,even,external⟩ := ready i j map
    have neq : i ≠ clock := by intro e; subst i; rw [clockFixed] at map; cases map
    have mirror_pos (p : Int) : coord clock i p = -p := if_neg neq
    have mirror_source (p : Int) : coord clock j p = -p := if_neg even
    have mirror_twice' (p : Int) : coord clock i (coord clock i p) = p := coord_twice clock i p
    have srcMid : mid j = old j := negativeFixed clock source old w j readOnly
    funext p
    change TapeInstall.installed source mid w i p = old j p
    by_cases pos : 1 ≤ p ∧ p ≤ (w : Int)
    · simp only [TapeInstall.installed,if_pos pos,map,Option.elim_some,srcMid]
    · simp only [TapeInstall.installed,if_neg pos]
      change TapeInstall.installed source (mirrorCells clock (originCells source old)) w i
          (coord clock i p) = old j p
      by_cases neg : 1 ≤ -p ∧ -p ≤ (w : Int)
      · rw [mirror_pos, TapeInstall.installed, if_pos neg,map]
        change originCells source old j (coord clock j (-p)) = _
        rw [mirror_source,neg_neg,originFixed source old readOnly]
      · have noNeg : ¬ (1 ≤ coord clock i p ∧ coord clock i p ≤ (w : Int)) := by
          rw [mirror_pos]
          exact neg
        rw [TapeInstall.installed, if_neg noNeg]
        change originCells source old i (coord clock i (coord clock i p)) = _
        rw [mirror_twice']
        by_cases zero : p = 0
        · simp [originCells,zero,map]
        · apply (if_neg zero).trans
          exact external p (by omega)

/-- Signed scratch reset with exact byte-for-byte restoration and head
return. Both sweeps share one physical marked clock of reset width. -/
theorem execute (raw out ticks : List Bool) (input : Int) (old : Fin W → Int → Option Bool)
    (clockFixed : source clock = none) (clockWord : old clock = work ticks)
    (legal : (-1 : Int) ≤ input ∧ input ≤ raw.length)
    (ready : ∀ i j, source i = some j → source j = none ∧ j ≠ clock ∧
      ∀ p, ticks.length < p.natAbs → old i p = old j p) :
    let d := finish clock source input out old ticks.length
    ∃ k, (machine clock source).BoundedSegment raw (ticks.length+1) (start clock source input out old) d k ∧
       (machine clock source).step raw d = none ∧ d.inputHead = input ∧ d.outputReversed = out ∧
       (∀ i, d.workHead i = 0) ∧ ∀ i, d.workCell i = (source i).elim (old i) (fun j => old j) := by
  obtain ⟨seg,halt⟩ := run clock source raw out ticks input old clockFixed clockWord legal
  exact ⟨_,seg,halt,finishCells clock source input out old ticks.length clockFixed ready⟩

end Reset

end Mathproof.MinimumGeneration.CayleyReaderReset
