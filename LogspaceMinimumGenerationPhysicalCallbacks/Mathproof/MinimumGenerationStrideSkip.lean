import Mathproof.MinimumGenerationInputPosition
import Mathproof.MinimumGenerationTapeCompose
import Mathlib.Tactic.IntervalCases

set_option backward.isDefEq.respectTransparency false

namespace Mathproof.MinimumGeneration.StrideSkip

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open SearchTransducer
open InputPosition (skip work digits)

private def countBank : Fin 2 := 0
private def widthBank : Fin 2 := 1
private def startStride : Fin 13 := 10
private def walkStride : Fin 13 := 11
private def returnStride : Fin 13 := 12

private def liftState (q : Fin 10) : Fin 13 := ⟨q.val, q.isLt.trans (by decide)⟩
private def fromState (q : Fin 13) (h : q.val < 6) : Fin 10 :=
  ⟨q.val, h.trans (by decide)⟩

private def only (bank : Fin 2) (action : Action (Option Bool)) (i : Fin 2) :
    Action (Option Bool) :=
  if i = bank then action else ⟨none, .stay⟩

private def counterTransition (q : Fin 10) (b : Option Bool) :=
  skip.transition q .rightEnd (fun _ => b)

/-- Reuse the six-state binary countdown. Each successful decrement replaces
the usual one-cell input move by a sweep over the prepared width bank. -/
abbrev strideSkip : SearchTransducer where
  states := 13
  workTapes := 2
  initialState := 0
  transition q _ read :=
    let jump := fun w inputMove =>
      some (w, inputMove, only widthBank ⟨none, .stay⟩, none)
    let walk := fun w inputMove workMove =>
      some (w, inputMove, only widthBank ⟨none, workMove⟩, none)
    if h : q.val < 6 then
      (counterTransition (fromState q h) (read countBank)).map fun (d, im, actions, out) =>
        let next := match im with
          | .right => startStride
          | _ => liftState d
        (next, .stay, only countBank (actions (0 : Fin 1)), out)
    else if q = startStride then walk walkStride .stay .right
    else if q = walkStride then
      match read widthBank with
      | some _ => walk walkStride .right .right
      | none => walk returnStride .stay .left
    else if q = returnStride then
      match read widthBank with
      | some _ => walk returnStride .stay .left
      | none => jump (liftState 3) .stay
    else none

abbrev config (q : Fin 13) (input countHead widthHead : Int)
    (countTape : Int → Option Bool) (width : List Bool) (prior : List Bool) : strideSkip.Config :=
  ⟨q, input, fun i : Fin 2 => if i = countBank then countHead else widthHead,
    fun i : Fin 2 => if i = countBank then countTape else work width, prior⟩

private theorem banks_ne : widthBank ≠ countBank := by decide

private theorem bank_cases (i : Fin 2) : i = countBank ∨ i = widthBank := by
  have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
  rcases hi with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

private theorem work_bit (bits : List Bool) (j : Nat) :
    work bits ((j : Int) + 1) = bits[j]? := by
  simp [work, show ¬ ((j : Int) + 1 ≤ 0) by omega]

private theorem work_last (bits : List Bool) : work bits ((bits.length : Int) + 1) = none := by
  rw [work_bit, List.getElem?_eq_none le_rfl]

private theorem width_step (word width prior : List Bool)
    (q r : Fin 13) (input countHead widthHead : Int) (countTape : Int → Option Bool)
    (im wm : Move)
    (h : strideSkip.transition q (readInput word input)
      (fun i : Fin 2 => if i = countBank then countTape countHead else work width widthHead) =
      some (r, im, only widthBank ⟨none, wm⟩, none)) :
    strideSkip.step word (config q input countHead widthHead countTape width prior) =
      some (config r (input + moveOffset im) countHead (widthHead + moveOffset wm) countTape width prior) := by
  have hc :
      (fun i : Fin 2 => (if i = countBank then countTape else work width)
        (if i = countBank then countHead else widthHead)) =
      (fun i : Fin 2 => if i = countBank then countTape countHead else work width widthHead) := by
    funext i
    by_cases hi : i = countBank <;> simp [hi]
  let c := config q input countHead widthHead countTape width prior
  have ht : strideSkip.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) =
      some (r, im, only widthBank ⟨none, wm⟩, none) := by
    exact (congrArg (strideSkip.transition q (readInput word input)) hc).trans h
  change strideSkip.step word c = _
  unfold SearchTransducer.step
  rw [ht]
  simp only [c, config, Option.map_some, Option.some.injEq]
  congr 1
  · funext i
    rcases bank_cases i with rfl | rfl
    · simp [only, Ne.symm banks_ne, moveOffset]
    · simp [only, banks_ne]
  · funext i j
    rcases bank_cases i with rfl | rfl
    · simp only [only, Ne.symm banks_ne]
      exact ite_self _
    · simp only [only]
      exact ite_self _

private theorem stride_start (word width prior : List Bool) (input countHead : Int)
    (countTape : Int → Option Bool) :
    strideSkip.step word (config startStride input countHead 0 countTape width prior) =
      some (config walkStride input countHead 1 countTape width prior) := by
  simpa [moveOffset] using
    width_step word width prior startStride walkStride input countHead 0 countTape .stay .right (by rfl)

private theorem stride_move (word width prior : List Bool) (input countHead : Int)
    (j : Nat) (hj : j < width.length) (countTape : Int → Option Bool) :
    strideSkip.step word (config walkStride input countHead ((j : Int) + 1) countTape width prior) =
      some (config walkStride (input + 1) countHead ((j : Int) + 2) countTape width prior) := by
  have hb : work width ((j : Int) + 1) = some width[j] := by
    rw [work_bit, List.getElem?_eq_getElem hj]
  have hs : walkStride ≠ startStride := by decide
  have h : strideSkip.transition walkStride (readInput word input)
      (fun i : Fin 2 => if i = countBank then countTape countHead else work width ((j : Int) + 1)) =
      some (walkStride, .right, only widthBank ⟨none, .right⟩, none) := by
    simp [strideSkip, walkStride, startStride, widthBank, countBank, hb]
  simpa [moveOffset, Int.add_assoc] using
    width_step word width prior walkStride walkStride input countHead ((j : Int) + 1) countTape .right .right h

private theorem stride_turn (word width prior : List Bool) (input countHead : Int)
    (countTape : Int → Option Bool) :
    strideSkip.step word (config walkStride input countHead ((width.length : Int) + 1) countTape width prior) =
      some (config returnStride input countHead width.length countTape width prior) := by
  have h : strideSkip.transition walkStride (readInput word input)
      (fun i : Fin 2 => if i = countBank then countTape countHead else work width ((width.length : Int) + 1)) =
      some (returnStride, .stay, only widthBank ⟨none, .left⟩, none) := by
    simp [strideSkip, walkStride, startStride, banks_ne]
  simpa [moveOffset] using
    width_step word width prior walkStride returnStride input countHead ((width.length : Int) + 1) countTape .stay .left h

private theorem stride_back (word width prior : List Bool) (input countHead : Int)
    (j : Nat) (hj : j < width.length) (countTape : Int → Option Bool) :
    strideSkip.step word (config returnStride input countHead ((j : Int) + 1) countTape width prior) =
      some (config returnStride input countHead j countTape width prior) := by
  have hb : work width ((j : Int) + 1) = some width[j] := by
    rw [work_bit, List.getElem?_eq_getElem hj]
  have h : strideSkip.transition returnStride (readInput word input)
      (fun i : Fin 2 => if i = countBank then countTape countHead else work width ((j : Int) + 1)) =
      some (returnStride, .stay, only widthBank ⟨none, .left⟩, none) := by
    simp [strideSkip, walkStride, startStride, returnStride, banks_ne, hb]
  simpa [moveOffset] using
    width_step word width prior returnStride returnStride input countHead ((j : Int) + 1) countTape .stay .left h

private theorem stride_finish (word width prior : List Bool) (input countHead : Int)
    (countTape : Int → Option Bool) :
    strideSkip.step word (config returnStride input countHead 0 countTape width prior) =
      some (config (liftState 3) input countHead 0 countTape width prior) := by
  have h : strideSkip.transition returnStride (readInput word input)
      (fun i : Fin 2 => if i = countBank then countTape countHead else work width 0) =
      some (liftState 3, .stay, only widthBank ⟨none, .stay⟩, none) := by
    simp [strideSkip, walkStride, startStride, returnStride, banks_ne, work]
  simpa [moveOffset] using
    width_step word width prior returnStride (liftState 3) input countHead 0 countTape .stay .stay h

private theorem walk_prefix (word width prior : List Bool) (input countHead : Int)
    (countTape : Int → Option Bool) (j : Nat) (hj : j ≤ width.length) :
    strideSkip.runFrom word (config startStride input countHead 0 countTape width prior) (j + 1) =
      some (config walkStride (input + j) countHead ((j : Int) + 1) countTape width prior) := by
  induction j with
  | zero => simpa [SearchTransducer.runFrom] using stride_start word width prior input countHead countTape
  | succ j ih =>
    rw [SearchTransducer.runFrom, ih (by omega)]
    simpa [Int.add_assoc] using stride_move word width prior (input + j) countHead j (by omega) countTape

private theorem rewind_prefix (word width prior : List Bool) (input countHead : Int)
    (countTape : Int → Option Bool) (j : Nat) (hj : j ≤ width.length) :
    strideSkip.runFrom word (config startStride input countHead 0 countTape width prior)
        (width.length + 2 + j) =
      some (config returnStride (input + width.length) countHead (width.length - j : Nat) countTape width prior) := by
  induction j with
  | zero =>
    rw [Nat.add_zero, show width.length + 2 = (width.length + 1) + 1 by omega,
      SearchTransducer.runFrom, walk_prefix word width prior input countHead countTape width.length le_rfl]
    exact stride_turn word width prior _ countHead countTape
  | succ j ih =>
    rw [show width.length + 2 + (j + 1) = (width.length + 2 + j) + 1 by omega,
      SearchTransducer.runFrom, ih (by omega),
      show width.length - j = (width.length - (j + 1)) + 1 by omega]
    simpa using stride_back word width prior (input + width.length) countHead _ (by omega) countTape

/-- A single stride advances by the exact live width and preserves both banks. -/
theorem stride_correct (word width prior : List Bool) (input countHead : Int)
    (countTape : Int → Option Bool) :
    strideSkip.runFrom word (config startStride input countHead 0 countTape width prior)
        (width.length + 2 + width.length + 1) =
      some (config (liftState 3) (input + width.length) countHead 0 countTape width prior) := by
  rw [SearchTransducer.runFrom, rewind_prefix word width prior input countHead countTape width.length le_rfl,
    Nat.sub_self]
  exact stride_finish word width prior _ countHead countTape


private theorem config_bounded (word width prior : List Bool) (B : Nat) (q : Fin 13)
    (input countHead widthHead : Int) (countTape : Int → Option Bool)
    (hlo : (-1 : Int) ≤ input) (hhi : input ≤ word.length)
    (hc : countHead.natAbs ≤ B) (hw : widthHead.natAbs ≤ B) :
    strideSkip.Bounded word B (config q input countHead widthHead countTape width prior) := by
  refine ⟨hlo, hhi, fun i => ?_⟩
  rcases bank_cases i with rfl | rfl
  · simpa [config] using hc
  · simpa [config, banks_ne] using hw

private theorem one_step_segment (word : List Bool) (B : Nat) (c d : strideSkip.Config)
    (hs : strideSkip.step word c = some d) (hc : strideSkip.Bounded word B c)
    (hd : strideSkip.Bounded word B d) :
    strideSkip.BoundedSegment word B c d 1 := by
  have hr : strideSkip.runFrom word c 1 = some d := hs
  refine ⟨hr, fun k hk x hx => ?_⟩
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · change some c = some x at hx
    cases hx
    exact hc
  · rw [hr] at hx
    cases hx
    exact hd

theorem stride_segment (word width prior : List Bool) (B : Nat) (input countHead : Int)
    (countTape : Int → Option Bool) (hlo : (-1 : Int) ≤ input)
    (hhi : input + (width.length : Int) ≤ word.length)
    (hc : countHead.natAbs ≤ B) (hw : width.length + 1 ≤ B) :
    strideSkip.BoundedSegment word B (config startStride input countHead 0 countTape width prior)
      (config (liftState 3) (input + width.length) countHead 0 countTape width prior)
      (width.length + 2 + width.length + 1) := by
  have hr := stride_correct word width prior input countHead countTape
  refine ⟨hr, fun k hk x hx => ?_⟩
  by_cases hz : k = 0
  · subst k
    change some _ = some x at hx
    cases hx
    exact config_bounded word width prior B _ input countHead 0 countTape hlo (by omega) hc (by simp)
  by_cases hf : k ≤ width.length + 1
  · let j := k - 1
    have he : k = j + 1 := by dsimp [j]; omega
    rw [he, walk_prefix word width prior input countHead countTape j (by omega)] at hx
    cases hx
    exact config_bounded word width prior B _ _ countHead _ countTape (by omega) (by omega) hc (by omega)
  by_cases hb : k ≤ width.length + 2 + width.length
  · let j := k - (width.length + 2)
    have he : k = width.length + 2 + j := by dsimp [j]; omega
    rw [he, rewind_prefix word width prior input countHead countTape j (by omega)] at hx
    cases hx
    exact config_bounded word width prior B _ _ countHead _ countTape (by omega) hhi hc (by omega)
  · have he : k = width.length + 2 + width.length + 1 := by omega
    rw [he, hr] at hx
    cases hx
    exact config_bounded word width prior B _ _ countHead 0 countTape (by omega) hhi hc (by simp)
private theorem counter_input_irrelevant (q : Fin 10) (hq : q.val < 6)
    (input : InputCell) (read : Fin 1 → Option Bool) :
    skip.transition q input read = counterTransition q (read 0) := by
  interval_cases hv : q.val <;> simp [counterTransition, skip, hv]

private theorem counter_transition_shape (q d : Fin 10) (hq : q.val < 6) (b : Option Bool)
    (im : Move) (act : Fin 1 → Action (Option Bool)) (out : Option Bool)
    (h : counterTransition q b = some (d, im, act, out)) :
    d.val < 6 ∧ (im = .stay ∨ im = .right ∧ d = 3) := by
  cases b with
  | none =>
    interval_cases hv : q.val <;> simp [counterTransition, skip, hv] at h
    all_goals
      obtain ⟨rfl, rfl, _, _⟩ := h
      decide
  | some bit =>
    cases bit <;> interval_cases hv : q.val <;> simp [counterTransition, skip, hv] at h
    all_goals
      obtain ⟨rfl, rfl, _, _⟩ := h
      decide

def liftedConfig (base : Int) (width : List Bool) (c : skip.Config) : strideSkip.Config :=
  config (liftState c.state) (base + (width.length : Int) * c.inputHead)
    (c.workHead (0 : Fin 1)) 0 (c.workCell (0 : Fin 1)) width c.outputReversed

private theorem counter_lift_step (word width prior : List Bool)
    (q d : Fin 10) (hq : q.val < 6) (input head : Int) (cell : Int → Option Bool)
    (im : Move) (act : Fin 1 → Action (Option Bool)) (output : Option Bool)
    (h : counterTransition q (cell head) = some (d, im, act, output)) :
    strideSkip.step word (config (liftState q) input head 0 cell width prior) =
      some (config
        (match im with | .right => startStride | _ => liftState d)
        input (head + moveOffset (act 0).move) 0
        (fun j => if j = head then (act 0).write.getD (cell j) else cell j)
        width (output.elim prior (fun bit => bit :: prior))) := by
  have hq' : (liftState q).val < 6 := hq
  have str : fromState (liftState q) hq' = q := Fin.ext rfl
  have ht : strideSkip.transition (liftState q) (readInput word input)
      (fun i : Fin 2 => (if i = countBank then cell else work width)
        (if i = countBank then head else 0)) =
      some ((match im with | .right => startStride | _ => liftState d), .stay,
        only countBank (act 0), output) := by
    dsimp only [strideSkip]
    rw [dif_pos hq', str]
    simp only [if_true, h, Option.map_some]
    cases im <;> rfl
  unfold SearchTransducer.step
  rw [show strideSkip.transition (config (liftState q) input head 0 cell width prior).state
        (readInput word (config (liftState q) input head 0 cell width prior).inputHead)
        (fun i => (config (liftState q) input head 0 cell width prior).workCell i
          ((config (liftState q) input head 0 cell width prior).workHead i)) = _ from ht]
  simp only [config, Option.map_some, Option.some.injEq]
  congr 1
  · simp [moveOffset]
  · funext i
    rcases bank_cases i with rfl | rfl
    · simp [only]
    · simp [only, banks_ne, moveOffset]
  · funext i j
    rcases bank_cases i with rfl | rfl
    · simp [only]
    · simp only [only, banks_ne, if_false, Option.getD_none]
      exact ite_self _

theorem simulateStep (virtual raw width : List Bool) (base : Int)
    (c d : skip.Config) (hq : c.state.val < 6) (h : skip.step virtual c = some d) :
    d.state.val < 6 ∧ c.inputHead ≤ d.inputHead ∧ ∃ k,
      strideSkip.runFrom raw (liftedConfig base width c) k = some (liftedConfig base width d) ∧
      ∀ B, strideSkip.Bounded raw B (liftedConfig base width c) →
        strideSkip.Bounded raw B (liftedConfig base width d) → width.length + 1 ≤ B →
        strideSkip.BoundedSegment raw B (liftedConfig base width c) (liftedConfig base width d) k := by
  have hlegacy := counter_input_irrelevant c.state hq (readInput virtual c.inputHead)
    (fun i => c.workCell i (c.workHead i))
  unfold SearchTransducer.step at h
  cases ht₀ : skip.transition c.state (readInput virtual c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => simp only [ht₀, Option.map_none, reduceCtorEq] at h
  | some tr =>
    obtain ⟨q, im, acts, output⟩ := tr
    have ht := hlegacy.symm.trans ht₀
    have hshape := counter_transition_shape c.state q hq _ im acts output ht
    simp only [ht₀, Option.map_some, Option.some.injEq] at h
    subst d
    refine ⟨hshape.1, ?_, ?_⟩
    · rcases hshape.2 with rfl | ⟨rfl, _⟩ <;> simp [moveOffset]
    have hs := counter_lift_step raw width c.outputReversed c.state q hq
      (base + (width.length : Int) * c.inputHead) (c.workHead (0 : Fin 1)) (c.workCell (0 : Fin 1))
      im acts output ht
    rcases hshape.2 with rfl | ⟨rfl, rfl⟩
    · refine ⟨1, ?_, ?_⟩
      · simpa [runFrom, liftedConfig, moveOffset] using hs
      · intro B hc hd _
        exact one_step_segment raw B _ _ (by simpa [liftedConfig, moveOffset] using hs) hc hd
    · have hs' : strideSkip.runFrom raw (liftedConfig base width c) 1 =
        some (config startStride (base + (width.length : Int) * c.inputHead)
          (c.workHead (0 : Fin 1) + moveOffset (acts (0 : Fin 1)).move) 0
          (fun j => if j = c.workHead (0 : Fin 1) then (acts (0 : Fin 1)).write.getD (c.workCell (0 : Fin 1) j)
            else c.workCell (0 : Fin 1) j)
          width (output.elim c.outputReversed (fun bit => bit :: c.outputReversed))) := by
        simpa [runFrom, liftedConfig] using hs
      refine ⟨1 + (width.length + 2 + width.length + 1), ?_, ?_⟩
      · rw [runFrom_add, hs', Option.bind_some, stride_correct]
        simp [liftedConfig, moveOffset, Int.mul_add, Int.add_assoc]
      · intro B hc hd hw
        have hlo := hc.1
        have hhi := hd.2.1
        have hcount := hd.2.2 countBank
        simp [liftedConfig, moveOffset, Int.mul_add] at hhi hcount
        have hseg := stride_segment raw width (output.elim c.outputReversed (fun bit => bit :: c.outputReversed)) B
          (base + (width.length : Int) * c.inputHead)
          (c.workHead (0 : Fin 1) + moveOffset (acts (0 : Fin 1)).move)
          (fun j => if j = c.workHead (0 : Fin 1) then (acts (0 : Fin 1)).write.getD (c.workCell (0 : Fin 1) j)
            else c.workCell (0 : Fin 1) j)
          hlo (by simpa only [Int.add_assoc] using hhi) hcount hw
        have hmid := hseg.2 0 (Nat.zero_le _) _ rfl
        have hstep := one_step_segment raw B _ _ hs' hc hmid
        simpa [liftedConfig, moveOffset, Int.mul_add, Int.add_assoc] using
          BoundedSegment.append strideSkip hstep hseg

theorem simulateRun (virtual raw width : List Bool) (base : Int)
    (c d : skip.Config) (hq : c.state.val < 6) (ticks : Nat)
    (h : TableIO.afterFrom skip virtual c ticks = some d) :
    d.state.val < 6 ∧ c.inputHead ≤ d.inputHead ∧ ∃ k,
      strideSkip.runFrom raw (liftedConfig base width c) k = some (liftedConfig base width d) := by
  induction ticks generalizing d with
  | zero =>
    change some c = some d at h
    cases h
    exact ⟨hq, le_rfl, 0, rfl⟩
  | succ t ih =>
    rw [TableIO.afterFrom] at h
    cases hp : TableIO.afterFrom skip virtual c t with
    | none => simp [hp] at h
    | some e =>
      obtain ⟨he, hle, k, hk⟩ := ih e hp
      obtain ⟨hd, hle₂, j, hj, _⟩ := simulateStep virtual raw width base e d he (by simpa [hp] using h)
      exact ⟨hd, hle.trans hle₂, k + j, by rw [runFrom_add, hk, Option.bind_some, hj]⟩

/-- Starting on a supplied width bank, the physical counter advances by the
product of that width and the live binary count. -/
theorem skipStride_correct (word bits width prior : List Bool) (a : Nat) :
    ∃ k done, done.length = bits.length ∧
      strideSkip.runFrom word
        (liftedConfig a width (InputPosition.cfg bits 0 0 0 prior)) k =
      some (config (liftState 5) (a + (width.length : Int) * (digits bits : Int))
        0 0 (work done) width prior) ∧
      strideSkip.step word (config (liftState 5) (a + (width.length : Int) * (digits bits : Int))
        0 0 (work done) width prior) = none := by
  let virtual := List.replicate (digits bits) false
  have hv : 0 + digits bits ≤ virtual.length := by simp [virtual]
  obtain ⟨t, done, hlen, hr, _, _⟩ := InputPosition.skip_correct virtual bits prior 0 hv
  obtain ⟨_, _, k, hk⟩ := simulateRun virtual word width a _ _ (by change (0 : Nat) < 6; decide) t hr
  refine ⟨k, done, hlen, ?_, ?_⟩
  · simpa [liftedConfig, InputPosition.cfg] using hk
  · simp [SearchTransducer.step, strideSkip, liftState, fromState, counterTransition, skip]

theorem simulateRun_segment (virtual raw width : List Bool) (base : Int)
    (B : Nat) (c d : skip.Config) (hq : c.state.val < 6) (ticks : Nat)
    (h : TableIO.afterFrom skip virtual c ticks = some d) (hw : width.length + 1 ≤ B)
    (hbound : ∀ t x, TableIO.afterFrom skip virtual c t = some x →
      strideSkip.Bounded raw B (liftedConfig base width x)) :
    ∃ k, strideSkip.BoundedSegment raw B (liftedConfig base width c)
      (liftedConfig base width d) k := by
  induction ticks generalizing d with
  | zero =>
    change some c = some d at h
    cases h
    refine ⟨0, rfl, fun j hj x hx => ?_⟩
    have hj' : j = 0 := by omega
    subst j
    change some _ = some x at hx
    cases hx
    exact hbound 0 c rfl
  | succ t ih =>
    have hd := hbound (t + 1) d h
    rw [TableIO.afterFrom] at h
    cases hp : TableIO.afterFrom skip virtual c t with
    | none => simp [hp] at h
    | some e =>
      obtain ⟨k, hk⟩ := ih e hp
      have hstate := (simulateRun virtual raw width base c e hq t hp).1
      obtain ⟨_, _, j, _, hj⟩ := simulateStep virtual raw width base e d hstate
        (by simpa [hp] using h)
      exact ⟨k + j, BoundedSegment.append strideSkip hk (hj B (hbound t e hp) hd hw)⟩

/-- One binary count and one width bank suffice for an entire counted stride.
The common space bound is independent of the count and of the executed time. -/
theorem skipStride_bounded (word bits width prior : List Bool) (a : Nat)
    (hword : a + width.length * digits bits ≤ word.length) :
    ∃ k done, done.length = bits.length ∧
      strideSkip.BoundedSegment word (max bits.length width.length + 1)
        (liftedConfig a width (InputPosition.cfg bits 0 0 0 prior))
        (config (liftState 5) (a + (width.length : Int) * (digits bits : Int))
          0 0 (work done) width prior) k ∧
      strideSkip.step word (config (liftState 5) (a + (width.length : Int) * (digits bits : Int))
        0 0 (work done) width prior) = none := by
  let virtual := List.replicate (digits bits) false
  let start := InputPosition.cfg bits 0 0 0 prior
  have hv : 0 + digits bits ≤ virtual.length := by simp [virtual]
  have hs : start.state.val < 6 := by change (0 : Nat) < 6; decide
  obtain ⟨t, done, hlen, hr, _, hfront⟩ := InputPosition.skip_correct virtual bits prior 0 hv
  have hglobal (j : Nat) (x : skip.Config) (hx : TableIO.afterFrom skip virtual start j = some x) :
      strideSkip.Bounded word (max bits.length width.length + 1) (liftedConfig a width x) := by
    have hfront' := hfront j x hx
    have hmono := (simulateRun virtual word width a start x hs j hx).2.1
    have hlo : 0 ≤ x.inputHead := hmono
    have hhi : x.inputHead ≤ (digits bits : Int) := by
      simpa [virtual] using hfront'.2.1
    have hmul₀ : 0 ≤ (width.length : Int) * x.inputHead := Int.mul_nonneg (by omega) hlo
    have hmul₁ : (width.length : Int) * x.inputHead ≤ (width.length : Int) * (digits bits : Int) :=
      Int.mul_le_mul_of_nonneg_left hhi (by omega)
    have hword' : (a : Int) + (width.length : Int) * (digits bits : Int) ≤ (word.length : Int) := by
      exact_mod_cast hword
    have hcount := hfront'.2.2 (0 : Fin 1)
    apply config_bounded word width x.outputReversed
    · omega
    · omega
    · exact hcount.trans (Nat.add_le_add_right (le_max_left _ _) 1)
    · simp
  obtain ⟨k, hk⟩ := simulateRun_segment virtual word width a (max bits.length width.length + 1)
    start _ hs t hr (Nat.add_le_add_right (le_max_right _ _) 1) hglobal
  refine ⟨k, done, hlen, ?_, ?_⟩
  · simpa [start, liftedConfig, InputPosition.cfg] using hk
  · simp [SearchTransducer.step, strideSkip, liftState, fromState, counterTransition, skip]
end Mathproof.MinimumGeneration.StrideSkip
