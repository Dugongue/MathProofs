import Mathproof.MinimumGenerationTapeCompose
import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

noncomputable section

namespace Mathproof.MinimumGeneration.NativeReingoldLowering

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open SearchTransducer
open Turing (MultiTapeTM)

variable {K N : ℕ} {Q : Type*}

private def encodeState (layout : Q ≃ Fin N) : Option Q → Fin (N + 1)
  | none => 0
  | some q => (layout q).succ

private def decodeState (layout : Q ≃ Fin N) : Fin (N + 1) → Option Q :=
  Fin.cases none (fun i => some (layout.symm i))

@[simp] private theorem decode_encode (layout : Q ≃ Fin N) (q : Option Q) :
    decodeState layout (encodeState layout q) = q := by
  cases q <;> simp [decodeState, encodeState]

private def stripMarker : InputCell → Option Bool
  | .leftEnd | .rightEnd => none
  | .data bit => some bit

private def nativeMove : SignType → Move
  | .neg => .left
  | .zero => .stay
  | .pos => .right

private def clampMove (c : InputCell) (m : SignType) : Move :=
  match c, m with
  | .leftEnd, .neg | .rightEnd, .pos => .stay
  | _, m => nativeMove m

@[simp] private theorem offset_native (m : SignType) :
    moveOffset (nativeMove m) = (m.cast : Int) := by
  cases m <;> rfl

/-- Convert a finite binary CSLib controller to the project machine model.
A single terminal state preserves the final source transition's writes and
output. The endpoint markers implement the source input head's saturation. -/
def compile (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) : SearchTransducer where
  states := N + 1
  workTapes := K
  initialState := encodeState layout (some tm.q₀)
  transition state cell work := (decodeState layout state).map fun q =>
    let p := tm.tr q (stripMarker cell) work
    (encodeState layout p.state, clampMove cell p.inputTape,
      (fun t => ⟨(p.workTapes t).1, nativeMove (p.workTapes t).2⟩), p.output)

def project (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) {word : List Bool}
    (c : Turing.Cfg K Bool Q word) :
    (compile tm layout).Config :=
  ⟨encodeState layout c.state, (c.inputPos.val : Int) - 1,
    c.workTapePos, c.workTapes, c.output.reverse⟩

private theorem read_left (word : List Bool) (p : Fin (word.length + 2)) (h : p = 0) :
    readInput word ((p.val : Int) - 1) = .leftEnd := by
  subst p
  rfl

private theorem read_right (word : List Bool) (p : Fin (word.length + 2))
    (h : p.val = word.length + 1) :
    readInput word ((p.val : Int) - 1) = .rightEnd := by
  have hp : ((p.val : Int) - 1) = (word.length : Int) := by omega
  rw [hp]
  simp [readInput]

private theorem read_inner (word : List Bool) (p : Fin (word.length + 2))
    (hl : p ≠ 0) (hr : p.val ≠ word.length + 1) :
    readInput word ((p.val : Int) - 1) =
      .data (word[p.val - 1]'(by have hp := p.isLt; have hh : p.val ≠ 0 := fun he => hl (Fin.ext he); omega)) := by
  have hP : p.val ≠ 0 := fun he => hl (Fin.ext he)
  have hQ := p.isLt
  have hNum : 0 ≤ (p.val : Int) - 1 := by omega
  have hIndex : ((p.val : Int) - 1).toNat = p.val - 1 := by omega
  unfold readInput
  rw [if_neg (not_lt.mpr hNum), hIndex, List.getElem?_eq_getElem (by omega)]
  rfl

private theorem read_source {word : List Bool} (c : Turing.Cfg K Bool Q word) :
    stripMarker (readInput word ((c.inputPos.val : Int) - 1)) = c.inputSymbol := by
  by_cases hl : c.inputPos = 0
  · rw [read_left _ _ hl]
    simp [stripMarker, Turing.Cfg.inputSymbol, hl]
  · by_cases hr : c.inputPos.val = word.length + 1
    · rw [read_right _ _ hr]
      simp [stripMarker, Turing.Cfg.inputSymbol, hl, hr]
    · rw [read_inner _ _ hl hr]
      simp [stripMarker, Turing.Cfg.inputSymbol, hl, hr]

private theorem input_motion (word : List Bool) (p : Fin (word.length + 2)) (m : SignType) :
    ((Turing.moveInputPos p m).val : Int) - 1 = (p.val : Int) - 1 +
      moveOffset (clampMove (readInput word ((p.val : Int) - 1)) m) := by
  cases m with
  | zero =>
    have hmove : Turing.moveInputPos p .zero = p := Turing.moveInputPos_zero p
    rw [hmove]
    cases readInput word ((p.val : Int) - 1) <;> simp [clampMove, nativeMove, moveOffset]
  | neg =>
    by_cases hl : p = 0
    · subst p
      have hmove : Turing.moveInputPos (0 : Fin (word.length + 2)) .neg = 0 :=
        Turing.moveInputPos_leftBoundary
      rw [hmove, read_left word 0 rfl]
      rfl
    · rw [Turing.moveInputPos_neg_of_ne_left p hl]
      have hP : p.val ≠ 0 := fun he => hl (Fin.ext he)
      by_cases hr : p.val = word.length + 1
      · rw [read_right _ _ hr]
        simp only [clampMove, nativeMove, moveOffset]
        omega
      · rw [read_inner _ _ hl hr]
        simp only [clampMove, nativeMove, moveOffset]
        omega
  | pos =>
    by_cases hr : p.val = word.length + 1
    · have he : p = (⟨word.length + 1, by omega⟩ : Fin (word.length + 2)) := Fin.ext hr
      rw [read_right _ _ hr]
      have hmove : Turing.moveInputPos p .pos = p := by
        rw [he]
        exact Turing.moveInputPos_rightBoundary
      rw [hmove]
      simp [clampMove, moveOffset, hr]
    · rw [Turing.moveInputPos_pos_of_ne_right p hr]
      by_cases hl : p = 0
      · rw [read_left _ _ hl]
        simp only [clampMove, nativeMove, moveOffset]
        omega
      · rw [read_inner _ _ hl hr]
        simp only [clampMove, nativeMove, moveOffset]
        omega

/-- Compile each physical instruction including writes on the terminal step. -/
theorem step_exact (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) {word : List Bool}
    (c : Turing.Cfg K Bool Q word) :
    (compile tm layout).step word (project tm layout c) =
      if c.state = none then none else some (project tm layout (tm.step c)) := by
  cases h : c.state with
  | none => simp [SearchTransducer.step, compile, project, h]
  | some q =>
    rw [tm.step_of_state h, if_neg (by exact Option.some_ne_none _)]
    unfold SearchTransducer.step
    simp only [compile, project, decode_encode, h, Option.map_some]
    rw [read_source]
    set act := tm.tr q c.inputSymbol c.workTapeSymbols

    change some (⟨encodeState layout act.state, _,
      (fun i => c.workTapePos i + moveOffset (nativeMove (act.workTapes i).2)), _,
      act.output.elim c.output.reverse (fun bit => bit :: c.output.reverse)⟩ : (compile tm layout).Config) = _
    simp only [Turing.Action.apply, offset_native, input_motion,
      List.reverse_append]
    congr 2
    · funext i j
      have hAct : tm.tr q c.inputSymbol (fun b => c.workTapes b (c.workTapePos b)) = act := rfl
      rw [hAct]
      cases hw : (act.workTapes i).1 <;>
        by_cases hj : j = c.workTapePos i <;> simp [hw, hj, Function.update]
    · cases act.output <;> rfl

theorem initial_exact (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) (word : List Bool) :
    (compile tm layout).initial = project tm layout (tm.initCfg word) := by
  simp [SearchTransducer.initial, project, compile, Turing.MultiTapeNTM.initCfg, Turing.Cfg.init]

theorem run_exact (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) {word : List Bool}
    (c : Turing.Cfg K Bool Q word) (n : Nat)
    (running : ∀ j < n, (tm.runFrom c j).state ≠ none) :
    (compile tm layout).runFrom word (project tm layout c) n =
      some (project tm layout (tm.runFrom c n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SearchTransducer.runFrom, ih (fun j hj => running j (by omega)), Option.bind_some,
      step_exact, if_neg (running n (by omega))]
    change _ = some (project tm layout (tm.step^[Nat.succ n] c))
    rw [Function.iterate_succ_apply']
    rfl

private theorem work_bound (tm : MultiTapeTM K Bool Q) {word : List Bool}
    {s : Nat} (space : tm.RunsInSpace word s) (j : Nat) (bank : Fin K) :
    ((tm.runFrom (tm.initCfg word) j).workTapePos bank).natAbs ≤ s := by
  let p := Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm word j
  have hWindow := Turing.MultiTapeNTM.RunPath.inWindow_of_space_le (p := p.toRunPath)
    (fun i => by rw [p.head_eq]; rfl) (space p)
  have hw := hWindow p.last p.toRunPath.last_mem bank
  rw [Turing.mem_window] at hw
  rw [tm.computationPath_last_eq_runFrom] at hw
  exact hw

/-- An actual bounded native physical run yields an exact transducer run. -/
theorem compile_correct (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N)
    (word answer : List Bool) (t s : Nat)
    (cert : tm.ComputesInTimeAndSpace word answer t s) :
    ∃ k result,
      (compile tm layout).BoundedSegment word s (compile tm layout).initial result k ∧
      (compile tm layout).step word result = none ∧ result.outputReversed.reverse = answer := by
  let start := tm.initCfg word
  obtain ⟨u, hHalt, hAnswer⟩ := cert.1
  have existsHalt : ∃ k, (tm.runFrom start k).state = none := ⟨u, hHalt⟩
  classical
  let first := Nat.find existsHalt
  have hf : (tm.runFrom start first).state = none := Nat.find_spec existsHalt
  have hFirst : first ≤ u := Nat.find_min' existsHalt hHalt
  have hBefore (j : Nat) (hj : j < first) : (tm.runFrom start j).state ≠ none :=
    Nat.find_min existsHalt hj
  let result := project tm layout (tm.runFrom start first)
  refine ⟨first, result, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [initial_exact]
    exact run_exact tm layout start first hBefore
  · intro j hj c he
    rw [initial_exact, run_exact tm layout start j (fun i hi => hBefore i (by omega))] at he
    have hEq := Option.some.inj he
    subst c
    have hPos := (tm.runFrom start j).inputPos.isLt
    have hNonnegative := Nat.zero_le (tm.runFrom start j).inputPos.val
    refine ⟨?_, ?_, fun b => work_bound tm cert.2.2 j b⟩
    · change (-1 : Int) ≤ ((tm.runFrom start j).inputPos.val : Int) - 1
      omega
    · change ((tm.runFrom start j).inputPos.val : Int) - 1 ≤ (word.length : Int)
      omega
  · exact (step_exact tm layout _).trans (if_pos hf)
  · rw [tm.runFrom_eq_of_halt start hFirst hf] at hAnswer
    simpa [result, project] using hAnswer

/-- One compiled binary machine inherits the input-dependent logarithmic
workspace and the literal output for the entire promised input family. -/
theorem compile_logspace (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N)
    {X : Type*} (encode : X → List Bool) (answer : X → List Bool)
    (C : ℕ) (h : ∀ x, ∃ t s,
      s ≤ C * (Nat.log2 ((encode x).length + 1) + 1) ∧
      tm.ComputesInTimeAndSpace (encode x) (answer x) t s) :
    ∀ x, (compile tm layout).logarithmicWorkspace C (encode x) ∧
      (compile tm layout).outputs (encode x) (answer x) := by
  intro x
  obtain ⟨t, s, hb, hs⟩ := h x
  obtain ⟨k, result, run, stop, output⟩ :=
    compile_correct tm layout (encode x) (answer x) t s hs
  have widened : (compile tm layout).BoundedSegment (encode x)
      (C * (Nat.log2 ((encode x).length + 1) + 1)) (compile tm layout).initial result k :=
    ⟨run.1, fun j hj c hc => by
      obtain ⟨hL, hR, hW⟩ := run.2 j hj c hc
      exact ⟨hL, hR, fun b => (hW b).trans hb⟩⟩
  rw [← output]
  exact BoundedSegment.logspaceOutput (compile tm layout) widened stop

end Mathproof.MinimumGeneration.NativeReingoldLowering
