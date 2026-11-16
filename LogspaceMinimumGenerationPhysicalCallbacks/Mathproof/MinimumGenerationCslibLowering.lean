import Mathproof.MinimumGenerationTapeCompose
import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

namespace Mathproof.MinimumGeneration.CslibLowering

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
abbrev compile (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) : SearchTransducer where
  states := N + 1
  workTapes := K
  initialState := encodeState layout (some tm.q₀)
  transition state cell work := (decodeState layout state).map fun q =>
    let p := tm.tr q (stripMarker cell) work
    (encodeState layout p.q', clampMove cell p.inputMove,
      (fun t => ⟨(p.workActions t).1, nativeMove (p.workActions t).2⟩), p.outS)

def project (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) {word : List Bool}
    (c : MultiTapeTM.Cfg K Bool Q word) (outReversed : List Bool) :
    (compile tm layout).Config :=
  ⟨encodeState layout c.state, (c.inputPos.val : Int) - 1,
    c.workTapePos, c.workTapes, outReversed⟩

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

private theorem read_source {word : List Bool} (c : MultiTapeTM.Cfg K Bool Q word) :
    stripMarker (readInput word ((c.inputPos.val : Int) - 1)) = c.inputSymbol := by
  by_cases hl : c.inputPos = 0
  · rw [read_left _ _ hl]
    simp [stripMarker, MultiTapeTM.Cfg.inputSymbol, hl]
  · by_cases hr : c.inputPos.val = word.length + 1
    · rw [read_right _ _ hr]
      simp [stripMarker, MultiTapeTM.Cfg.inputSymbol, hl, hr]
    · rw [read_inner _ _ hl hr]
      simp [stripMarker, MultiTapeTM.Cfg.inputSymbol, hl, hr]

private theorem input_motion (word : List Bool) (p : Fin (word.length + 2)) (m : SignType) :
    ((MultiTapeTM.moveInputPos p m).val : Int) - 1 = (p.val : Int) - 1 +
      moveOffset (clampMove (readInput word ((p.val : Int) - 1)) m) := by
  cases m with
  | zero =>
    have hmove : MultiTapeTM.moveInputPos p .zero = p := MultiTapeTM.moveInputPos_zero p
    rw [hmove]
    cases readInput word ((p.val : Int) - 1) <;> simp [clampMove, nativeMove, moveOffset]
  | neg =>
    by_cases hl : p = 0
    · subst p
      have hmove : MultiTapeTM.moveInputPos (0 : Fin (word.length + 2)) .neg = 0 :=
        MultiTapeTM.moveInputPos_leftBoundary
      rw [hmove, read_left word 0 rfl]
      rfl
    · rw [MultiTapeTM.moveInputPos_neg_of_ne_left p hl]
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
      have hmove : MultiTapeTM.moveInputPos p .pos = p := by
        rw [he]
        exact MultiTapeTM.moveInputPos_rightBoundary
      rw [hmove]
      simp [clampMove, moveOffset, hr]
    · rw [MultiTapeTM.moveInputPos_pos_of_ne_right p hr]
      by_cases hl : p = 0
      · rw [read_left _ _ hl]
        simp only [clampMove, nativeMove, moveOffset]
        omega
      · rw [read_inner _ _ hl hr]
        simp only [clampMove, nativeMove, moveOffset]
        omega

/-- Running one compiled instruction is exact even on the final transition
that changes the native state to `none`. Once in that state the compiled
machine has no additional transitions. -/
theorem step_exact (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) {word : List Bool}
    (c : MultiTapeTM.Cfg K Bool Q word) (outReversed : List Bool) :
    (compile tm layout).step word (project tm layout c outReversed) =
      if c.state = none then none else
        some (project tm layout (tm.step c)
          ((tm.outputSymbol c).elim outReversed (fun b => b :: outReversed))) := by
  unfold SearchTransducer.step
  cases h : c.state with
  | none => simp [compile, project, h]
  | some q =>
    simp only [compile, project, decode_encode, h, Option.map_some, Option.some_ne_none,
      if_false, Turing.MultiTapeTM.step, Turing.MultiTapeTM.outputSymbol]
    rw [read_source]
    simp only [Option.some.injEq, offset_native, input_motion]
    congr 1
    funext t j
    have symbols : c.workTapeSymbols = (fun i => c.workTapes i (c.workTapePos i)) := rfl
    rw [symbols]
    cases hw : ((tm.tr q c.inputSymbol (fun i => c.workTapes i (c.workTapePos i))).workActions t).1 <;>
      by_cases hj : j = c.workTapePos t <;> simp [hw, hj, Function.update]


/-- The two versions have the same blank start. -/
theorem initial_exact (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) (word : List Bool) :
    (compile tm layout).initial = project tm layout (tm.initCfg word) [] := by
  simp [SearchTransducer.initial, project, MultiTapeTM.initCfg]

/-- Exact prefix execution up through the first halt, including output from
the native final instruction. -/
theorem run_exact (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N) {word : List Bool}
    (c : MultiTapeTM.Cfg K Bool Q word) (prior : List Bool) (steps : ℕ)
    (running : ∀ j < steps, (tm.configs c j).state ≠ none) :
    (compile tm layout).runFrom word (project tm layout c prior) steps =
      some (project tm layout (tm.configs c steps) ((tm.outputString c steps).reverse ++ prior)) := by
  induction steps with
  | zero => simp [runFrom, MultiTapeTM.outputString]
  | succ k ih =>
    rw [runFrom, ih (fun j hj => running j (by omega)), Option.bind_some, step_exact]
    rw [if_neg (running k (by omega)), MultiTapeTM.configs_succ_eq_step', MultiTapeTM.outputString_succ,
      List.reverse_append]
    cases tm.outputSymbol (tm.configs c k) <;> rfl

private theorem work_bound (tm : MultiTapeTM K Bool Q) (word : List Bool)
    {k t : ℕ} (ht : k ≤ t) (bank : Fin K) :
    ((tm.configs (tm.initCfg word) k).workTapePos bank).natAbs ≤ tm.spaceUsed (tm.initCfg word) t := by
  have visits := Finset.card_le_card (tm.uIcc_workTapePos_subset_visitedByTapeHead (tm.initCfg word) bank k)
  rw [Int.card_uIcc] at visits
  simp only [MultiTapeTM.initCfg, sub_zero] at visits
  have monotone := Finset.card_le_card (tm.visitedByTapeHead_mono (tm.initCfg word) bank ht)
  have total := tm.spaceUsedByTape_le_spaceUsed (tm.initCfg word) t bank
  change _ ≤ tm.spaceUsedByTape (tm.initCfg word) k bank at visits
  change tm.spaceUsedByTape (tm.initCfg word) k bank ≤ tm.spaceUsedByTape (tm.initCfg word) t bank at monotone
  exact (Nat.le_succ _).trans (visits.trans (monotone.trans total))

/-- A checked native finite-controller execution is lowered to one actual
project transducer execution. The native visited-cell bound dominates the
absolute work-head bound, and the last output symbol is retained. -/
theorem compile_correct (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N)
    (word answer : List Bool) (t s : ℕ)
    (cert : tm.ComputesInTimeAndSpace word answer t s) :
    ∃ (k : ℕ) (result : (compile tm layout).Config), k ≤ t ∧
      (compile tm layout).BoundedSegment word s (compile tm layout).initial result k ∧
      (compile tm layout).step word result = none ∧ result.outputReversed.reverse = answer := by
  let start := tm.initCfg word
  let stopped (k : Nat) := (tm.configs start k).state = none
  have terminates : ∃ k, stopped k := ⟨t, cert.1⟩
  classical
  let first := Nat.find terminates
  have hf : stopped first := Nat.find_spec terminates
  have ht : first ≤ t := Nat.find_min' terminates cert.1
  have hrun (j : Nat) (hj : j < first) : (tm.configs start j).state ≠ none :=
    Nat.find_min terminates hj
  let result := project tm layout (tm.configs start first) ((tm.outputString start first).reverse ++ [])
  refine ⟨first, result, ht, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [initial_exact]
    exact run_exact tm layout start [] first hrun
  · intro j hj c hc
    rw [initial_exact, run_exact _ _ _ _ _ (fun a ha => hrun a (by omega))] at hc
    have hej := Option.some.inj hc
    subst c
    have hpos := (tm.configs start j).inputPos.isLt
    have hnonneg := Nat.zero_le (tm.configs start j).inputPos.val
    refine ⟨?_, ?_, fun bank => ?_⟩
    · change (-1 : Int) ≤ ((tm.configs start j).inputPos.val : Int) - 1
      omega
    · change ((tm.configs start j).inputPos.val : Int) - 1 ≤ (word.length : Int)
      omega
    · change ((tm.configs start j).workTapePos bank).natAbs ≤ s
      exact (work_bound tm word (hj.trans ht) bank).trans_eq cert.2.2
  · rw [step_exact, if_pos hf]
  · change (((tm.outputString start first).reverse ++ []).reverse) = answer
    simp only [List.append_nil, List.reverse_reverse]
    exact (tm.outputString_eq_of_halt start ht hf).symm.trans cert.2.1

/-- A single input-independent project machine inherits the certified
logarithmic bound of a native binary machine, on every promised input. -/
theorem compile_logspace (tm : MultiTapeTM K Bool Q) (layout : Q ≃ Fin N)
    {X : Type*} (encode : X → List Bool) (answer : X → List Bool)
    (C : ℕ) (h : ∀ x, ∃ t s,
      s ≤ C * (Nat.log2 ((encode x).length + 1) + 1) ∧
      tm.ComputesInTimeAndSpace (encode x) (answer x) t s) :
    ∀ x, (compile tm layout).logarithmicWorkspace C (encode x) ∧
      (compile tm layout).outputs (encode x) (answer x) := by
  intro x
  obtain ⟨t, s, hb, hs⟩ := h x
  obtain ⟨k, result, _, run, stop, output⟩ :=
    compile_correct tm layout (encode x) (answer x) t s hs
  have widened : (compile tm layout).BoundedSegment (encode x)
      (C * (Nat.log2 ((encode x).length + 1) + 1)) (compile tm layout).initial result k :=
    ⟨run.1, fun j hj c hc => by
      obtain ⟨hL, hR, hW⟩ := run.2 j hj c hc
      exact ⟨hL, hR, fun b => (hW b).trans hb⟩⟩
  rw [← output]
  exact BoundedSegment.logspaceOutput (compile tm layout) widened stop

end Mathproof.MinimumGeneration.CslibLowering
