import Mathproof.MinimumGenerationReingoldGeneratorStream

namespace Mathproof.MinimumGeneration.ReingoldPositiveStream

open SearchTransducer ReingoldGeneratorStream
open ReingoldLiveInput (difference signedTrialMachine)

set_option backward.isDefEq.respectTransparency false

variable {S W : Nat} (R : LabelReader S W) (fit : signedTrialMachine.states ≤ S)
  (e : Fin signedTrialMachine.workTapes ↪ Fin W)

abbrev scanMachine := ReingoldGeneratorStream.machine R fit e

def scanBit (q : Fin (2 * S)) : Bool :=
  let (i, s) := finProdFinEquiv.symm q
  if i = (0 : Fin 2) then false else trialAccept s.val

abbrev stages (resetEntry : Fin (2 * S)) (reset : MacroTransition (2 * S) W) : Stages 3 (2 * S) W where
  first := 0
  entry i := if i = 1 then resetEntry else (scanMachine R fit e).initialState
  transition i := if i = 1 then reset else (scanMachine R fit e).transition
  next i q :=
    if i = 0 then (if scanBit q then none else some 1)
    else if i = 1 then some 2 else none

def verdict {resetEntry : Fin (2 * S)} {reset : MacroTransition (2 * S) W}
    (c : (stages R fit e resetEntry reset).machine.Config) : Bool :=
  let (i, q) := finProdFinEquiv.symm c.state
  if i = (1 : Fin 3) then false else scanBit q

def labels {n m : Nat} (gen : Fin m → Fin n) (x y : Fin n) : List (Fin n) :=
  if x = y then [] else List.ofFn gen

theorem labels_adjacency {n m : Nat} (G : Group (Fin n))
    (gen : Fin m → Fin n) (x y : Fin n) :
    (difference G x y ∈ labels gen x y ∨ difference G y x ∈ labels gen x y) ↔
      (@SimpleGraph.mulCayley (Fin n) (Set.range gen) G.toMul).Adj x y := by
  let _ : Group (Fin n) := G
  let _ : Mul (Fin n) := G.toMul
  let _ : Inv (Fin n) := G.toInv
  rw [SimpleGraph.mulCayley_adj]
  by_cases h : x = y
  · simp [labels, h]
  · simp [labels, h, difference, List.mem_ofFn, Set.mem_range]
    rfl

/-- After a rejection in the first direction, the supplied physical reset starts
the same scanner on the same positive labels with the endpoints exchanged.
The protected banks and prior output are carried across both passes. -/
theorem execute {n m : Nat} (G : Group (Fin n)) (gen : Fin m → Fin n) (x y : Fin n)
    (C : Nat) (hC : 3 ≤ C) (keep : Set (Fin W)) (hkeep : keep ⊆ (Set.range e)ᶜ)
    (F Bwd : List (Fin n) → readerConfig R fit e → Prop)
    (front : Contract R fit e G x y (C * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1)) keep F)
    (back : Contract R fit e G y x (C * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1)) keep Bwd)
    (resetEntry : Fin (2 * S)) (reset : MacroTransition (2 * S) W)
    (c : readerConfig R fit e) (hc : F (labels gen x y) c)
    (resetOK :
      let word := @encodeCayley n G.toMul
      let cap := C * (Nat.log2 (word.length + 1) + 1)
      let T := stages R fit e resetEntry reset
      ∀ (p : Nat) (d : (scanMachine R fit e).Config),
        (scanMachine R fit e).BoundedSegment word cap
          ((ReingoldGeneratorStream.stages R fit e).tag 0 c) d p →
        (scanMachine R fit e).step word d = none →
        ReingoldGeneratorStream.verdict R fit e d = false →
        d.outputReversed = c.outputReversed →
        SameOn keep c.workHead d.workHead c.workCell d.workCell →
        ∃ (k : Nat) (q : (T.component 1).Config) (c' : readerConfig R fit e),
          (T.component 1).BoundedSegment word cap (T.enter (i := 0) 1 d) q k ∧
          (T.component 1).step word q = none ∧
          T.enter 2 q = (ReingoldGeneratorStream.stages R fit e).tag 0 c' ∧
          Bwd (labels gen x y) c' ∧
          c'.outputReversed = d.outputReversed ∧ SameOn keep d.workHead c'.workHead d.workCell c'.workCell) :
    let word := @encodeCayley n G.toMul
    let cap := C * (Nat.log2 (word.length + 1) + 1)
    let T := stages R fit e resetEntry reset
    ∃ (k : Nat) (d : T.machine.Config),
      T.machine.BoundedSegment word cap
        (T.tag 0 ((ReingoldGeneratorStream.stages R fit e).tag 0 c)) d k ∧
      T.machine.step word d = none ∧
      (verdict R fit e d = true ↔ (@SimpleGraph.mulCayley (Fin n) (Set.range gen) G.toMul).Adj x y) ∧
      d.outputReversed = c.outputReversed ∧ SameOn keep c.workHead d.workHead c.workCell d.workCell := by
  let T := stages R fit e resetEntry reset
  obtain ⟨p, d, first, hStop, hBit, hOut, hFrame⟩ :=
    executeLabelStream R fit e G x y C hC keep hkeep F front (labels gen x y) c hc
  cases hb : ReingoldGeneratorStream.verdict R fit e d with
  | true =>
    have hn : T.next 0 d.state = none := by
      change (if scanBit d.state then none else some 1) = none
      change scanBit d.state = true at hb
      rw [hb]
      rfl
    obtain ⟨hRun, halt⟩ := T.routed_stop (Stages.Routed.finish (i := 0) first) hStop hn
    refine ⟨p, T.tag 0 d, hRun, halt, ?_, hOut, hFrame⟩
    have hmem := hBit.mp hb
    rw [← labels_adjacency G gen x y]
    have hs : verdict R fit e (T.tag 0 d) = true := by
      change scanBit d.state = true at hb
      simpa [verdict, Stages.tag] using hb
    simp [hs, hmem]
  | false =>
    have hn : T.next 0 d.state = some 1 := by
      change (if scanBit d.state then none else some 1) = some 1
      change scanBit d.state = false at hb
      rw [hb]
      rfl
    obtain ⟨r, q, c', hReset, hResetStop, join, ready, out, frame⟩ := resetOK p d first hStop hb hOut hFrame
    obtain ⟨z, t, second, hSecondStop, hSecondBit, hSecondOut, hSecondFrame⟩ :=
      executeLabelStream R fit e G y x C hC keep hkeep Bwd back (labels gen x y) c' ready
    rw [← join] at second
    have ht : T.next 1 q.state = some 2 := by simp [T, show (1 : Fin 3) ≠ 0 by decide]
    have hEnd : T.next 2 t.state = none := by
      simp [T, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
    obtain ⟨hRun, hHalt⟩ := T.routed_stop
      (Stages.Routed.call (T := T) (i := 0) (j := 1) first hStop hn
        (Stages.Routed.call (T := T) (i := 1) (j := 2) hReset hResetStop ht (.finish second))) hSecondStop hEnd
    refine ⟨p + 1 + (r + 1 + z), T.tag 2 t, hRun, hHalt, ?_,
      hSecondOut.trans (out.trans hOut), hFrame.trans (frame.trans hSecondFrame)⟩
    have hmiss : difference G x y ∉ labels gen x y := by
      intro hm
      have he := hBit.mpr hm
      rw [hb] at he
      contradiction
    rw [← labels_adjacency G gen x y]
    have he : verdict R fit e (T.tag 2 t) = ReingoldGeneratorStream.verdict R fit e t := by
      simp [verdict, Stages.tag, show (2 : Fin 3) ≠ 1 by decide]
      rfl
    simpa only [he, hmiss, false_or] using hSecondBit

end Mathproof.MinimumGeneration.ReingoldPositiveStream
