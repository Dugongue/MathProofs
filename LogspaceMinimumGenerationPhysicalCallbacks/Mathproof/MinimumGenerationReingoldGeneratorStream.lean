import Mathproof.MinimumGenerationReingoldLiveInput
import Mathproof.MinimumGenerationMacroDispatch

namespace Mathproof.MinimumGeneration.ReingoldGeneratorStream

open SearchTransducer
open ReingoldLiveInput (difference signedTrialMachine signedTrialStart signedTrialVerdict)

set_option backward.isDefEq.respectTransparency false

/-- Physical code for reading the next signed label. Exhaustion versus a
prepared trial is signalled by the finite control. -/
structure LabelReader (S W : Nat) where
  start : Fin S
  transition : MacroTransition S W
  ready : Fin S → Bool

def trialAccept (q : Nat) : Bool :=
  decide (q = LiveInverse.machine.states + (TapeRegisters.done true).val)

abbrev stages {S W : Nat} (R : LabelReader S W) (fit : signedTrialMachine.states ≤ S)
    (e : Fin signedTrialMachine.workTapes ↪ Fin W) : Stages 2 S W where
  first := 0
  entry i := if i = 0 then R.start else signedTrialMachine.initialState.castLE fit
  transition i := if i = 0 then R.transition else signedTrialMachine.padTransition fit e
  next i q := if i = 0 then (if R.ready q then some 1 else none)
    else (if trialAccept q.val then none else some 0)

variable {S W : Nat} (R : LabelReader S W) (fit : signedTrialMachine.states ≤ S)
  (e : Fin signedTrialMachine.workTapes ↪ Fin W)

abbrev machine := (stages R fit e).machine

abbrev readerConfig := ((stages R fit e).component 0).Config

abbrev trialConfig := ((stages R fit e).component 1).Config

/-- The resulting bit is held in the control, with the previous output intact. -/
def verdict (c : (machine R fit e).Config) : Bool :=
  let (i, q) := finProdFinEquiv.symm c.state
  if i = 0 then false else trialAccept q.val

@[simp] theorem verdict_reader (c : readerConfig R fit e) :
    verdict R fit e ((stages R fit e).tag 0 c) = false := by
  simp [verdict, Stages.tag]

@[simp] theorem verdict_trial (c : trialConfig R fit e) :
    verdict R fit e ((stages R fit e).tag 1 c) = trialAccept c.state.val := by
  simp [verdict, Stages.tag, show (1 : Fin 2) ≠ 0 by decide]

/-- Heads and cells of all indicated banks are equal. Across a trial this holds
for every bank outside the ten designated trial banks. -/
def SameOn (keep : Set (Fin W)) (leftHead rightHead : Fin W → Int)
    (leftCell rightCell : Fin W → Int → Option Bool) : Prop :=
  ∀ i ∈ keep, leftHead i = rightHead i ∧ leftCell i = rightCell i

namespace SameOn

theorem trans {keep : Set (Fin W)} {a b c : Fin W → Int}
    {x y z : Fin W → Int → Option Bool}
    (hab : SameOn keep a b x y) (hbc : SameOn keep b c y z) : SameOn keep a c x z :=
  fun i hi => ⟨(hab i hi).1.trans (hbc i hi).1, (hab i hi).2.trans (hbc i hi).2⟩

end SameOn

def trialEntry (n x y label : Nat) (prior : List Bool)
    (heads : Fin W → Int) (cells : Fin W → Int → Option Bool) : trialConfig R fit e :=
  signedTrialMachine.padConfig fit e
    (signedTrialMachine.bankConfig e (signedTrialStart n x y label prior) heads cells)

theorem trialSegment {n B : Nat} (G : Group (Fin n)) (x y label : Fin n)
    (prior : List Bool) (heads : Fin W → Int) (cells : Fin W → Int → Option Bool)
    (hwidth : 3 * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1) ≤ B)
    (hframe : ∀ i ∉ Set.range e, (heads i).natAbs ≤ B) :
    let word := @encodeCayley n G.toMul
    ∃ (k : Nat) (result : trialConfig R fit e),
      ((stages R fit e).component 1).BoundedSegment word B
        (trialEntry R fit e n x.val y.val label.val prior heads cells) result k ∧
      ((stages R fit e).component 1).step word result = none ∧
      (trialAccept result.state.val = true ↔ difference G x y = label) ∧
      result.outputReversed = prior ∧
      SameOn (Set.range e)ᶜ heads result.workHead cells result.workCell := by
  let word := @encodeCayley n G.toMul
  let P := signedTrialMachine
  obtain ⟨k, stop, run, halt, accept, output, _, _⟩ :=
    ReingoldLiveInput.signedTrial_execute n G x y label prior
  let lifted := P.bankConfig e stop heads cells
  let result : trialConfig R fit e := P.padConfig fit e lifted
  have runBound := PhysicalEntry.segment_mono run hwidth
  have active := P.relocateBanks_segment e runBound (heads := heads) (cells := cells) hframe
  have segment := P.padMachine_segment fit e active
  refine ⟨k, result, segment, ?_, accept, output, ?_⟩
  · change (P.padMachine fit e).step word result = none
    unfold result lifted
    rw [P.padMachine_step, P.relocateBanks_step, halt]
    rfl
  · intro j hj
    obtain ⟨hh,hc⟩ := P.bankConfig_frame e stop heads cells hj
    exact ⟨hh.symm, hc.symm⟩

/-- Each leaf is the checked execution of the supplied reader on the same
physical input word. For a label leaf, the post-read cursor is carried in
banks outside the trial layout, so the reader can resume after the trial. -/
structure Contract {n : Nat} (G : Group (Fin n)) (x y : Fin n) (B : Nat)
    (keep : Set (Fin W)) (Ready : List (Fin n) → readerConfig R fit e → Prop) : Prop where
  readEmpty : ∀ c, Ready [] c →
    ∃ (k : Nat) (d : readerConfig R fit e),
      ((stages R fit e).component 0).BoundedSegment (@encodeCayley n G.toMul) B c d k ∧
      ((stages R fit e).component 0).step (@encodeCayley n G.toMul) d = none ∧
      R.ready d.state = false ∧ d.outputReversed = c.outputReversed ∧
      SameOn keep c.workHead d.workHead c.workCell d.workCell
  readLabel : ∀ label left c, Ready (label :: left) c →
    ∃ (k : Nat) (d : readerConfig R fit e),
      ((stages R fit e).component 0).BoundedSegment (@encodeCayley n G.toMul) B c d k ∧
      ((stages R fit e).component 0).step (@encodeCayley n G.toMul) d = none ∧
      R.ready d.state = true ∧
      (stages R fit e).enter 1 d =
        trialEntry R fit e n x.val y.val label.val c.outputReversed d.workHead d.workCell ∧
      SameOn keep c.workHead d.workHead c.workCell d.workCell ∧
      ∀ (l : Nat) (z : trialConfig R fit e),
        ((stages R fit e).component 1).BoundedSegment (@encodeCayley n G.toMul) B
          ((stages R fit e).enter 1 d) z l →
        ((stages R fit e).component 1).step (@encodeCayley n G.toMul) z = none →
        z.outputReversed = c.outputReversed →
        SameOn (Set.range e)ᶜ d.workHead z.workHead d.workCell z.workCell →
        Ready left ((stages R fit e).enter 0 z)

private theorem routedLabelStream {n B : Nat} (G : Group (Fin n)) (x y : Fin n)
    (keep : Set (Fin W)) (hkeep : keep ⊆ (Set.range e)ᶜ)
    (Ready : List (Fin n) → readerConfig R fit e → Prop)
    (hR : Contract R fit e G x y B keep Ready)
    (hwidth : 3 * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1) ≤ B)
    (labels : List (Fin n)) (c : readerConfig R fit e) (hc : Ready labels c) :
    let word := @encodeCayley n G.toMul
    let T := stages R fit e
    ∃ (k : Nat) (i : Fin 2) (d : (T.component i).Config),
      T.Routed word B 0 c i d k ∧
      (T.component i).step word d = none ∧ T.next i d.state = none ∧
      (verdict R fit e (T.tag i d) = true ↔ difference G x y ∈ labels) ∧
      d.outputReversed = c.outputReversed ∧ SameOn keep c.workHead d.workHead c.workCell d.workCell := by
  let word := @encodeCayley n G.toMul
  let T := stages R fit e
  induction labels generalizing c with
  | nil =>
    obtain ⟨k, d, run, stop, noneLeft, output, frame⟩ := hR.readEmpty c hc
    refine ⟨k, 0, d, .finish run, stop, ?_, ?_, output, frame⟩
    · simp [stages, noneLeft]
    · simp
  | cons label labels ih =>
    obtain ⟨k, d, run, stop, available, handoff, frame, resume⟩ := hR.readLabel label labels c hc
    have hs : T.next 0 d.state = some 1 := by simp [T, stages, available]
    have hb : ∀ i ∉ Set.range e, (d.workHead i).natAbs ≤ B := by
      intro i _
      exact (run.2 k le_rfl d run.1).2.2 i
    obtain ⟨l, z, trialRun, trialStop, trialVerdict, output, parked⟩ :=
      trialSegment R fit e G x y label c.outputReversed d.workHead d.workCell hwidth hb
    rw [← handoff] at trialRun
    have frame' : SameOn keep c.workHead z.workHead c.workCell z.workCell :=
      frame.trans (fun i hi => parked i (hkeep hi))
    cases hv : trialAccept z.state.val with
    | true =>
      refine ⟨k + 1 + l, 1, z, .call run stop hs (.finish trialRun), trialStop,
        ?_, ?_, output, frame'⟩
      · simp [stages, hv, show (1 : Fin 2) ≠ 0 by decide]
      · rw [verdict_trial, hv]
        have matchLabel := trialVerdict.mp hv
        simp [matchLabel]
    | false =>
      have more : T.next 1 z.state = some 0 := by
        simp [T, stages, hv, show (1 : Fin 2) ≠ 0 by decide]
      obtain ⟨j, phase, finish, tailRun, tailStop, tailDone, tailVerdict, tailOut, tailFrame⟩ :=
        ih (T.enter 0 z) (resume l z trialRun trialStop output parked)
      refine ⟨k + 1 + (l + 1 + j), phase, finish,
        .call run stop hs (.call trialRun trialStop more tailRun), tailStop, tailDone, ?_,
        tailOut.trans output, frame'.trans tailFrame⟩
      have noMatch : difference G x y ≠ label := fun he => by
        have hyes := trialVerdict.mpr he
        rw [hv] at hyes
        contradiction
      simpa only [List.mem_cons, noMatch, false_or] using tailVerdict

/-- Complete the adjacency trial on a prepared finite stream. The actual
binary machine stops at the first successful comparison or at exhaustion.
Its workspace coefficient is independent of the number of signed labels. -/
theorem executeLabelStream {n : Nat} (G : Group (Fin n)) (x y : Fin n)
    (C : Nat) (hC : 3 ≤ C)
    (keep : Set (Fin W)) (hkeep : keep ⊆ (Set.range e)ᶜ)
    (Ready : List (Fin n) → readerConfig R fit e → Prop)
    (hR : Contract R fit e G x y (C * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1))
      keep Ready)
    (labels : List (Fin n)) (c : readerConfig R fit e) (hc : Ready labels c) :
    let word := @encodeCayley n G.toMul
    ∃ (k : Nat) (d : (machine R fit e).Config),
      (machine R fit e).BoundedSegment word (C * (Nat.log2 (word.length + 1) + 1))
        ((stages R fit e).tag 0 c) d k ∧
      (machine R fit e).step word d = none ∧
      (verdict R fit e d = true ↔ difference G x y ∈ labels) ∧
      d.outputReversed = c.outputReversed ∧ SameOn keep c.workHead d.workHead c.workCell d.workCell := by
  let T := stages R fit e
  obtain ⟨k, i, d, run, stop, exhausted, answer, output, frame⟩ :=
    routedLabelStream R fit e G x y keep hkeep Ready hR (Nat.mul_le_mul_right _ hC) labels c hc
  obtain ⟨compiled, halted⟩ := T.routed_stop run stop exhausted
  exact ⟨k, T.tag i d, compiled, halted, answer, output, frame⟩


/-- Enumerate signed versions of each generator. A diagonal query has an empty
schedule, matching the loopless Cayley graph convention. -/
def signedLabels {n m : Nat} (G : Group (Fin n)) (gen : Fin m → Fin n) (x y : Fin n) :
    List (Fin n) :=
  if x = y then [] else
    (((List.finRange m).flatMap fun i => [(i, false), (i, true)]).map
      (@Connectivity.letterValue (Fin n) G m gen))

theorem signedLabels_spec {n m : Nat} (G : Group (Fin n)) (gen : Fin m → Fin n) (x y : Fin n) :
    difference G x y ∈ signedLabels G gen x y ↔
      (@SimpleGraph.mulCayley (Fin n) (Set.range gen) G.toMul).Adj x y := by
  rw [ReingoldLiveInput.cayley_generation_trials_spec]
  by_cases he : x = y
  · simp [signedLabels, he]
  · unfold signedLabels
    rw [if_neg he, List.mem_map]
    constructor
    · rintro ⟨l, _, h⟩
      exact ⟨he, l, h.symm⟩
    · rintro ⟨_, ⟨i, bit⟩, h⟩
      refine ⟨(i, bit), List.mem_flatMap.2 ⟨i, by simp, ?_⟩, h.symm⟩
      cases bit <;> simp

/-- Implement the complete Cayley predicate starting in the certified physical
signed-label reader's caller state. The fixed routing machine and its space
coefficient are uniform in the group and in the generator count. -/
theorem executeCayleyAdjacency {n m : Nat} (G : Group (Fin n)) (gen : Fin m → Fin n)
    (x y : Fin n) (C : Nat) (hC : 3 ≤ C)
    (keep : Set (Fin W)) (hkeep : keep ⊆ (Set.range e)ᶜ)
    (Ready : List (Fin n) → readerConfig R fit e → Prop)
    (hR : Contract R fit e G x y (C * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1))
      keep Ready)
    (c : readerConfig R fit e) (hc : Ready (signedLabels G gen x y) c) :
    let word := @encodeCayley n G.toMul
    ∃ (k : Nat) (d : (machine R fit e).Config),
      (machine R fit e).BoundedSegment word (C * (Nat.log2 (word.length + 1) + 1))
        ((stages R fit e).tag 0 c) d k ∧
      (machine R fit e).step word d = none ∧
      (verdict R fit e d = true ↔
        (@SimpleGraph.mulCayley (Fin n) (Set.range gen) G.toMul).Adj x y) ∧
      d.outputReversed = c.outputReversed ∧ SameOn keep c.workHead d.workHead c.workCell d.workCell := by
  obtain ⟨k, d, run, stop, hv, output, frame⟩ :=
    executeLabelStream R fit e G x y C hC keep hkeep Ready hR (signedLabels G gen x y) c hc
  exact ⟨k, d, run, stop, hv.trans (signedLabels_spec G gen x y), output, frame⟩
end Mathproof.MinimumGeneration.ReingoldGeneratorStream
