import Mathproof.MinimumGenerationTapeCompose

/-!
# Finite routing between verified Cayley-table macros
-/

namespace Mathproof.MinimumGeneration.SearchTransducer

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)

abbrev MacroTransition (S W : ℕ) :=
  Fin S → InputCell → (Fin W → Option Bool) →
    Option (Fin S × Move × (Fin W → Action (Option Bool)) × Option Bool)

/-- A fixed collection of stages on the same work banks. Choosing the next
stage reads only the current stage and its terminal control state. -/
structure Stages (K S W : ℕ) where
  first : Fin K
  entry : Fin K → Fin S
  transition : Fin K → MacroTransition S W
  next : Fin K → Fin S → Option (Fin K)

namespace Stages

variable {K S W : ℕ} (T : Stages K S W)

abbrev component (i : Fin K) : SearchTransducer where
  states := S
  workTapes := W
  initialState := T.entry i
  transition := T.transition i

private def routeTransition : MacroTransition (K * S) W :=
  fun q input scanned =>
    let (i, state) := finProdFinEquiv.symm q
    match T.transition i state input scanned with
    | some (next, move, acts, bit) => some (finProdFinEquiv (i, next), move, acts, bit)
    | none => (T.next i state).map fun j =>
      (finProdFinEquiv (j, T.entry j), .stay, fun _ => ⟨none, .stay⟩, none)

/-- The executable finite control for the whole routing graph. -/
abbrev machine : SearchTransducer where
  states := K * S
  workTapes := W
  initialState := finProdFinEquiv (T.first, T.entry T.first)
  transition := T.routeTransition

def tag (i : Fin K) (c : (T.component i).Config) : T.machine.Config :=
  ⟨finProdFinEquiv (i, c.state), c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

def enter {i : Fin K} (j : Fin K) (c : (T.component i).Config) : (T.component j).Config :=
  ⟨T.entry j, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

theorem step_run (i : Fin K) {word : List Bool} {c d : (T.component i).Config}
    (h : (T.component i).step word c = some d) :
    T.machine.step word (T.tag i c) = some (T.tag i d) := by
  unfold SearchTransducer.step at h ⊢
  cases ht : T.transition i c.state (readInput word c.inputHead)
      (fun b => c.workCell b (c.workHead b)) with
  | none => simp [ht] at h
  | some p =>
    rcases p with ⟨q, m, a, o⟩
    simp only [ht, Option.map_some, Option.some.injEq] at h
    subst d
    simp only [tag, machine, routeTransition, Equiv.symm_apply_apply, ht, Option.map_some]
    rfl

theorem step_halt (i : Fin K) {word : List Bool} {c : (T.component i).Config}
    (h : (T.component i).step word c = none) :
    T.machine.step word (T.tag i c) = (T.next i c.state).map (fun j => T.tag j (T.enter j c)) := by
  unfold SearchTransducer.step at h ⊢
  have htransition : T.transition i c.state (readInput word c.inputHead)
      (fun b => c.workCell b (c.workHead b)) = none := Option.map_eq_none_iff.mp h
  simp only [tag, machine, routeTransition, Equiv.symm_apply_apply, htransition]
  cases hn : T.next i c.state with
  | none => rfl
  | some j =>
    simp only [Option.map_some, Option.some.injEq, enter, moveOffset, Int.add_zero,
      Option.getD_none, Option.elim]
    congr 1
    funext b x
    exact ite_self _

theorem run_component (i : Fin K) {word : List Bool} {c d : (T.component i).Config} {k : ℕ}
    (h : runFrom (T.component i) word c k = some d) :
    runFrom T.machine word (T.tag i c) k = some (T.tag i d) := by
  induction k generalizing d with
  | zero => simp only [runFrom, Option.some.injEq] at h; subst d; rfl
  | succ k ih =>
    obtain ⟨b, hb, hstep⟩ := Option.bind_eq_some_iff.mp h
    rw [runFrom, ih hb, Option.bind_some]
    exact T.step_run i hstep

theorem segment_component (i : Fin K) {word : List Bool} {B k : ℕ}
    {c d : (T.component i).Config} (h : (T.component i).BoundedSegment word B c d k) :
    T.machine.BoundedSegment word B (T.tag i c) (T.tag i d) k := by
  refine ⟨T.run_component i h.1, ?_⟩
  intro t ht x hx
  have he : k = t + (k - t) := by omega
  have hs := h.1
  rw [he, runFrom_add] at hs
  obtain ⟨p, hp, _⟩ := Option.bind_eq_some_iff.mp hs
  rw [T.run_component i hp] at hx
  have hp' : T.tag i p = x := Option.some.inj hx
  subst x
  exact h.2 t ht p hp

theorem segment_handoff {i j : Fin K} {word : List Bool} {B : ℕ}
    {c : (T.component i).Config} (h : (T.component i).step word c = none)
    (hnext : T.next i c.state = some j) (hb : (T.component i).Bounded word B c) :
    T.machine.BoundedSegment word B (T.tag i c) (T.tag j (T.enter j c)) 1 := by
  have hs := T.step_halt i h
  rw [hnext, Option.map_some] at hs
  refine ⟨hs, ?_⟩
  intro t ht x hx
  have he : t = 0 ∨ t = 1 := by omega
  rcases he with rfl | rfl
  · have he : T.tag i c = x := Option.some.inj hx
    subst x
    exact hb
  · have he : T.tag j (T.enter j c) = x := Option.some.inj (hs.symm.trans hx)
    subst x
    exact hb

/-- Any number of actual macro invocations and routing transitions can be
certified under one common bound. -/
inductive Routed (T : Stages K S W) (word : List Bool) (B : ℕ) :
    (i : Fin K) → (T.component i).Config → (j : Fin K) → (T.component j).Config → ℕ → Prop
  | finish {i c d k} (h : (T.component i).BoundedSegment word B c d k) :
      Routed T word B i c i d k
  | call {i j f c d z k n}
      (h : (T.component i).BoundedSegment word B c d k)
      (hs : (T.component i).step word d = none) (hn : T.next i d.state = some j)
      (rest : Routed T word B j (T.enter j d) f z n) :
      Routed T word B i c f z (k + 1 + n)

theorem routed_segment {word : List Bool} {B k : ℕ} {i j : Fin K}
    {c : (T.component i).Config} {d : (T.component j).Config}
    (h : T.Routed word B i c j d k) :
    T.machine.BoundedSegment word B (T.tag i c) (T.tag j d) k := by
  induction h with
  | finish h => exact T.segment_component _ h
  | call h hs hn rest ih =>
    have first := T.segment_component _ h
    have jump := T.segment_handoff hs hn (h.2 _ (Nat.le_refl _) _ h.1)
    exact BoundedSegment.append _ (BoundedSegment.append _ first jump) ih

theorem routed_stop {word : List Bool} {B k : ℕ} {i j : Fin K}
    {c : (T.component i).Config} {d : (T.component j).Config}
    (h : T.Routed word B i c j d k)
    (hstop : (T.component j).step word d = none) (hnext : T.next j d.state = none) :
    T.machine.BoundedSegment word B (T.tag i c) (T.tag j d) k ∧
      T.machine.step word (T.tag j d) = none := by
  refine ⟨T.routed_segment h, ?_⟩
  rw [T.step_halt j hstop, hnext]
  rfl


/-- An audited route from the shared blank start yields the original
search-transducer workspace predicate and the exact output word. -/
theorem routed_logspace_output {word : List Bool} {C k : ℕ} {j : Fin K}
    {d : (T.component j).Config}
    (h : T.Routed word (C * (Nat.log2 (word.length + 1) + 1))
      T.first (T.component T.first).initial j d k)
    (hstop : (T.component j).step word d = none) (hnext : T.next j d.state = none) :
    T.machine.logarithmicWorkspace C word ∧ T.machine.outputs word d.outputReversed.reverse := by
  obtain ⟨hr, hs⟩ := T.routed_stop h hstop hnext
  exact BoundedSegment.logspaceOutput T.machine hr hs
end Stages

/-- Inject one component's own finite-state table into a larger shared
finite-state budget, with arbitrary relocation of its work banks. -/
def padTransition (P : SearchTransducer) {S W : ℕ} (hS : P.states ≤ S)
    (e : Fin P.workTapes ↪ Fin W) : MacroTransition S W :=
  fun q input scanned =>
    if hq : q.val < P.states then
      ((P.relocateBanks e).transition ⟨q.val, hq⟩ input scanned).map fun (r, m, a, b) =>
        (r.castLE hS, m, a, b)
    else none

theorem padTransition_at (P : SearchTransducer) {S W : ℕ} (hS : P.states ≤ S)
    (e : Fin P.workTapes ↪ Fin W) (q : Fin P.states) (input : InputCell)
    (scanned : Fin W → Option Bool) :
    P.padTransition hS e (q.castLE hS) input scanned =
      ((P.relocateBanks e).transition q input scanned).map (fun (r, m, a, b) =>
        (r.castLE hS, m, a, b)) := by
  simp only [padTransition, Fin.val_castLE, dif_pos q.isLt, Fin.eta]


/-- The padded machine is literally the original relocated macro at states
below its native state bound. -/
abbrev padMachine (P : SearchTransducer) {S W : ℕ} (hS : P.states ≤ S)
    (e : Fin P.workTapes ↪ Fin W) : SearchTransducer where
  states := S
  workTapes := W
  initialState := P.initialState.castLE hS
  transition := P.padTransition hS e

def padConfig (P : SearchTransducer) {S W : ℕ} (hS : P.states ≤ S)
    (e : Fin P.workTapes ↪ Fin W) (c : (P.relocateBanks e).Config) :
    (P.padMachine hS e).Config :=
  ⟨c.state.castLE hS, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

theorem padMachine_step (P : SearchTransducer) {S W : ℕ} (hS : P.states ≤ S)
    (e : Fin P.workTapes ↪ Fin W) (word : List Bool) (c : (P.relocateBanks e).Config) :
    (P.padMachine hS e).step word (P.padConfig hS e c) =
      ((P.relocateBanks e).step word c).map (P.padConfig hS e) := by
  unfold SearchTransducer.step
  simp only [padMachine, padConfig, padTransition_at]
  simp only [Option.map_map]
  apply Option.map_congr
  intro p _
  rcases p with ⟨q, m, a, b⟩
  rfl

theorem padMachine_runFrom (P : SearchTransducer) {S W : ℕ} (hS : P.states ≤ S)
    (e : Fin P.workTapes ↪ Fin W) (word : List Bool) (c : (P.relocateBanks e).Config) (k : ℕ) :
    runFrom (P.padMachine hS e) word (P.padConfig hS e c) k =
      (runFrom (P.relocateBanks e) word c k).map (P.padConfig hS e) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runFrom, ih]
    cases runFrom (P.relocateBanks e) word c k with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some]
      exact P.padMachine_step hS e word d

theorem padMachine_segment (P : SearchTransducer) {S W : ℕ} (hS : P.states ≤ S)
    (e : Fin P.workTapes ↪ Fin W) {word : List Bool} {B k : ℕ}
    {c d : (P.relocateBanks e).Config}
    (h : (P.relocateBanks e).BoundedSegment word B c d k) :
    (P.padMachine hS e).BoundedSegment word B (P.padConfig hS e c) (P.padConfig hS e d) k := by
  refine ⟨by rw [P.padMachine_runFrom, h.1, Option.map_some], ?_⟩
  intro t ht x hx
  rw [P.padMachine_runFrom] at hx
  obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp hx
  subst x
  exact h.2 t ht b hb

namespace Stages

/-- Assemble heterogeneous macros from their own bounded controls and their
chosen physical bank layouts. Route functions receive native terminal states. -/
def ofMachines {K S W : ℕ} (first : Fin K) (P : Fin K → SearchTransducer)
    (hS : ∀ i, (P i).states ≤ S) (e : ∀ i, Fin (P i).workTapes ↪ Fin W)
    (next : (i : Fin K) → Fin (P i).states → Option (Fin K)) : Stages K S W where
  first := first
  entry i := (P i).initialState.castLE (hS i)
  transition i := (P i).padTransition (hS i) (e i)
  next i q := if h : q.val < (P i).states then next i ⟨q.val, h⟩ else none

theorem ofMachines_next_at {K S W : ℕ} (first : Fin K) (P : Fin K → SearchTransducer)
    (hS : ∀ i, (P i).states ≤ S) (e : ∀ i, Fin (P i).workTapes ↪ Fin W)
    (next : (i : Fin K) → Fin (P i).states → Option (Fin K))
    (i : Fin K) (q : Fin (P i).states) :
    (ofMachines first P hS e next).next i (q.castLE (hS i)) = next i q := by
  simp only [ofMachines, Fin.val_castLE, dif_pos q.isLt, Fin.eta]


theorem ofMachines_native_segment {K S W : ℕ} (first : Fin K) (P : Fin K → SearchTransducer)
    (hS : ∀ i, (P i).states ≤ S) (e : ∀ i, Fin (P i).workTapes ↪ Fin W)
    (next : (i : Fin K) → Fin (P i).states → Option (Fin K))
    (i : Fin K) {word : List Bool} {B k : ℕ} {c d : (P i).Config}
    (heads : Fin W → Int) (cells : Fin W → Int → Option Bool)
    (h : (P i).BoundedSegment word B c d k)
    (hframe : ∀ j ∉ Set.range (e i), (heads j).natAbs ≤ B) :
    let T := ofMachines first P hS e next
    let start := (P i).padConfig (hS i) (e i) ((P i).bankConfig (e i) c heads cells)
    let stop := (P i).padConfig (hS i) (e i) ((P i).bankConfig (e i) d heads cells)
    T.machine.BoundedSegment word B (T.tag i start) (T.tag i stop) k := by
  let T := ofMachines first P hS e next
  apply T.segment_component i
  exact (P i).padMachine_segment (hS i) (e i) ((P i).relocateBanks_segment (e i) h hframe)
end Stages
end Mathproof.MinimumGeneration.SearchTransducer
