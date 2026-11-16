import Mathproof.MinimumGenerationProblem
import Batteries.Data.Fin.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Work-tape layout and framed calls for the Cayley-table transducer
-/

namespace Mathproof.MinimumGeneration.SearchTransducer

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)

/-- Run a machine from an explicit configuration for exactly this many steps. -/
def runFrom (M : SearchTransducer) (word : List Bool) (c : M.Config) :
    ℕ → Option M.Config
  | 0 => some c
  | k + 1 => (runFrom M word c k).bind (M.step word)

theorem runFrom_initial (M : SearchTransducer) (word : List Bool) (k : ℕ) :
    runFrom M word M.initial k = M.after word k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [runFrom, SearchTransducer.after, ih]

theorem runFrom_add (M : SearchTransducer) (word : List Bool) (c : M.Config) (a b : ℕ) :
    runFrom M word c (a + b) =
      (runFrom M word c a).bind (fun d => runFrom M word d b) := by
  induction b with
  | zero => cases runFrom M word c a <;> rfl
  | succ b ih =>
    change (runFrom M word c (a + b)).bind (M.step word) =
      (runFrom M word c a).bind (fun d => (runFrom M word d b).bind (M.step word))
    rw [ih, Option.bind_assoc]

/-- Decode a physical bank number using the fixed finite bank layout. -/
private def bankIndex {s t : ℕ} (e : Fin s ↪ Fin t) (j : Fin t) : Option (Fin s) :=
  Fin.find? (fun i => decide (e i = j))

private theorem bankIndex_some {s t : ℕ} {e : Fin s ↪ Fin t}
    {j : Fin t} {i : Fin s} (h : bankIndex e j = some i) : e i = j := by
  exact of_decide_eq_true (Fin.eq_true_of_find?_eq_some h)

@[simp] private theorem bankIndex_image {s t : ℕ} (e : Fin s ↪ Fin t) (i : Fin s) :
    bankIndex e (e i) = some i := by
  apply Fin.find?_eq_some_iff.mpr
  refine ⟨by simp, ?_⟩
  intro j hj
  have hne : e j ≠ e i := fun h => (ne_of_lt hj) (e.injective h)
  simp [hne]

private theorem bankIndex_none {s t : ℕ} {e : Fin s ↪ Fin t} {j : Fin t}
    (h : j ∉ Set.range e) : bankIndex e j = none := by
  apply Fin.find?_eq_none_iff.mpr
  intro i
  have hne : e i ≠ j := fun he => h ⟨i, he⟩
  simp [hne]

private def transitionOnBanks (M : SearchTransducer) {W : ℕ} (e : Fin M.workTapes ↪ Fin W)
    (q : Fin M.states) (b : InputCell) (scanned : Fin W → Option Bool) :
    Option (Fin M.states × Move × (Fin W → Action (Option Bool)) × Option Bool) :=
  (M.transition q b (fun i => scanned (e i))).map fun (q', inputMove, actions, output) =>
    (q', inputMove, fun j => ((bankIndex e j).map actions).getD ⟨none, .stay⟩, output)

/-- Run a macro on designated physical work tapes. The transition table has
the same states and uses the same read-only input and write-only output. -/
@[reducible] def relocateBanks (M : SearchTransducer) {W : ℕ} (e : Fin M.workTapes ↪ Fin W) :
    SearchTransducer where
  states := M.states
  workTapes := W
  initialState := M.initialState
  transition := transitionOnBanks M e

/-- Extend a macro configuration by an arbitrary frame of unused banks. -/
def bankConfig (M : SearchTransducer) {W : ℕ} (e : Fin M.workTapes ↪ Fin W)
    (c : M.Config) (heads : Fin W → Int) (cells : Fin W → Int → Option Bool) :
    (M.relocateBanks e).Config where
  state := c.state
  inputHead := c.inputHead
  workHead := fun j => ((bankIndex e j).map c.workHead).getD (heads j)
  workCell := fun j => ((bankIndex e j).map c.workCell).getD (cells j)
  outputReversed := c.outputReversed

@[simp] theorem bankConfig_head_image (M : SearchTransducer) {W : ℕ}
    (e : Fin M.workTapes ↪ Fin W) (c : M.Config) (heads : Fin W → Int)
    (cells : Fin W → Int → Option Bool) (i : Fin M.workTapes) :
    (M.bankConfig e c heads cells).workHead (e i) = c.workHead i := by
  simp [bankConfig]

@[simp] theorem bankConfig_cell_image (M : SearchTransducer) {W : ℕ}
    (e : Fin M.workTapes ↪ Fin W) (c : M.Config) (heads : Fin W → Int)
    (cells : Fin W → Int → Option Bool) (i : Fin M.workTapes) :
    (M.bankConfig e c heads cells).workCell (e i) = c.workCell i := by
  simp [bankConfig]

theorem bankConfig_frame (M : SearchTransducer) {W : ℕ}
    (e : Fin M.workTapes ↪ Fin W) (c : M.Config) (heads : Fin W → Int)
    (cells : Fin W → Int → Option Bool) {j : Fin W} (h : j ∉ Set.range e) :
    (M.bankConfig e c heads cells).workHead j = heads j ∧
      (M.bankConfig e c heads cells).workCell j = cells j := by
  simp [bankConfig, bankIndex_none h]

theorem relocateBanks_step (M : SearchTransducer) {W : ℕ}
    (e : Fin M.workTapes ↪ Fin W) (word : List Bool) (c : M.Config)
    (heads : Fin W → Int) (cells : Fin W → Int → Option Bool) :
    (M.relocateBanks e).step word (M.bankConfig e c heads cells) =
      (M.step word c).map (fun d => M.bankConfig e d heads cells) := by
  unfold SearchTransducer.step
  simp only [relocateBanks, transitionOnBanks, bankConfig, bankIndex_image, Option.map_some, Option.getD_some]
  cases ht : M.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => simp
  | some p =>
    rcases p with ⟨state, inputMove, actions, output⟩
    simp only [Option.map_some, Option.some.injEq]
    congr 1
    · funext j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        simp
      · simp [bankIndex_none hj, moveOffset]
    · funext j x
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        simp
      · simp [bankIndex_none hj]

/-- Every prefix in the relocated macro is the same prefix on its chosen banks,
and its entire unused bank frame is identical to the initial frame. -/
theorem relocateBanks_runFrom (M : SearchTransducer) {W : ℕ}
    (e : Fin M.workTapes ↪ Fin W) (word : List Bool) (c : M.Config)
    (heads : Fin W → Int) (cells : Fin W → Int → Option Bool) (k : ℕ) :
    runFrom (M.relocateBanks e) word (M.bankConfig e c heads cells) k =
      (runFrom M word c k).map (fun d => M.bankConfig e d heads cells) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runFrom, ih]
    cases h : runFrom M word c k with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some]
      exact relocateBanks_step M e word d heads cells

/-- Absolute input and work-head bounds for a prefix configuration. -/
def Bounded (M : SearchTransducer) (word : List Bool) (B : ℕ) (c : M.Config) : Prop :=
  (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (word.length : Int) ∧
    ∀ i, (c.workHead i).natAbs ≤ B

theorem bankConfig_bounded (M : SearchTransducer) {W : ℕ}
    (e : Fin M.workTapes ↪ Fin W) {word : List Bool} {B : ℕ} {c : M.Config}
    {heads : Fin W → Int} {cells : Fin W → Int → Option Bool}
    (hc : M.Bounded word B c) (hframe : ∀ j ∉ Set.range e, (heads j).natAbs ≤ B) :
    (M.relocateBanks e).Bounded word B (M.bankConfig e c heads cells) := by
  refine ⟨hc.1, hc.2.1, ?_⟩
  intro j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simpa only [bankConfig_head_image] using hc.2.2 i
  · rw [(bankConfig_frame M e c heads cells hj).1]
    exact hframe j hj

/-- A segment has a common head bound at every configuration, including its
entry and exit. This is independent of how many steps are executed. -/
def BoundedSegment (M : SearchTransducer) (word : List Bool) (B : ℕ)
    (c d : M.Config) (length : ℕ) : Prop :=
  runFrom M word c length = some d ∧
    ∀ k ≤ length, ∀ x, runFrom M word c k = some x → M.Bounded word B x

theorem relocateBanks_segment (M : SearchTransducer) {W : ℕ}
    (e : Fin M.workTapes ↪ Fin W) {word : List Bool} {B length : ℕ}
    {c d : M.Config} {heads : Fin W → Int} {cells : Fin W → Int → Option Bool}
    (h : M.BoundedSegment word B c d length)
    (hframe : ∀ j ∉ Set.range e, (heads j).natAbs ≤ B) :
    (M.relocateBanks e).BoundedSegment word B (M.bankConfig e c heads cells)
      (M.bankConfig e d heads cells) length := by
  refine ⟨by simp only [relocateBanks_runFrom, h.1, Option.map_some], ?_⟩
  intro k hk x hx
  rw [relocateBanks_runFrom] at hx
  cases hd : runFrom M word c k with
  | none => simp [hd] at hx
  | some b =>
    simp only [hd, Option.map_some, Option.some.injEq] at hx
    subst x
    exact bankConfig_bounded M e (h.2 k hk b hd) hframe

/-- Concatenation does not increase the common bound. Iterating this lemma
accounts for arbitrary call counts without an input-dependent space overhead. -/
theorem BoundedSegment.append (M : SearchTransducer) {word : List Bool} {B a b : ℕ}
    {c d f : M.Config} (h₁ : M.BoundedSegment word B c d a)
    (h₂ : M.BoundedSegment word B d f b) : M.BoundedSegment word B c f (a + b) := by
  refine ⟨by simp only [runFrom_add, h₁.1, Option.bind_some, h₂.1], ?_⟩
  intro k hk x hx
  by_cases ha : k ≤ a
  · exact h₁.2 k ha x hx
  · have hle : k - a ≤ b := by omega
    have heq : a + (k - a) = k := by omega
    rw [← heq, runFrom_add, h₁.1, Option.bind_some] at hx
    exact h₂.2 (k - a) hle x hx



/-- A completed bounded run supplies both the problem's logarithmic workspace
predicate and the exact write-only output. -/
theorem BoundedSegment.logspaceOutput (M : SearchTransducer) {word : List Bool} {C length : ℕ}
    {c : M.Config}
    (run : M.BoundedSegment word (C * (Nat.log2 (word.length + 1) + 1)) M.initial c length)
    (stop : M.step word c = none) :
    M.logarithmicWorkspace C word ∧ M.outputs word c.outputReversed.reverse := by
  refine ⟨?_, ⟨length, c, (runFrom_initial M word length).symm.trans run.1, stop, rfl⟩⟩
  intro k x hx
  rw [← runFrom_initial] at hx
  by_cases hk : k ≤ length
  · exact run.2 k hk x hx
  · have he : k = length + 1 + (k - (length + 1)) := by omega
    rw [he, runFrom_add, runFrom, run.1, Option.bind_some, stop] at hx
    simp at hx
section Handoff

variable (A B : SearchTransducer) {W : ℕ}
    (eA : Fin A.workTapes ↪ Fin W) (eB : Fin B.workTapes ↪ Fin W)


/-- Execute two macros in one physical work layout. The first halt is replaced
by a stay-and-preserve transition into the second macro's initial state. -/
@[reducible] def thenMachine : SearchTransducer where
  states := A.states + B.states
  workTapes := W
  initialState := Fin.castAdd B.states A.initialState
  transition q input scanned := Sum.elim
    (fun state =>
      match (A.relocateBanks eA).transition state input scanned with
      | none => some (Fin.natAdd A.states B.initialState, .stay, (fun _ => ⟨none, .stay⟩), none)
      | some (next, move, acts, bit) => some (Fin.castAdd B.states next, move, acts, bit))
    (fun state => ((B.relocateBanks eB).transition state input scanned).map fun (next, move, acts, bit) =>
      (Fin.natAdd A.states next, move, acts, bit))
    (finSumFinEquiv.symm q)

/-- Embed the first macro's literal configuration in the two-stage machine. -/
def thenLeft (c : (A.relocateBanks eA).Config) : (thenMachine A B eA eB).Config :=
  ⟨Fin.castAdd B.states c.state, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

/-- Embed the second macro's literal configuration in the two-stage machine. -/
def thenRight (c : (B.relocateBanks eB).Config) : (thenMachine A B eA eB).Config :=
  ⟨Fin.natAdd A.states c.state, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

/-- The first macro's final tapes and heads become the second macro's entry
tapes and heads without copying or scanning. -/
def thenEntry (c : (A.relocateBanks eA).Config) : (B.relocateBanks eB).Config :=
  ⟨B.initialState, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

theorem thenStep_left {word : List Bool} {c d : (A.relocateBanks eA).Config}
    (h : (A.relocateBanks eA).step word c = some d) :
    (thenMachine A B eA eB).step word (thenLeft A B eA eB c) =
      some (thenLeft A B eA eB d) := by
  unfold SearchTransducer.step at h ⊢
  cases ht : transitionOnBanks A eA c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => simp [ht] at h
  | some p =>
    rcases p with ⟨state, inputMove, actions, output⟩
    simp only [ht, Option.map_some, Option.some.injEq] at h
    subst d
    simp only [thenMachine, thenLeft]
    rw [finSumFinEquiv_symm_apply_castAdd (m := A.states) (n := B.states) c.state, Sum.elim_inl, ht]
    rfl

theorem thenStep_right (word : List Bool) (c : (B.relocateBanks eB).Config) :
    (thenMachine A B eA eB).step word (thenRight A B eA eB c) =
      ((B.relocateBanks eB).step word c).map (thenRight A B eA eB) := by
  unfold SearchTransducer.step
  simp only [thenMachine, thenRight]
  rw [finSumFinEquiv_symm_apply_natAdd (m := A.states) (n := B.states) c.state, Sum.elim_inr]
  cases ht : transitionOnBanks B eB c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => rfl
  | some p => rcases p with ⟨state, inputMove, actions, output⟩; rfl

theorem thenStep_handoff {word : List Bool} {c : (A.relocateBanks eA).Config}
    (h : (A.relocateBanks eA).step word c = none) :
    (thenMachine A B eA eB).step word (thenLeft A B eA eB c) =
      some (thenRight A B eA eB (thenEntry A B eA eB c)) := by
  unfold SearchTransducer.step at h ⊢
  simp only [thenMachine, thenLeft]
  rw [finSumFinEquiv_symm_apply_castAdd (m := A.states) (n := B.states) c.state, Sum.elim_inl]
  cases ht : transitionOnBanks A eA c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none =>
    simp only [Option.map_some, Option.some.injEq, thenRight, thenEntry,
      moveOffset, Int.add_zero, Option.getD_none, Option.elim]
    congr 1
    funext i x
    exact ite_self _
  | some p => simp [ht] at h

theorem thenRun_left {word : List Bool} {c d : (A.relocateBanks eA).Config} {k : ℕ}
    (h : runFrom (A.relocateBanks eA) word c k = some d) :
    runFrom (thenMachine A B eA eB) word (thenLeft A B eA eB c) k =
      some (thenLeft A B eA eB d) := by
  induction k generalizing d with
  | zero => simp only [runFrom, Option.some.injEq] at h; subst d; rfl
  | succ k ih =>
    rcases Option.bind_eq_some_iff.mp h with ⟨b, hb, hstep⟩
    rw [runFrom, ih hb, Option.bind_some]
    exact thenStep_left A B eA eB hstep

theorem thenRun_right (word : List Bool) (c : (B.relocateBanks eB).Config) (k : ℕ) :
    runFrom (thenMachine A B eA eB) word (thenRight A B eA eB c) k =
      (runFrom (B.relocateBanks eB) word c k).map (thenRight A B eA eB) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runFrom, ih]
    cases runFrom (B.relocateBanks eB) word c k with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some]
      exact thenStep_right A B eA eB word d

theorem thenRun_handoff {word : List Bool} {a b : ℕ} {ca da : (A.relocateBanks eA).Config} {db : (B.relocateBanks eB).Config}
    (ha : runFrom (A.relocateBanks eA) word ca a = some da)
    (hh : (A.relocateBanks eA).step word da = none)
    (hb : runFrom (B.relocateBanks eB) word (thenEntry A B eA eB da) b = some db) :
    runFrom (thenMachine A B eA eB) word (thenLeft A B eA eB ca) (a + 1 + b) =
      some (thenRight A B eA eB db) := by
  rw [runFrom_add, runFrom, thenRun_left A B eA eB ha, Option.bind_some,
    thenStep_handoff A B eA eB hh, Option.bind_some, thenRun_right, hb]
  rfl

private theorem runFrom_prefix_exists {M : SearchTransducer} {word : List Bool}
    {c d : M.Config} {length k : ℕ} (h : runFrom M word c length = some d) (hk : k ≤ length) :
    ∃ x, runFrom M word c k = some x := by
  have heq : length = k + (length - k) := by omega
  rw [heq, runFrom_add] at h
  obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨x, hx⟩

/-- The common physical workspace bound transports through a completed
handoff with no additive space charge. -/
theorem thenSegment {word : List Bool} {Bnd a b : ℕ} {ca da : (A.relocateBanks eA).Config} {db : (B.relocateBanks eB).Config}
    (ha : (A.relocateBanks eA).BoundedSegment word Bnd ca da a)
    (hh : (A.relocateBanks eA).step word da = none)
    (hb : (B.relocateBanks eB).BoundedSegment word Bnd (thenEntry A B eA eB da) db b) :
    (thenMachine A B eA eB).BoundedSegment word Bnd (thenLeft A B eA eB ca)
      (thenRight A B eA eB db) (a + 1 + b) := by
  refine ⟨thenRun_handoff A B eA eB ha.1 hh hb.1, ?_⟩
  intro k hk x hx
  by_cases hka : k ≤ a
  · obtain ⟨d, hd⟩ := runFrom_prefix_exists ha.1 hka
    have he : thenLeft A B eA eB d = x := by
      rw [thenRun_left A B eA eB hd] at hx
      exact Option.some.inj hx
    subst x
    exact ha.2 k hka d hd
  · have heq : k = a + 1 + (k - (a + 1)) := by omega
    have hkb : k - (a + 1) ≤ b := by omega
    obtain ⟨d, hd⟩ := runFrom_prefix_exists hb.1 hkb
    rw [heq, thenRun_handoff A B eA eB ha.1 hh hd] at hx
    have he : thenRight A B eA eB d = x := Option.some.inj hx
    subst x
    exact hb.2 _ hkb d hd

end Handoff

section Repeat

variable (P : SearchTransducer)

/-- The restart test can inspect only the finite control and scanned symbols. -/
abbrev RepeatTest := Fin P.states → InputCell → (Fin P.workTapes → Option Bool) → Bool

def shouldRepeat (again : P.RepeatTest) (word : List Bool) (c : P.Config) : Bool :=
  again c.state (readInput word c.inputHead) (fun i => c.workCell i (c.workHead i))

/-- On a selected halt, restart a macro in the same physical configuration. -/
@[reducible] def repeatMachine (again : P.RepeatTest) : SearchTransducer where
  states := P.states
  workTapes := P.workTapes
  initialState := P.initialState
  transition q input scanned :=
    match P.transition q input scanned with
    | some p => some p
    | none =>
      if again q input scanned then some (P.initialState, .stay, fun _ => ⟨none, .stay⟩, none)
      else none

def repeatConfig (again : P.RepeatTest) (c : P.Config) : (P.repeatMachine again).Config :=
  ⟨c.state, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

/-- Restart changes only the finite control. -/
def restartConfig (c : P.Config) : P.Config :=
  {c with state := P.initialState}

theorem repeatStep_run (again : P.RepeatTest) {word : List Bool} {c d : P.Config}
    (h : P.step word c = some d) :
    (P.repeatMachine again).step word (P.repeatConfig again c) = some (P.repeatConfig again d) := by
  unfold SearchTransducer.step at h ⊢
  cases ht : P.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => simp [ht] at h
  | some p =>
    rcases p with ⟨next, move, actions, out⟩
    simp only [ht, Option.map_some, Option.some.injEq] at h
    subst d
    simp only [repeatMachine, repeatConfig, ht, Option.map_some]
    rfl

theorem repeatStep_halt (again : P.RepeatTest) {word : List Bool} {c : P.Config}
    (h : P.step word c = none) :
    (P.repeatMachine again).step word (P.repeatConfig again c) =
      if P.shouldRepeat again word c then some (P.repeatConfig again (P.restartConfig c))
      else none := by
  unfold SearchTransducer.step at h ⊢
  cases ht : P.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | some p => simp [ht] at h
  | none =>
    simp only [repeatMachine, repeatConfig, shouldRepeat, ht]
    by_cases ha : again c.state (readInput word c.inputHead)
        (fun i => c.workCell i (c.workHead i)) = true
    · simp [ha, restartConfig, moveOffset]
      funext i x
      exact ite_self _
    · simp [ha]

theorem repeatRun (again : P.RepeatTest) {word : List Bool} {c d : P.Config} {k : ℕ}
    (h : runFrom P word c k = some d) :
    runFrom (P.repeatMachine again) word (P.repeatConfig again c) k =
      some (P.repeatConfig again d) := by
  induction k generalizing d with
  | zero => simp only [runFrom, Option.some.injEq] at h; subst d; rfl
  | succ k ih =>
    obtain ⟨b, hb, hstep⟩ := Option.bind_eq_some_iff.mp h
    rw [runFrom, ih hb, Option.bind_some]
    exact repeatStep_run P again hstep

theorem repeatSegment (again : P.RepeatTest) {word : List Bool} {B k : ℕ} {c d : P.Config}
    (h : P.BoundedSegment word B c d k) :
    (P.repeatMachine again).BoundedSegment word B (P.repeatConfig again c)
      (P.repeatConfig again d) k := by
  refine ⟨repeatRun P again h.1, ?_⟩
  intro t ht x hx
  obtain ⟨p, hp⟩ := runFrom_prefix_exists h.1 ht
  rw [repeatRun P again hp] at hx
  have he : P.repeatConfig again p = x := Option.some.inj hx
  subst x
  exact h.2 t ht p hp

/-- One certified iteration consumes one bounded macro execution and one
neutral restart. The number of iterations is unconstrained. -/
inductive RepeatSegments (again : P.RepeatTest) (word : List Bool) (B : ℕ) :
    P.Config → P.Config → ℕ → Prop
  | done {c} (h : P.Bounded word B c) : RepeatSegments again word B c c 0
  | more {c d f : P.Config} {steps rest : ℕ}
      (hseg : P.BoundedSegment word B c d steps) (hhalt : P.step word d = none)
      (hagain : P.shouldRepeat again word d = true)
      (hrest : RepeatSegments again word B (P.restartConfig d) f rest) :
      RepeatSegments again word B c f (steps + 1 + rest)

/-- Any sequence of certified iterations is an actual bounded run of a
single finite-control machine, with the same bound throughout. -/
theorem repeatSegments_run (again : P.RepeatTest) {word : List Bool} {B k : ℕ} {c d : P.Config}
    (h : P.RepeatSegments again word B c d k) :
    (P.repeatMachine again).BoundedSegment word B (P.repeatConfig again c)
      (P.repeatConfig again d) k := by
  induction h with
  | done h =>
    refine ⟨rfl, ?_⟩
    intro t ht x hx
    have he : t = 0 := Nat.eq_zero_of_le_zero ht
    subst t
    have hcx := Option.some.inj hx
    subst x
    exact h
  | @more c d f steps rest hseg hhalt hagain hrest ih =>
    have hbound := hseg.2 steps (Nat.le_refl _) d hseg.1
    have hs : (P.repeatMachine again).BoundedSegment word B (P.repeatConfig again d)
        (P.repeatConfig again (P.restartConfig d)) 1 := by
      refine ⟨?_, ?_⟩
      · change (P.repeatMachine again).step word (P.repeatConfig again d) = _
        rw [repeatStep_halt P again hhalt, hagain]
        rfl
      · intro t ht x hx
        have he : t = 0 ∨ t = 1 := by omega
        rcases he with rfl | rfl
        · have he := Option.some.inj hx
          subst x
          exact hbound
        · change (P.repeatMachine again).step word (P.repeatConfig again d) = _ at hx
          rw [repeatStep_halt P again hhalt, hagain] at hx
          have he : P.repeatConfig again (P.restartConfig d) = x := Option.some.inj hx
          subst x
          exact hbound
    exact BoundedSegment.append _ (BoundedSegment.append _ (repeatSegment P again hseg) hs) ih

end Repeat
end Mathproof.MinimumGeneration.SearchTransducer
