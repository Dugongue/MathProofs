import Mathproof.MinimumGenerationVirtualTapeStep
import Mathproof.MinimumGenerationMacroDispatch

namespace Mathproof.MinimumGeneration.VirtualCallbackDriver

open Mathproof.Multitape SearchTransducer
open Mathproof.Multitape.Locality (moveOffset)

private def resumeState (M : SearchTransducer) (q : Fin M.states) (cell : InputCell) :
    Fin (VirtualTapeStep.routed M).states :=
  (VirtualTapeStep.routedReady M
    ⟨q, 0, fun _ => 0, fun _ _ => none, []⟩ cell 0 0 (fun _ => none)).state

/-- The native state stays in finite control while the physical callback runs. -/
structure Callback where
  read : SearchTransducer
  returnCell : Fin read.states → InputCell

variable (M : SearchTransducer) (R : Callback)
variable (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)

abbrev play := (VirtualTapeStep.routed M).relocateBanks e
private abbrev readStates := M.states * R.read.states
private abbrev playStates := 2 * (VirtualTapeStep.routed M).states

private def tagReadState (q : Fin M.states) (r : Fin R.read.states) :
    Fin (readStates M R + playStates M) :=
  Fin.castAdd _ (finProdFinEquiv (q, r))

private def tagPlayState (fired : Fin 2) (p : Fin (VirtualTapeStep.routed M).states) :
    Fin (readStates M R + playStates M) :=
  Fin.natAdd _ (finProdFinEquiv (fired, p))

private def idle : Fin R.read.workTapes → Action (Option Bool) := fun _ => ⟨none, .stay⟩

private abbrev PlayCommand := Fin (VirtualTapeStep.routed M).states × Move ×
  (Fin R.read.workTapes → Action (Option Bool)) × Option Bool

private def dispatchPlay (fired : Fin 2) (p : Fin (VirtualTapeStep.routed M).states)
    (command : Option (PlayCommand M R)) :
    Option (Fin (readStates M R + playStates M) × Move ×
      (Fin R.read.workTapes → Action (Option Bool)) × Option Bool) :=
  match command with
  | some (p', m, a, b) => some (tagPlayState M R 1 p', m, a, b)
  | none =>
    if fired = 0 then none else
      some (tagReadState M R (finProdFinEquiv.symm p).1 R.read.initialState, .stay, idle R, none)


/-- A callback and any number of native instructions use a single finite
physical control. The first successful native action sets a flag. A halt before
that action stops the driver, while a pointer routine’s halt calls the reader. -/
@[reducible] def machine : SearchTransducer where
  states := readStates M R + playStates M
  workTapes := R.read.workTapes
  initialState := tagReadState M R M.initialState R.read.initialState
  transition state inp scanned :=
    (finSumFinEquiv.symm state).elim
      (fun left =>
        let (q, r) := finProdFinEquiv.symm left
        match R.read.transition r inp scanned with
        | some (r', m, a, b) => some (tagReadState M R q r', m, a, b)
        | none => some (tagPlayState M R 0 (resumeState M q (R.returnCell r)), .stay, idle R, none))
      (fun right =>
        let (fired, p) := finProdFinEquiv.symm right
        dispatchPlay M R fired p ((play M R e).transition p inp scanned))

abbrev tagRead (q : Fin M.states) (c : R.read.Config) : (machine M R e).Config :=
  ⟨tagReadState M R q c.state, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

abbrev tagPlay (fired : Fin 2) (c : (play M R e).Config) : (machine M R e).Config :=
  ⟨tagPlayState M R fired c.state, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

def acceptCell (q : Fin M.states) (c : R.read.Config) : (play M R e).Config :=
  ⟨resumeState M q (R.returnCell c.state), c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

def requestCell (c : (play M R e).Config) : R.read.Config :=
  ⟨R.read.initialState, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

def resumedNative (c : (play M R e).Config) : Fin M.states := (finProdFinEquiv.symm c.state).1

private theorem transitionPlay (fired : Fin 2) (p : Fin (VirtualTapeStep.routed M).states)
    (inp : InputCell) (scanned : Fin R.read.workTapes → Option Bool) :
    (machine M R e).transition (tagPlayState M R fired p) inp scanned =
      dispatchPlay M R fired p ((play M R e).transition p inp scanned) := by
  simp only [machine, tagPlayState, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr,
    Equiv.symm_apply_apply]


theorem stepRead {raw : List Bool} (q : Fin M.states) {c d : R.read.Config}
    (h : R.read.step raw c = some d) :
    (machine M R e).step raw (tagRead M R e q c) = some (tagRead M R e q d) := by
  unfold SearchTransducer.step at h ⊢
  cases ht : R.read.transition c.state (readInput raw c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => simp [ht] at h
  | some a =>
    obtain ⟨r, m, act, b⟩ := a
    simp only [ht, Option.map_some, Option.some.injEq] at h
    subst d
    simp only [machine, tagReadState, finSumFinEquiv_symm_apply_castAdd,
      Sum.elim_inl, Equiv.symm_apply_apply, ht]
    rfl

theorem stepPlay {raw : List Bool} (fired : Fin 2) {c d : (play M R e).Config}
    (h : (play M R e).step raw c = some d) :
    (machine M R e).step raw (tagPlay M R e fired c) = some (tagPlay M R e 1 d) := by
  unfold SearchTransducer.step at h ⊢
  cases ht : (play M R e).transition c.state (readInput raw c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none =>
    with_unfolding_all erw [ht] at h
    cases h
  | some a =>
    obtain ⟨r, m, act, b⟩ := a
    with_unfolding_all erw [ht] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst d
    have h' := (transitionPlay M R e fired c.state (readInput raw c.inputHead)
      (fun i => c.workCell i (c.workHead i))).trans (congrArg (dispatchPlay M R fired c.state) ht)
    generalize hcmd : (machine M R e).transition (tagPlayState M R fired c.state)
      (readInput raw c.inputHead) (fun i => c.workCell i (c.workHead i)) = command
    rw [hcmd] at h'
    subst command
    rfl

theorem finishRead {raw : List Bool} (q : Fin M.states) (c : R.read.Config)
    (h : R.read.step raw c = none) :
    (machine M R e).step raw (tagRead M R e q c) =
      some (tagPlay M R e 0 (acceptCell M R e q c)) := by
  unfold SearchTransducer.step at h ⊢
  have ht := Option.map_eq_none_iff.mp h
  simp only [machine, tagReadState, finSumFinEquiv_symm_apply_castAdd,
    Sum.elim_inl, Equiv.symm_apply_apply, ht, Option.map_some]
  simp only [tagPlay, acceptCell, idle, moveOffset, Int.add_zero, Option.getD_none,
    Option.elim]
  apply congrArg some
  congr 1
  funext i j
  exact ite_self _

theorem finishPlay {raw : List Bool} (c : (play M R e).Config)
    (h : (play M R e).step raw c = none) :
    (machine M R e).step raw (tagPlay M R e 1 c) =
      some (tagRead M R e (resumedNative M R e c) (requestCell M R e c)) := by
  unfold SearchTransducer.step at h ⊢
  have ht := Option.map_eq_none_iff.mp h
  have h' := (transitionPlay M R e 1 c.state (readInput raw c.inputHead)
    (fun i => c.workCell i (c.workHead i))).trans (congrArg (dispatchPlay M R 1 c.state) ht)
  generalize hcmd : (machine M R e).transition (tagPlayState M R 1 c.state)
    (readInput raw c.inputHead) (fun i => c.workCell i (c.workHead i)) = command
  rw [hcmd] at h'
  subst command
  simp only [dispatchPlay, show (1 : Fin 2) = 0 ↔ False by decide, if_false,
    Option.map_some, tagRead, requestCell, resumedNative, idle, moveOffset,
    Int.add_zero, Option.getD_none, Option.elim]
  apply congrArg some
  congr 1
  funext i j
  exact ite_self _

theorem stopPlay {raw : List Bool} (c : (play M R e).Config)
    (h : (play M R e).step raw c = none) :
    (machine M R e).step raw (tagPlay M R e 0 c) = none := by
  unfold SearchTransducer.step at h ⊢
  have ht := Option.map_eq_none_iff.mp h
  have h' := (transitionPlay M R e 0 c.state (readInput raw c.inputHead)
    (fun i => c.workCell i (c.workHead i))).trans (congrArg (dispatchPlay M R 0 c.state) ht)
  generalize hcmd : (machine M R e).transition (tagPlayState M R 0 c.state)
    (readInput raw c.inputHead) (fun i => c.workCell i (c.workHead i)) = command
  rw [hcmd] at h'
  subst command
  rfl

theorem runRead {raw : List Bool} (q : Fin M.states) {c d : R.read.Config} {len : ℕ}
    (h : R.read.runFrom raw c len = some d) :
    (machine M R e).runFrom raw (tagRead M R e q c) len = some (tagRead M R e q d) := by
  induction len generalizing d with
  | zero => cases h; rfl
  | succ k ih =>
    obtain ⟨p, run, step⟩ := Option.bind_eq_some_iff.mp h
    rw [SearchTransducer.runFrom, ih run, Option.bind_some]
    exact stepRead M R e q step

theorem runPlay {raw : List Bool} (fired : Fin 2) {c d : (play M R e).Config} {len : ℕ}
    (h : (play M R e).runFrom raw c len = some d) :
    (machine M R e).runFrom raw (tagPlay M R e fired c) len =
      some (tagPlay M R e (if len = 0 then fired else 1) d) := by
  induction len generalizing d with
  | zero => cases h; rfl
  | succ k ih =>
    obtain ⟨p, run, step⟩ := Option.bind_eq_some_iff.mp h
    simp only [SearchTransducer.runFrom, ih run, Option.bind_some, Nat.succ_ne_zero, if_false]
    exact stepPlay M R e _ step

private theorem existingPrefix {A : SearchTransducer} {raw : List Bool} {c d : A.Config} {n k : ℕ}
    (h : A.runFrom raw c n = some d) (hk : k ≤ n) :
    ∃ p, A.runFrom raw c k = some p := by
  have e : n = k + (n - k) := by omega
  rw [e, SearchTransducer.runFrom_add] at h
  obtain ⟨p, hp, _⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨p, hp⟩

theorem readSegment {raw : List Bool} {B len : ℕ} (q : Fin M.states) {c d : R.read.Config}
    (h : R.read.BoundedSegment raw B c d len) :
    (machine M R e).BoundedSegment raw B (tagRead M R e q c) (tagRead M R e q d) len := by
  refine ⟨runRead M R e q h.1, ?_⟩
  intro k hk p hp
  obtain ⟨d, hd⟩ := existingPrefix h.1 hk
  rw [runRead M R e q hd] at hp
  cases hp
  exact h.2 k hk d hd

theorem playSegment {raw : List Bool} {B len : ℕ}
    (fired : Fin 2) {c d : (play M R e).Config}
    (h : (play M R e).BoundedSegment raw B c d len) :
    (machine M R e).BoundedSegment raw B (tagPlay M R e fired c)
      (tagPlay M R e (if len = 0 then fired else 1) d) len := by
  refine ⟨runPlay M R e fired h.1, ?_⟩
  intro k hk p hp
  obtain ⟨d, hd⟩ := existingPrefix h.1 hk
  rw [runPlay M R e fired hd] at hp
  cases hp
  exact h.2 k hk d hd

private theorem singleSegment (M : SearchTransducer) {raw : List Bool} {B : ℕ}
    {c d : M.Config} (h : M.step raw c = some d)
    (hc : M.Bounded raw B c) (hd : M.Bounded raw B d) :
    M.BoundedSegment raw B c d 1 := by
  refine ⟨h, ?_⟩
  intro k hk x hx
  interval_cases k
  · cases hx
    exact hc
  · change M.step raw c = some x at hx
    rw [h] at hx
    cases hx
    exact hd

/-- One complete physical call and virtual instruction, including both actual
handoff transitions, under the common per-prefix head bound. -/
theorem driverCycle {raw : List Bool} {B a b : ℕ} (q : Fin M.states)
    {c d : R.read.Config} {out : (play M R e).Config}
    (read : R.read.BoundedSegment raw B c d a)
    (readDone : R.read.step raw d = none) (positive : 0 < b)
    (action : (play M R e).BoundedSegment raw B (acceptCell M R e q d) out b)
    (actionDone : (play M R e).step raw out = none) :
    (machine M R e).BoundedSegment raw B (tagRead M R e q c)
      (tagRead M R e (resumedNative M R e out) (requestCell M R e out)) (a + 1 + b + 1) := by
  have hRead := readSegment M R e q read
  have hBound := read.2 _ le_rfl _ read.1
  have left := singleSegment (machine M R e) (finishRead M R e q d readDone) hBound hBound
  have hPlay := playSegment M R e 0 action
  rw [if_neg (by omega : b ≠ 0)] at hPlay
  have hBound := action.2 _ le_rfl _ action.1
  have right := singleSegment (machine M R e) (finishPlay M R e out actionDone) hBound hBound
  exact BoundedSegment.append _ (BoundedSegment.append _ (BoundedSegment.append _ hRead left) hPlay) right

/-- A callback followed by a native halt emits no new bit and halts the physical
driver. The final callback answer remains in finite control. -/
theorem driverStop {raw : List Bool} {B a : ℕ} (q : Fin M.states)
    {c d : R.read.Config}
    (read : R.read.BoundedSegment raw B c d a)
    (readDone : R.read.step raw d = none)
    (stop : (play M R e).step raw (acceptCell M R e q d) = none) :
    let out := tagPlay M R e 0 (acceptCell M R e q d)
    (machine M R e).BoundedSegment raw B (tagRead M R e q c) out (a + 1) ∧
      (machine M R e).step raw out = none := by
  have readBound := read.2 _ le_rfl _ read.1
  have left := singleSegment (machine M R e) (finishRead M R e q d readDone) readBound readBound
  exact ⟨BoundedSegment.append _ (readSegment M R e q read) left, stopPlay M R e _ stop⟩

section VirtualExecution

open VirtualTapeStep (AtAddress pointerBank routed routedReady)
open ReingoldLiveInput (callbackStep)

/-- A reader cycle also preserves the full exterior of the pointer bank. -/
theorem driverExecuteFramed {raw : List Bool} {B w p a : ℕ}
    {native next : M.Config} {start result : R.read.Config}
    (read : R.read.BoundedSegment raw B start result a)
    (readDone : R.read.step raw result = none)
    (nativeStep : callbackStep M (fun _ => R.returnCell result.state) native = some next)
    (position : native.inputHead + 1 = (p : Int)) (valid : (-1 : Int) ≤ next.inputHead)
    {realHead base : Int} {pointer : Int → Option Bool}
    (hin : (-1 : Int) ≤ realHead ∧ realHead ≤ (raw.length : Int))
    (before : ∀ i, (native.workHead i).natAbs ≤ B)
    (after : ∀ i, (next.workHead i).natAbs ≤ B)
    (window : ∀ j, base ≤ j → j ≤ base + w + 1 → j.natAbs ≤ B)
    (hLeft : pointer base = none) (hRight : pointer (base + w + 1) = none)
    (bits : TapeArithmetic.block pointer (base + 1) (encodeLabel w p))
    (ready : acceptCell M R e native.state result =
      (routed M).bankConfig e (routedReady M native (R.returnCell result.state) realHead base pointer)
        result.workHead result.workCell) :
    ∃ (b : ℕ) (out : (routed M).Config), 0 < b ∧ b ≤ 2 * w + 4 ∧
      (machine M R e).BoundedSegment raw B (tagRead M R e native.state start)
        (tagRead M R e next.state
          (requestCell M R e ((routed M).bankConfig e out result.workHead result.workCell)))
        (a + 1 + b + 1) ∧ AtAddress M next realHead base w out ∧
      VirtualTapeStep.PointerExterior M base w pointer out := by
  obtain ⟨b, out, time, action, done, aligned, exterior⟩ :=
    VirtualTapeStep.routedExecuteFramed M raw B w p (R.returnCell result.state) native next
      realHead base pointer nativeStep position valid hin before after window hLeft hRight bits
  have positive : 0 < b := by
    by_contra! h
    have hb : b = 0 := Nat.eq_zero_of_le_zero h
    subst b
    have econfig := (Option.some.inj action.1).symm
    rw [econfig] at done
    obtain ⟨_, first, _⟩ := VirtualTapeStep.routedPlayback M raw (R.returnCell result.state)
      native next realHead base pointer nativeStep
    rw [first] at done
    cases done
  have cap := read.2 _ le_rfl _ read.1
  have bankAction := relocateBanks_segment (routed M) e (heads := result.workHead) (cells := result.workCell)
    action (fun t _ => cap.2.2 t)
  have bankDone := relocateBanks_step (routed M) e raw out result.workHead result.workCell
  rw [done] at bankDone
  rw [← ready] at bankAction
  have cycle := driverCycle M R e native.state read readDone positive bankAction bankDone
  have stateEq :
      resumedNative M R e ((routed M).bankConfig e out result.workHead result.workCell) =
        next.state := aligned.state
  rw [stateEq] at cycle
  exact ⟨b, out, positive, time, cycle, aligned, exterior⟩

/-- Connect the addressed reader's return to one checked physical native step. -/
theorem driverExecute {raw : List Bool} {B w p a : ℕ}
    {native next : M.Config} {start result : R.read.Config}
    (read : R.read.BoundedSegment raw B start result a)
    (readDone : R.read.step raw result = none)
    (nativeStep : callbackStep M (fun _ => R.returnCell result.state) native = some next)
    (position : native.inputHead + 1 = (p : Int)) (valid : (-1 : Int) ≤ next.inputHead)
    {realHead base : Int} {pointer : Int → Option Bool}
    (hin : (-1 : Int) ≤ realHead ∧ realHead ≤ (raw.length : Int))
    (before : ∀ i, (native.workHead i).natAbs ≤ B)
    (after : ∀ i, (next.workHead i).natAbs ≤ B)
    (window : ∀ j, base ≤ j → j ≤ base + w + 1 → j.natAbs ≤ B)
    (hLeft : pointer base = none) (hRight : pointer (base + w + 1) = none)
    (bits : TapeArithmetic.block pointer (base + 1) (encodeLabel w p))
    (ready : acceptCell M R e native.state result =
      (routed M).bankConfig e (routedReady M native (R.returnCell result.state) realHead base pointer)
        result.workHead result.workCell) :
    ∃ (b : ℕ) (out : (routed M).Config), 0 < b ∧ b ≤ 2 * w + 4 ∧
      (machine M R e).BoundedSegment raw B (tagRead M R e native.state start)
        (tagRead M R e next.state
          (requestCell M R e ((routed M).bankConfig e out result.workHead result.workCell)))
        (a + 1 + b + 1) ∧ AtAddress M next realHead base w out := by
  obtain ⟨b,out,hb,ht,run,aligned,_⟩ :=
    driverExecuteFramed M R e read readDone nativeStep position valid hin before after window
      hLeft hRight bits ready
  exact ⟨b,out,hb,ht,run,aligned⟩

/-- A reader return witnessing a native no-transition propagates to the
physical driver's final halt. -/
theorem driverNativeStop {raw : List Bool} {B a : ℕ}
    {native : M.Config} {start result : R.read.Config}
    (read : R.read.BoundedSegment raw B start result a)
    (readDone : R.read.step raw result = none)
    (nativeStop : callbackStep M (fun _ => R.returnCell result.state) native = none)
    {realHead base : Int} {pointer : Int → Option Bool}
    (ready : acceptCell M R e native.state result =
      (routed M).bankConfig e (routedReady M native (R.returnCell result.state) realHead base pointer)
        result.workHead result.workCell) :
    ∃ out, (machine M R e).BoundedSegment raw B (tagRead M R e native.state start) out (a + 1) ∧
      (machine M R e).step raw out = none ∧ out.outputReversed = result.outputReversed := by
  have hs := VirtualTapeStep.routedStops M raw (R.returnCell result.state) native
    realHead base pointer nativeStop
  have physical := relocateBanks_step (routed M) e raw
    (routedReady M native (R.returnCell result.state) realHead base pointer)
    result.workHead result.workCell
  rw [hs, ← ready] at physical
  obtain ⟨seg, done⟩ := driverStop M R e native.state read readDone physical
  exact ⟨_, seg, done, rfl⟩

end VirtualExecution


section CompleteRun

open VirtualTapeStep (AtAddress routed routedReady)
open ReingoldLiveInput (callbackStep callbackRun)

/-- Correctness interface for a physical addressed cell reader. Its own
initialization invariant can include raw data, live bounds and reusable scratch.
A call produces one cell and restores the native and address banks. -/
structure ReaderContract (raw : List Bool) (source : Int → InputCell) (B w : ℕ) where
  ready : M.Config → R.read.Config → Prop
  windowBase : Int
  window : ∀ j, windowBase ≤ j → j ≤ windowBase + w + 1 → j.natAbs ≤ B
  call : ∀ {native start}, ready native start →
    ∃ (a : ℕ) (result : R.read.Config) (realHead : Int) (pointer : Int → Option Bool),
      R.read.BoundedSegment raw B start result a ∧ R.read.step raw result = none ∧
      R.returnCell result.state = source native.inputHead ∧
      native.outputReversed = result.outputReversed ∧
      pointer windowBase = none ∧ pointer (windowBase + w + 1) = none ∧
      TapeArithmetic.block pointer (windowBase + 1) (encodeLabel w (native.inputHead + 1).toNat) ∧
      acceptCell M R e native.state result =
        (routed M).bankConfig e (routedReady M native (R.returnCell result.state) realHead windowBase pointer)
          result.workHead result.workCell ∧
      (-1 : Int) ≤ realHead ∧ realHead ≤ (raw.length : Int) ∧
      (∀ j, (native.workHead j).natAbs ≤ B) ∧ (-1 : Int) ≤ native.inputHead ∧
      (∀ next, callbackStep M source native = some next →
        ((-1 : Int) ≤ next.inputHead ∧ ∀ j, (next.workHead j).natAbs ≤ B)) ∧
      (∀ next out, AtAddress M next realHead windowBase w out →
        ready next (requestCell M R e ((routed M).bankConfig e out result.workHead result.workCell)))

namespace ReaderContract

variable {M R e}
variable {raw : List Bool} {source : Int → InputCell} {B w : ℕ}
variable (C : ReaderContract M R e raw source B w)

theorem executeNext {native next : M.Config} {start : R.read.Config}
    (ready : C.ready native start) (step : callbackStep M source native = some next) :
    ∃ len finish, (machine M R e).BoundedSegment raw B (tagRead M R e native.state start)
      (tagRead M R e next.state finish) len ∧ C.ready next finish := by
  obtain ⟨a, result, realHead, pointer, run, done, cell, _, left, right, bits, ships,
    realLow, realHigh, headBound, nativeLow, nextBound, restore⟩ := C.call ready
  have hStep : callbackStep M (fun _ => R.returnCell result.state) native = some next := by
    unfold callbackStep at *
    rwa [cell]
  have hAddr : native.inputHead + 1 = (((native.inputHead + 1).toNat : ℕ) : Int) := by
    rw [Int.toNat_of_nonneg]
    omega
  have bounds := nextBound next step
  obtain ⟨b, out, _, _, segment, position⟩ := driverExecute M R e run done hStep hAddr
    bounds.1 ⟨realLow, realHigh⟩ headBound bounds.2 C.window left right bits ships
  exact ⟨a + 1 + b + 1, _, segment, restore next out position⟩

theorem executePrefix {native next : M.Config} {start : R.read.Config} {rounds : ℕ}
    (ready : C.ready native start) (run : callbackRun M source native rounds = some next) :
    ∃ len finish, (machine M R e).BoundedSegment raw B (tagRead M R e native.state start)
      (tagRead M R e next.state finish) len ∧ C.ready next finish := by
  induction rounds generalizing next with
  | zero =>
    cases run
    obtain ⟨a, result, realHead, pointer, segment, _⟩ := C.call ready
    exact ⟨0, start, ⟨rfl, by
      intro i hi x hx
      have hz : i = 0 := by omega
      subst i
      cases hx
      exact (readSegment M R e native.state segment).2 0 (Nat.zero_le _) _ rfl⟩, ready⟩
  | succ rounds ih =>
    obtain ⟨mid, pre, step⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨a, c, s, hc⟩ := ih pre
    obtain ⟨b, d, t, hd⟩ := C.executeNext hc step
    exact ⟨a + b, d, BoundedSegment.append _ s t, hd⟩

/-- The finite driver follows the entire halting native run. The same work
bound applies to every bit move of every callback and native instruction. -/
theorem executeHalting {native next : M.Config} {start : R.read.Config} {rounds : ℕ}
    (ready : C.ready native start) (run : callbackRun M source native rounds = some next)
    (nativeHalt : callbackStep M source next = none) :
    ∃ len out, (machine M R e).BoundedSegment raw B (tagRead M R e native.state start) out len ∧
      (machine M R e).step raw out = none ∧ out.outputReversed = next.outputReversed := by
  obtain ⟨a, mid, hPrefix, hReady⟩ := C.executePrefix ready run
  obtain ⟨b, result, realHead, pointer, read, readDone, cell, output, _, _, _, hEntry, _⟩ :=
    C.call hReady
  have hStop : callbackStep M (fun _ => R.returnCell result.state) next = none := by
    unfold callbackStep at *
    rwa [cell]
  obtain ⟨out, hLast, hHalt, hOutput⟩ := driverNativeStop M R e read readDone hStop hEntry
  exact ⟨a + (b + 1), out, BoundedSegment.append _ hPrefix hLast, hHalt, hOutput.trans output.symm⟩

end ReaderContract
/-- The same addressed reader loop, with an exact frame for the updated
native pointer bank available when reestablishing the next ready state. -/
structure FramedReaderContract (raw : List Bool) (source : Int → InputCell) (B w : ℕ) where
  ready : M.Config → R.read.Config → Prop
  windowBase : Int
  window : ∀ j, windowBase ≤ j → j ≤ windowBase + w + 1 → j.natAbs ≤ B
  call : ∀ {native start}, ready native start →
    ∃ (a : ℕ) (result : R.read.Config) (realHead : Int) (pointer : Int → Option Bool),
      R.read.BoundedSegment raw B start result a ∧ R.read.step raw result = none ∧
      R.returnCell result.state = source native.inputHead ∧
      native.outputReversed = result.outputReversed ∧
      pointer windowBase = none ∧ pointer (windowBase + w + 1) = none ∧
      TapeArithmetic.block pointer (windowBase + 1) (encodeLabel w (native.inputHead + 1).toNat) ∧
      acceptCell M R e native.state result =
        (routed M).bankConfig e (routedReady M native (R.returnCell result.state) realHead windowBase pointer)
          result.workHead result.workCell ∧
      (-1 : Int) ≤ realHead ∧ realHead ≤ (raw.length : Int) ∧
      (∀ j, (native.workHead j).natAbs ≤ B) ∧ (-1 : Int) ≤ native.inputHead ∧
      (∀ next, callbackStep M source native = some next →
        ((-1 : Int) ≤ next.inputHead ∧ ∀ j, (next.workHead j).natAbs ≤ B)) ∧
      (∀ next out, AtAddress M next realHead windowBase w out →
        VirtualTapeStep.PointerExterior M windowBase w pointer out →
        callbackStep M source native = some next →
        ready next (requestCell M R e ((routed M).bankConfig e out result.workHead result.workCell)))

namespace FramedReaderContract

variable {M R e}
variable {raw : List Bool} {source : Int → InputCell} {B w : ℕ}
variable (C : FramedReaderContract M R e raw source B w)

theorem executeNext {native next : M.Config} {start : R.read.Config}
    (ready : C.ready native start) (step : callbackStep M source native = some next) :
    ∃ len finish, (machine M R e).BoundedSegment raw B (tagRead M R e native.state start)
      (tagRead M R e next.state finish) len ∧ C.ready next finish := by
  obtain ⟨a, result, realHead, pointer, run, done, cell, _, left, right, bits, ships,
    realLow, realHigh, headBound, nativeLow, nextBound, restore⟩ := C.call ready
  have hStep : callbackStep M (fun _ => R.returnCell result.state) native = some next := by
    unfold callbackStep at *
    rwa [cell]
  have hAddr : native.inputHead + 1 = (((native.inputHead + 1).toNat : ℕ) : Int) := by
    rw [Int.toNat_of_nonneg]
    omega
  have bounds := nextBound next step
  obtain ⟨b, out, _, _, segment, position, exterior⟩ := driverExecuteFramed M R e run done hStep hAddr
    bounds.1 ⟨realLow, realHigh⟩ headBound bounds.2 C.window left right bits ships
  exact ⟨a + 1 + b + 1, _, segment, restore next out position exterior step⟩

theorem executePrefix {native next : M.Config} {start : R.read.Config} {rounds : ℕ}
    (ready : C.ready native start) (run : callbackRun M source native rounds = some next) :
    ∃ len finish, (machine M R e).BoundedSegment raw B (tagRead M R e native.state start)
      (tagRead M R e next.state finish) len ∧ C.ready next finish := by
  induction rounds generalizing next with
  | zero =>
    cases run
    obtain ⟨a, result, realHead, pointer, segment, _⟩ := C.call ready
    exact ⟨0, start, ⟨rfl, by
      intro i hi x hx
      have hz : i = 0 := by omega
      subst i
      cases hx
      exact (readSegment M R e native.state segment).2 0 (Nat.zero_le _) _ rfl⟩, ready⟩
  | succ rounds ih =>
    obtain ⟨mid, pre, step⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨a, c, s, hc⟩ := ih pre
    obtain ⟨b, d, t, hd⟩ := C.executeNext hc step
    exact ⟨a + b, d, BoundedSegment.append _ s t, hd⟩

/-- The finite driver follows the entire halting native run. The same work
bound applies to every bit move of every callback and native instruction. -/
theorem executeHalting {native next : M.Config} {start : R.read.Config} {rounds : ℕ}
    (ready : C.ready native start) (run : callbackRun M source native rounds = some next)
    (nativeHalt : callbackStep M source next = none) :
    ∃ len out, (machine M R e).BoundedSegment raw B (tagRead M R e native.state start) out len ∧
      (machine M R e).step raw out = none ∧ out.outputReversed = next.outputReversed := by
  obtain ⟨a, mid, hPrefix, hReady⟩ := C.executePrefix ready run
  obtain ⟨b, result, realHead, pointer, read, readDone, cell, output, _, _, _, hEntry, _⟩ :=
    C.call hReady
  have hStop : callbackStep M (fun _ => R.returnCell result.state) next = none := by
    unfold callbackStep at *
    rwa [cell]
  obtain ⟨out, hLast, hHalt, hOutput⟩ := driverNativeStop M R e read readDone hStop hEntry
  exact ⟨a + (b + 1), out, BoundedSegment.append _ hPrefix hLast, hHalt, hOutput.trans output.symm⟩

end FramedReaderContract

namespace FramedReaderContract
/-- The complete reader loop stops with the precise tape contents and heads
of its last physical cell call. The final native instruction is a halt. -/
theorem framedHaltingExact {M : SearchTransducer} {R : Callback}
    {e : Fin (routed M).workTapes ↪ Fin R.read.workTapes}
    {raw : List Bool} {source : Int → InputCell} {B w : ℕ}
    (C : FramedReaderContract M R e raw source B w)
    {native next : M.Config} {start : R.read.Config} {rounds : ℕ}
    (ready : C.ready native start)
    (run : callbackRun M source native rounds = some next)
    (halt : callbackStep M source next = none) :
    ∃ (len : ℕ) (d : (machine M R e).Config) (lastStart lastResult : R.read.Config) (a : ℕ),
      (machine M R e).BoundedSegment raw B (tagRead M R e native.state start) d len ∧
      (machine M R e).step raw d = none ∧ d.outputReversed = next.outputReversed ∧
      C.ready next lastStart ∧ R.read.BoundedSegment raw B lastStart lastResult a ∧
      R.read.step raw lastResult = none ∧
      d.workHead = lastResult.workHead ∧ d.workCell = lastResult.workCell := by
  obtain ⟨prefixLen, mid, hPrefix, hReady⟩ := C.executePrefix ready run
  obtain ⟨a, result, real, pointer, read, readDone, cell, output, _, _, _, aligned, _⟩ :=
    C.call hReady
  have hStop : callbackStep M (fun _ => R.returnCell result.state) next = none := by
    unfold callbackStep at *
    rwa [cell]
  have readyStop := VirtualTapeStep.routedStops M raw (R.returnCell result.state) next
    real C.windowBase pointer hStop
  have physical := relocateBanks_step (routed M) e raw
    (routedReady M next (R.returnCell result.state) real C.windowBase pointer)
    result.workHead result.workCell
  rw [readyStop, ← aligned] at physical
  obtain ⟨tail, stopped⟩ := driverStop M R e next.state read readDone physical
  refine ⟨prefixLen+(a+1),_,mid,result,a, BoundedSegment.append _ hPrefix tail, stopped,
    output.symm, hReady, read, readDone, rfl, rfl⟩

end FramedReaderContract

end CompleteRun


end Mathproof.MinimumGeneration.VirtualCallbackDriver
