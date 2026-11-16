import Mathproof.MinimumGenerationNativeReingoldWindow
import Mathproof.MinimumGenerationPhysicalGreedyPrefixCall

namespace Mathproof.MinimumGeneration.VirtualCallbackDriver

open SearchTransducer ReingoldLiveInput
open VirtualTapeStep (routed routedReady)

set_option backward.isDefEq.respectTransparency false

/-- The complete reader loop stops with the precise tape contents and heads
of its last physical cell call. The final native instruction is a halt. -/
theorem ReaderContract.executeHaltingExact {M : SearchTransducer} {R : Callback}
    {e : Fin (routed M).workTapes ↪ Fin R.read.workTapes}
    {raw : List Bool} {source : Int → InputCell} {B w : ℕ}
    (C : ReaderContract M R e raw source B w)
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

end Mathproof.MinimumGeneration.VirtualCallbackDriver

namespace Mathproof.MinimumGeneration.NativeBipartiteReingold

open SearchTransducer ReingoldLiveInput VirtualCallbackDriver
open PhysicalGreedyHeaderInstall (Bank outside)
open PhysicalGreedyPrefixCall (guard scratch view rawWord prefixVerdict)
open PhysicalGreedyHeader (width)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev callMachine (M : SearchTransducer) (R : Callback)
    (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes) : SearchTransducer :=
  LatchedVerdict.machine (VirtualCallbackDriver.machine M R e)

def resultBit (M : SearchTransducer) (R : Callback)
    (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
    (state : Fin (callMachine M R e).states) : Bool :=
  (LatchedVerdict.unpack (finProdFinEquiv.symm state).2).getD false

def readStart (M : SearchTransducer) (R : Callback)
    (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
    (c : (callMachine M R e).Config) : R.read.Config :=
  ⟨R.read.initialState, c.inputHead, c.workHead, c.workCell, []⟩

def nativeStart (M : SearchTransducer) (R : Callback)
    (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
    (B : ℕ) (c : (callMachine M R e).Config) : M.Config :=
  patchWork M B (fun i => c.workCell (e i.castSucc)) M.initial

private theorem preparedStartExact (M : SearchTransducer) (R : Callback)
    (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
    (B : ℕ) (c : (callMachine M R e).Config) (h : c.state = (callMachine M R e).initialState) :
    LatchedVerdict.lift _ (tagRead M R e (nativeStart M R e B c).state (readStart M R e c))
      c.outputReversed = c := by
  change SearchTransducer.Config.mk (callMachine M R e).initialState
    c.inputHead c.workHead c.workCell c.outputReversed = c
  rw [← h]

open scoped Classical in
/-- A real tidy Reingold machine supplies the prepared greedy call as soon as
the recurrent physical one-cell reader is instantiated. Entry requires only
the logarithmic window of the native tapes to have been cleared. The exit
conditions refer to the reader's final cell call alone. -/
theorem preparedCore :
    ∃ (M : SearchTransducer) (C : ℕ), ∀ (R : Callback)
      (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
      (banks : Bank ↪ Fin R.read.workTapes) {n : ℕ} (G : Group (Fin n))
      (B : ℕ) (keep : Set (Fin R.read.workTapes)),
      C * (Nat.log2 ((rawWord G).length + 1) + 1) ≤ B →
      ∀ (reader : ∀ x : Fin n, (callMachine M R e).Config →
          ReaderContract M R e (rawWord G) (inputCells G (fun _ => true) x.val x) B (width n)),
      (∀ (x : Fin n) (c : (callMachine M R e).Config),
        c.state = (callMachine M R e).initialState →
        c.workHead = (fun _ => 0) →
        (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (rawWord G).length →
        PhysicalGreedyHeaderDriver.Live n G.toOne.one.val x.val (view (callMachine M R e) banks c.workCell) →
        (reader x c).ready (nativeStart M R e B c) (readStart M R e c)) →
      (∀ (x : Fin n) (c : (callMachine M R e).Config) (next : M.Config)
          (a b : R.read.Config) (ticks : ℕ),
        (reader x c).ready next a →
        callbackStep M (inputCells G (fun _ => true) x.val x) next = none →
        next.inputHead = 0 → next.workHead = (fun _ => 0) →
        next.workCell = (nativeStart M R e B c).workCell →
        R.read.BoundedSegment (rawWord G) B a b ticks → R.read.step (rawWord G) b = none →
        b.workHead = (fun _ => 0) ∧
        (∀ j ∈ keep, j ∉ scratch (callMachine M R e) banks → b.workCell j = c.workCell j) ∧
        ∀ i : Bank, 11 ≤ i.val → outside (width n) (b.workCell (banks i))) →
      PhysicalGreedyPrefixCall.Core (callMachine M R e) banks (resultBit M R e) G B keep := by
  classical
  obtain ⟨M,K,trace⟩ := nativePrefixWindowRun
  refine ⟨M,K,?_⟩
  intro R e banks n G B keep budget reader setup checkout x c state heads input live
  let C := reader x c
  have hReady := setup x c state heads input live
  obtain ⟨k,d,nrun,nhalt,nout,_,ninput,nheads,ncells⟩ :=
    trace G (fun _ => true) x.val x (fun i => c.workCell (e i.castSucc)) B budget
  obtain ⟨len,out,a,b,t,rawRun,rawHalt,rawOut,lastReady,lastRun,lastStop,lastHeads,lastCells⟩ :=
    C.executeHaltingExact hReady nrun nhalt
  obtain ⟨pHeads,pFrame,pScratch⟩ :=
    checkout x c d a b t lastReady nhalt ninput nheads ncells lastRun lastStop
  obtain ⟨run,halt,hbit,output⟩ :=
    LatchedVerdict.execute (VirtualCallbackDriver.machine M R e) (prior := c.outputReversed) rawRun rawHalt
  rw [preparedStartExact M R e B c state] at run
  let stop := LatchedVerdict.lift _ out c.outputReversed
  refine ⟨len,stop,run,halt,?_,lastHeads.trans pHeads,output,?_,?_⟩
  · change (LatchedVerdict.state (VirtualCallbackDriver.machine M R e) stop).getD false =
      prefixVerdict G x
    rw [hbit, rawOut, nout]
    change decide (x ∈ @Subgroup.closure (Fin n) G (seed (fun _ => true) x.val)) = prefixVerdict G x
    apply Bool.eq_iff_iff.mpr
    have semantic := BipartiteCayley.rawPrefixQuery_correct G (fun _ => true) x.val x
    exact ⟨fun h => semantic.mpr (of_decide_eq_true h),
      fun h => decide_eq_true (semantic.mp h)⟩
  · intro j hj h
    exact (congrFun lastCells j).trans (pFrame j hj h)
  · intro i hi
    rw [show stop.workCell = out.workCell from rfl, lastCells]
    exact pScratch i hi

open scoped Classical in
/-- A real tidy Reingold machine supplies the prepared greedy call with
a one-cell reader that preserves the pointer exterior. Entry requires only
the logarithmic window of the native tapes to have been cleared. The exit
conditions refer to the reader's final cell call alone. -/
theorem preparedFramedCore :
    ∃ (M : SearchTransducer) (C : ℕ), WindowCertificate M C ∧ ∀ (R : Callback)
      (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
      (banks : Bank ↪ Fin R.read.workTapes) {n : ℕ} (G : Group (Fin n))
      (B : ℕ) (keep : Set (Fin R.read.workTapes)),
      C * (Nat.log2 ((rawWord G).length + 1) + 1) ≤ B →
      ∀ (reader : ∀ x : Fin n, (callMachine M R e).Config →
          FramedReaderContract M R e (rawWord G) (inputCells G (fun _ => true) x.val x) B (width n)),
      (∀ (x : Fin n) (c : (callMachine M R e).Config),
        c.state = (callMachine M R e).initialState →
        c.workHead = (fun _ => 0) →
        (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (rawWord G).length →
        PhysicalGreedyHeaderDriver.Live n G.toOne.one.val x.val (view (callMachine M R e) banks c.workCell) →
        (reader x c).ready (nativeStart M R e B c) (readStart M R e c)) →
      (∀ (x : Fin n) (c : (callMachine M R e).Config) (next : M.Config)
          (a b : R.read.Config) (ticks : ℕ),
        (reader x c).ready next a →
        callbackStep M (inputCells G (fun _ => true) x.val x) next = none →
        next.inputHead = 0 → next.workHead = (fun _ => 0) →
        next.workCell = (nativeStart M R e B c).workCell →
        R.read.BoundedSegment (rawWord G) B a b ticks → R.read.step (rawWord G) b = none →
        b.workHead = (fun _ => 0) ∧
        (∀ j ∈ keep, j ∉ scratch (callMachine M R e) banks → b.workCell j = c.workCell j) ∧
        ∀ i : Bank, 11 ≤ i.val → outside (width n) (b.workCell (banks i))) →
      PhysicalGreedyPrefixCall.Core (callMachine M R e) banks (resultBit M R e) G B keep := by
  classical
  obtain ⟨M,K,trace⟩ := nativePrefixWindowRun
  refine ⟨M,K,trace,?_⟩
  intro R e banks n G B keep budget reader setup checkout x c state heads input live
  let C := reader x c
  have hReady := setup x c state heads input live
  obtain ⟨k,d,nrun,nhalt,nout,_,ninput,nheads,ncells⟩ :=
    trace G (fun _ => true) x.val x (fun i => c.workCell (e i.castSucc)) B budget
  obtain ⟨len,out,a,b,t,rawRun,rawHalt,rawOut,lastReady,lastRun,lastStop,lastHeads,lastCells⟩ :=
    C.framedHaltingExact hReady nrun nhalt
  obtain ⟨pHeads,pFrame,pScratch⟩ :=
    checkout x c d a b t lastReady nhalt ninput nheads ncells lastRun lastStop
  obtain ⟨run,halt,hbit,output⟩ :=
    LatchedVerdict.execute (VirtualCallbackDriver.machine M R e) (prior := c.outputReversed) rawRun rawHalt
  rw [preparedStartExact M R e B c state] at run
  let stop := LatchedVerdict.lift _ out c.outputReversed
  refine ⟨len,stop,run,halt,?_,lastHeads.trans pHeads,output,?_,?_⟩
  · change (LatchedVerdict.state (VirtualCallbackDriver.machine M R e) stop).getD false =
      prefixVerdict G x
    rw [hbit, rawOut, nout]
    change decide (x ∈ @Subgroup.closure (Fin n) G (seed (fun _ => true) x.val)) = prefixVerdict G x
    apply Bool.eq_iff_iff.mpr
    have semantic := BipartiteCayley.rawPrefixQuery_correct G (fun _ => true) x.val x
    exact ⟨fun h => semantic.mpr (of_decide_eq_true h),
      fun h => decide_eq_true (semantic.mp h)⟩
  · intro j hj h
    exact (congrFun lastCells j).trans (pFrame j hj h)
  · intro i hi
    rw [show stop.workCell = out.workCell from rfl, lastCells]
    exact pScratch i hi

end Mathproof.MinimumGeneration.NativeBipartiteReingold
