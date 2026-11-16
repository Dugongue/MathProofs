import Mathproof.MinimumGenerationNativePhysicalReader

namespace Mathproof.MinimumGeneration.NativePhysicalReader

open SearchTransducer VirtualCallbackDriver ReingoldLiveInput
open NativeBipartiteReingold
open PhysicalGreedyPrefixCall (prefixVerdict)
open CayleyQueryPrefixModel (width)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

private theorem sameTerminal (M : SearchTransducer) (raw : List Bool) (c : M.Config)
    {k l : ℕ} {d e : M.Config}
    (one : M.runFrom raw c k = some d) (stop : M.step raw d = none)
    (two : M.runFrom raw c l = some e) (other : M.step raw e = none) : d = e := by
  have past {a b : ℕ} {x y : M.Config} (lt : a < b)
      (pre : M.runFrom raw c a = some x) (halt : M.step raw x = none)
      (post : M.runFrom raw c b = some y) : False := by
    have sum : b = a+1+(b-(a+1)) := by omega
    rw [sum, SearchTransducer.runFrom_add, SearchTransducer.runFrom, pre, Option.bind_some, halt] at post
    simp at post
  rcases lt_trichotomy k l with lt | rfl | gt
  · exact (past lt one stop two).elim
  · exact Option.some.inj (one.symm.trans two)
  · exact (past gt two other one).elim

abbrev prefixMachine (M : SearchTransducer) := callMachine M (callback M) (playbackBanks M)
abbrev prefixBit (M : SearchTransducer) := resultBit M (callback M) (playbackBanks M)

private theorem initialLayout (M : SearchTransducer) (R : Callback)
    (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
    (B : ℕ) (c : (callMachine M R e).Config) (h : c.state = (callMachine M R e).initialState) :
    LatchedVerdict.lift (VirtualCallbackDriver.machine M R e)
      (tagRead M R e (nativeStart M R e B c).state (readStart M R e c)) c.outputReversed = c := by
  change SearchTransducer.Config.mk (callMachine M R e).initialState c.inputHead
    c.workHead c.workCell c.outputReversed = c
  rw [← h]

private theorem finishReader {M : SearchTransducer} {n : ℕ}
    (G : Group (Fin n)) (x : Fin n) (ticks : List Bool) (B : ℕ)
    (origin terminal : M.Config) (k : ℕ)
    (run : callbackRun M (inputCells G (fun _ => true) x.val x) origin k = some terminal)
    (halt : callbackStep M (inputCells G (fun _ => true) x.val x) terminal = none)
    (space : ∀ j c, j ≤ k → callbackRun M (inputCells G (fun _ => true) x.val x) origin j = some c →
      (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤
        (Cslib.Complexity.encUSTCON (instanceOf G (fun _ => true) x.val x)).length ∧
        ∀ i, (c.workHead i).natAbs ≤ B)
    (clockBound : ticks.length + 1 ≤ B) (window : width n + 1 ≤ B)
    (nativePos : terminal.inputHead = 0) (nativeHeads : terminal.workHead = fun _ => 0)
    (start : (callback M).read.Config) (init : Ready G x ticks B origin k origin start) :
    let word := @encodeCayley n G.toMul
    let D := VirtualCallbackDriver.machine M (callback M) (playbackBanks M)
    ∃ (len : ℕ) (last : D.Config),
      D.BoundedSegment word B (tagRead M (callback M) (playbackBanks M) origin.state start) last len ∧
      D.step word last = none ∧ last.outputReversed = terminal.outputReversed ∧
      last.workHead = (fun _ => 0) ∧
      (∀ i, last.workCell (nativeBank M i) = terminal.workCell i) ∧
      CayleyReaderCycle.Ready G x.val (BipartiteCayley.left G.toOne.one)
        (BipartiteCayley.left x) 1 ticks (fun i => last.workCell (readerBank M i)) := by
  let C := contract G x ticks B origin terminal k run halt space clockBound window
  let R := callback M
  let word := @encodeCayley n G.toMul
  obtain ⟨len,last,a,b,rlen,physical,stop,printed,lastReady,lastRun,lastStop,lastHeads,lastCells⟩ :=
    C.framedHaltingExact init run halt
  obtain ⟨j,hj,atTerminal⟩ := lastReady.reached
  obtain ⟨lo,hi,bnd⟩ := space j terminal hj atTerminal
  obtain ⟨len',z,r,zStop,_,_,_,_,rHeads,nHeads,nTapes,returned⟩ :=
    executeCell G x ticks lastReady lo hi bnd clockBound
  have same := sameTerminal R.read word a lastRun.1 lastStop r.1 zStop
  refine ⟨len,last,physical,stop,printed,?_,?_,?_⟩
  · rw [lastHeads,same]
    funext i
    refine Fin.addCases (fun q => ?_) (fun q => ?_) i
    · exact rHeads q
    · exact (nHeads q).trans (congrFun nativeHeads q)
  · intro i
    rw [lastCells,same]
    exact nTapes i
  · rw [lastCells,same]
    have position : (terminal.inputHead + 1).toNat = 1 := by
      rw [nativePos]
      rfl
    rw [position] at returned
    exact returned

/-- Run the actual compiled Reingold controller through the recurrent 74-bank
raw Cayley reader. The reader may begin at any legal raw input position. Native
scratch starts blank only within the charged interval and returns unchanged. -/
private theorem latchBit {D : SearchTransducer} {word : List Bool} {B k : ℕ}
    {start finish : D.Config} (prior : List Bool) (answer : Bool)
    (segment : D.BoundedSegment word B start finish k) (halt : D.step word finish = none)
    (out : finish.outputReversed = [answer]) :
    let L := LatchedVerdict.machine D
    ∃ d : L.Config,
      L.BoundedSegment word B (LatchedVerdict.lift D start prior) d k ∧
      L.step word d = none ∧ (LatchedVerdict.state D d).getD false = answer ∧
      d.outputReversed = prior ∧ d.workHead = finish.workHead ∧ d.workCell = finish.workCell := by
  obtain ⟨run,stop,bit,printed⟩ := LatchedVerdict.execute D (prior := prior) segment halt
  refine ⟨_,run,stop,?_,printed,rfl,rfl⟩
  rw [bit,out]
  rfl

open scoped Classical in
private theorem decisionEq {n : ℕ} (G : Group (Fin n)) (x : Fin n) :
    decide (x ∈ @Subgroup.closure (Fin n) G (seed (fun _ => true) x.val)) = prefixVerdict G x := by
  apply Bool.eq_iff_iff.mpr
  have semantic := BipartiteCayley.rawPrefixQuery_correct G (fun _ => true) x.val x
  exact ⟨fun h => semantic.mpr (of_decide_eq_true h),fun h => decide_eq_true (semantic.mp h)⟩

private theorem startingFields (M : SearchTransducer) (R : Callback)
    (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
    (B : ℕ) (c : (callMachine M R e).Config) :
    let origin := nativeStart M R e B c
    let start := readStart M R e c
    origin.inputHead = 0 ∧ origin.workHead = (fun _ => 0) ∧ origin.outputReversed = [] ∧
    start.state = R.read.initialState ∧ start.inputHead = c.inputHead ∧
    start.workHead = c.workHead ∧ start.workCell = c.workCell ∧ start.outputReversed = [] :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem startingCells (M : SearchTransducer) (R : Callback)
    (e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes)
    (B : ℕ) (c : (callMachine M R e).Config)
    (blank : ∀ (i : Fin M.workTapes) (p : Int), p.natAbs ≤ B → c.workCell (e i.castSucc) p = none) :
    ∀ i, (nativeStart M R e B c).workCell i = c.workCell (e i.castSucc) := by
  intro i
  funext p
  change (if p.natAbs ≤ B then none else c.workCell (e i.castSucc) p) = _
  by_cases h : p.natAbs ≤ B
  · rw [if_pos h, blank i p h]
  · rw [if_neg h]

private theorem readyAtOrigin {M : SearchTransducer} {n : ℕ}
    (G : Group (Fin n)) (x : Fin n) (ticks : List Bool) (B k : ℕ)
    (c : (prefixMachine M).Config) (heads : c.workHead = fun _ => 0)
    (input : (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (@encodeCayley n G.toMul).length)
    (blank : ∀ i p, p.natAbs ≤ B → c.workCell (nativeBank M i) p = none)
    (cycle : CayleyReaderCycle.Ready G x.val (BipartiteCayley.left G.toOne.one)
      (BipartiteCayley.left x) 1 ticks (fun i => c.workCell (readerBank M i))) :
    let origin := nativeStart M (callback M) (playbackBanks M) B c
    let start := readStart M (callback M) (playbackBanks M) c
    Ready G x ticks B origin k origin start ∧
      ∀ i, origin.workCell i = c.workCell (nativeBank M i) := by
  let R := callback M
  let e := playbackBanks M
  let origin := nativeStart M R e B c
  let start := readStart M R e c
  obtain ⟨nativePos,nativeHeads,nativeOut,initial,real,readerHeads,readerCells,readerOut⟩ :=
    startingFields M R e B c
  have nativeBlank (i : Fin M.workTapes) (p : Int) (h : p.natAbs ≤ B) :
      c.workCell (e i.castSucc) p = none := by
    rw [playbackNative]
    exact blank i p h
  have cells (i : Fin M.workTapes) : origin.workCell i = c.workCell (nativeBank M i) := by
    rw [← playbackNative]
    exact startingCells M R e B c nativeBlank i
  have shift : (origin.inputHead + 1).toNat = 1 := by
    rw [nativePos]
    rfl
  refine ⟨⟨⟨0,Nat.zero_le _,rfl⟩,initial,?_,readerOut.trans nativeOut.symm,?_,?_,?_,?_⟩,cells⟩
  · rw [real]
    exact input
  · intro i
    exact (congrFun (readerHeads.trans heads) _)
  · intro i
    exact (congrFun (readerHeads.trans heads) _).trans (congrFun nativeHeads i).symm
  · intro i
    exact (congrFun readerCells _).trans (cells i).symm
  · change CayleyReaderCycle.Ready G x.val (BipartiteCayley.left G.toOne.one)
      (BipartiteCayley.left x) (origin.inputHead+1).toNat ticks
      (fun i => start.workCell (readerBank M i))
    rw [shift,readerCells]
    exact cycle

private theorem executeCertified (M : SearchTransducer) (K : ℕ)
    (certificate : WindowCertificate M K) :
    ∀ {n : ℕ} (G : Group (Fin n)) (x : Fin n)
      (ticks : List Bool) (B : ℕ),
      let word := @encodeCayley n G.toMul
      let P := prefixMachine M
      K * (Nat.log2 (word.length + 1) + 1) ≤ B →
      ticks.length+1 ≤ B → width n+1 ≤ B →
      ∀ (c : P.Config), c.state = P.initialState → c.workHead = (fun _ => 0) →
        (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ word.length →
        (∀ i p, p.natAbs ≤ B → c.workCell (nativeBank M i) p = none) →
        CayleyReaderCycle.Ready G x.val (BipartiteCayley.left G.toOne.one)
          (BipartiteCayley.left x) 1 ticks (fun i => c.workCell (readerBank M i)) →
        ∃ (len : ℕ) (d : P.Config), P.BoundedSegment word B c d len ∧ P.step word d = none ∧
          prefixBit M d.state = prefixVerdict G x ∧ d.outputReversed = c.outputReversed ∧
          d.workHead = (fun _ => 0) ∧
          (∀ i, d.workCell (nativeBank M i) = c.workCell (nativeBank M i)) ∧
          CayleyReaderCycle.Ready G x.val (BipartiteCayley.left G.toOne.one)
            (BipartiteCayley.left x) 1 ticks (fun i => d.workCell (readerBank M i)) := by
  classical
  intro n G x ticks B word P budget clockBound window c state heads input blank cycle
  let R := callback M
  let e := playbackBanks M
  let origin := nativeStart M R e B c
  let start := readStart M R e c
  obtain ⟨k,terminal,run,halt,out,space,nativePos,nativeHeads,nativeTapes⟩ :=
    certificate G (fun _ => true) x.val x (fun i => c.workCell (e i.castSucc)) B budget
  obtain ⟨init,startCells⟩ := readyAtOrigin G x ticks B k c heads input blank cycle
  obtain ⟨len,last,physical,stop,printed,parked,saved,restored⟩ :=
    finishReader G x ticks B origin terminal k run halt space clockBound window
      nativePos nativeHeads start init
  have unwrapped := initialLayout M R e B c state
  have actualOutput : last.outputReversed = [prefixVerdict G x] := by
    rw [printed,out,decisionEq]
  obtain ⟨d,segment,done,bit,output,dHeads,dCells⟩ :=
    latchBit c.outputReversed (prefixVerdict G x) physical stop actualOutput
  rw [unwrapped] at segment
  refine ⟨len,d,segment,done,bit,output,dHeads.trans parked,?_,?_⟩
  · intro i
    exact (congrFun dCells _).trans ((saved i).trans ((congrFun nativeTapes i).trans (startCells i)))
  · rw [dCells]
    exact restored

theorem executePrepared :
    ∃ (M : SearchTransducer) (K : ℕ), ∀ {n : ℕ} (G : Group (Fin n)) (x : Fin n)
      (ticks : List Bool) (B : ℕ),
      let word := @encodeCayley n G.toMul
      let P := prefixMachine M
      K * (Nat.log2 (word.length + 1) + 1) ≤ B →
      ticks.length+1 ≤ B → width n+1 ≤ B →
      ∀ (c : P.Config), c.state = P.initialState → c.workHead = (fun _ => 0) →
        (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ word.length →
        (∀ i p, p.natAbs ≤ B → c.workCell (nativeBank M i) p = none) →
        CayleyReaderCycle.Ready G x.val (BipartiteCayley.left G.toOne.one)
          (BipartiteCayley.left x) 1 ticks (fun i => c.workCell (readerBank M i)) →
        ∃ (len : ℕ) (d : P.Config), P.BoundedSegment word B c d len ∧ P.step word d = none ∧
          prefixBit M d.state = prefixVerdict G x ∧ d.outputReversed = c.outputReversed ∧
          d.workHead = (fun _ => 0) ∧
          (∀ i, d.workCell (nativeBank M i) = c.workCell (nativeBank M i)) ∧
          CayleyReaderCycle.Ready G x.val (BipartiteCayley.left G.toOne.one)
            (BipartiteCayley.left x) 1 ticks (fun i => d.workCell (readerBank M i)) := by
  obtain ⟨M,K,certificate⟩ := nativePrefixWindowRun
  exact ⟨M,K,executeCertified M K certificate⟩
end Mathproof.MinimumGeneration.NativePhysicalReader
