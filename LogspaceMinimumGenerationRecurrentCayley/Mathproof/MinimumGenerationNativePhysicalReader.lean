import Mathproof.MinimumGenerationNativePhysicalReaderLayout

namespace Mathproof.MinimumGeneration.NativePhysicalReader

open SearchTransducer VirtualCallbackDriver ReingoldLiveInput
open NativeBipartiteReingold (instanceOf inputCells)
open InputPosition (work)
open VirtualTapeStep (routed routedReady pointerBank)
open CayleyQueryPrefixModel (width rawSpace)
open Cslib.Complexity

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

private theorem cfgEq {R : SearchTransducer} (c d : R.Config)
    (s : c.state = d.state) (i : c.inputHead = d.inputHead)
    (h : c.workHead = d.workHead) (z : c.workCell = d.workCell)
    (o : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem readerBank_cases (M : SearchTransducer) (j : Fin (74 + M.workTapes)) :
    (∃ i, readerBank M i = j) ∨ ∃ i, nativeBank M i = j := by
  refine Fin.addCases (fun i => .inl ⟨i,rfl⟩) (fun i => .inr ⟨i,rfl⟩) j

private theorem scannedBlock (w p : ℕ) :
    TapeArithmetic.block (work (encodeLabel w p)) 1 (encodeLabel w p) := by
  intro i
  have hp : ¬ (1 + (i.val : Int) ≤ 0) := by omega
  simp [work, hp, List.getElem?_eq_getElem i.isLt]

private theorem blankExterior (w p : ℕ) :
    ∀ j, j ≤ 0 ∨ (w : Int) < j → work (encodeLabel w p) j = none := by
  intro j h
  rcases h with h | h
  · exact if_pos h
  · rw [work, if_neg (by omega)]
    apply List.getElem?_eq_none
    rw [length_encodeLabel]
    omega

variable {M : SearchTransducer} {n : ℕ} (G : Group (Fin n)) (x : Fin n) (ticks : List Bool)

private abbrev raw := @encodeCayley n G.toMul
private abbrev source := inputCells G (fun _ => true) x.val x
private abbrev s := BipartiteCayley.left G.toOne.one
private abbrev t := BipartiteCayley.left x

/-- Recurrent call state for the physical reader and disjoint native banks. -/
structure Ready (B : ℕ) (origin : M.Config) (k : ℕ)
    (native : M.Config) (start : (callback M).read.Config) : Prop where
  reached : ∃ j, j ≤ k ∧ callbackRun M (source G x) origin j = some native
  state : start.state = (callback M).read.initialState
  input : (-1 : Int) ≤ start.inputHead ∧ start.inputHead ≤ (raw G).length
  output : start.outputReversed = native.outputReversed
  readerHeads : ∀ i, start.workHead (readerBank M i) = 0
  nativeHeads : ∀ i, start.workHead (nativeBank M i) = native.workHead i
  nativeCells : ∀ i, start.workCell (nativeBank M i) = native.workCell i
  reader : CayleyReaderCycle.Ready G x.val (s G) (t x) (native.inputHead+1).toNat ticks
    (fun i => start.workCell (readerBank M i))

private theorem legalAddress (native : M.Config)
    (lo : (-1 : Int) ≤ native.inputHead)
    (hi : native.inputHead ≤ (encUSTCON (instanceOf G (fun _ => true) x.val x)).length) :
    (native.inputHead+1).toNat ≤ Connectivity.ustconHeaderLength (s G) (t x)+(n+n)*(n+n)+1 := by
  rw [NativeReingoldCayley.encode_eq, Connectivity.ustconWord_length] at hi
  change native.inputHead ≤ ((Connectivity.ustconHeaderLength (s G) (t x)+(n+n)*(n+n) : ℕ) : Int) at hi
  omega

private theorem cellMatch (native : M.Config) (lo : (-1 : Int) ≤ native.inputHead) :
    Connectivity.ustconCell (BipartiteCayley.bits G (fun _ => true) x.val) (s G) (t x)
      (((native.inputHead+1).toNat : Int)-1) = source G x native.inputHead := by
  have p : (((native.inputHead+1).toNat : ℕ) : Int)-1 = native.inputHead := by omega
  rw [p]
  unfold source inputCells
  have hb : BipartiteCayley.rawBits (raw G) G.toOne.one (fun _ => true) x.val =
      BipartiteCayley.bits G (fun _ => true) x.val := by
    funext i j
    exact BipartiteCayley.rawBits_correct G (fun _ => true) x.val i j
  change _ = Connectivity.ustconCell
    (BipartiteCayley.rawBits (raw G) G.toOne.one (fun _ => true) x.val) (s G) (t x) native.inputHead
  rw [hb]

/-- One actual call of the complete physical recurrent cell program. The
returned tape layout is exact, and the native banks are preserved. -/
theorem executeCell {B : ℕ} {origin native : M.Config} {k : ℕ} {start : (callback M).read.Config}
    (h : Ready G x ticks B origin k native start)
    (nlo : (-1 : Int) ≤ native.inputHead)
    (nhi : native.inputHead ≤ (encUSTCON (instanceOf G (fun _ => true) x.val x)).length)
    (nativeBound : ∀ i, (native.workHead i).natAbs ≤ B) (clockBound : ticks.length + 1 ≤ B) :
    ∃ (a : ℕ) (result : (callback M).read.Config),
      (callback M).read.BoundedSegment (raw G) B start result a ∧
      (callback M).read.step (raw G) result = none ∧
      (callback M).returnCell result.state = source G x native.inputHead ∧
      result.outputReversed = native.outputReversed ∧
      (-1 : Int) ≤ result.inputHead ∧ result.inputHead ≤ (raw G).length ∧
      (∀ i, result.workHead (readerBank M i) = 0) ∧
      (∀ i, result.workHead (nativeBank M i) = native.workHead i) ∧
      (∀ i, result.workCell (nativeBank M i) = native.workCell i) ∧
      CayleyReaderCycle.Ready G x.val (s G) (t x) (native.inputHead+1).toNat ticks
        (fun i => result.workCell (readerBank M i)) := by
  let p := (native.inputHead+1).toNat
  let old := fun i => start.workCell (readerBank M i)
  let P := CayleyReaderCycle.machine
  let initial := CayleyReaderCycle.start start.inputHead start.outputReversed old
  obtain ⟨a,d,read,done,answer,out,heads,lo,hi,cycle⟩ :=
    CayleyReaderCycle.execute G x.val x.isLt.le (s G) (t x) p start.outputReversed
      ticks start.inputHead old h.reader h.input (legalAddress G x native nlo nhi)
  let result := P.bankConfig (readerBank M) d start.workHead start.workCell
  have given : P.bankConfig (readerBank M) initial start.workHead start.workCell = start := by
    have q := CayleyReaderCycle.startSpec start.inputHead start.outputReversed old
    apply cfgEq
    · exact q.1.trans h.state.symm
    · exact q.2.1
    · funext l
      by_cases img : l ∈ Set.range (readerBank M)
      · obtain ⟨i,rfl⟩ := img
        exact (P.bankConfig_head_image _ _ _ _ i).trans ((q.2.2.2.1 i).trans (h.readerHeads i).symm)
      · exact (P.bankConfig_frame _ _ _ _ img).1
    · funext l
      by_cases img : l ∈ Set.range (readerBank M)
      · obtain ⟨i,rfl⟩ := img
        exact (P.bankConfig_cell_image _ _ _ _ i).trans (congrFun q.2.2.2.2 i)
      · exact (P.bankConfig_frame _ _ _ _ img).2
    · exact q.2.2.1
  have frameBound : ∀ i ∉ Set.range (readerBank M), (start.workHead i).natAbs ≤ B := by
    intro i ni
    rcases readerBank_cases M i with ⟨r,eq⟩ | ⟨r,rfl⟩
    · exact (ni ⟨r,eq⟩).elim
    · rw [h.nativeHeads]
      exact nativeBound r
  have physical := P.relocateBanks_segment (readerBank M)
    (heads := start.workHead) (cells := start.workCell)
    (PhysicalEntry.segment_mono read clockBound) frameBound
  change ((callback M).read).BoundedSegment (raw G) B
    (P.bankConfig (readerBank M) initial start.workHead start.workCell) result a at physical
  rw [given] at physical
  have stopRead : (callback M).read.step (raw G) result = none := by
    change (P.relocateBanks (readerBank M)).step (raw G) result = none
    rw [relocateBanks_step,done]
    rfl
  have resultHeads (i : Fin 74) : result.workHead (readerBank M i) = 0 :=
    (P.bankConfig_head_image _ _ _ _ i).trans (heads i)
  have resultNativeHeads (i : Fin M.workTapes) : result.workHead (nativeBank M i) = native.workHead i :=
    (P.bankConfig_frame _ _ _ _ (native_not_reader M i)).1.trans (h.nativeHeads i)
  have resultNativeCells (i : Fin M.workTapes) : result.workCell (nativeBank M i) = native.workCell i :=
    (P.bankConfig_frame _ _ _ _ (native_not_reader M i)).2.trans (h.nativeCells i)
  have resultCycle : CayleyReaderCycle.Ready G x.val (s G) (t x) p ticks
      (fun i => result.workCell (readerBank M i)) := by
    have eq : (fun i => result.workCell (readerBank M i)) = d.workCell := by
      funext i
      exact P.bankConfig_cell_image _ _ _ _ i
    rwa [eq]
  exact ⟨a,result,physical,stopRead,answer.trans (cellMatch G x native nlo),
    out.trans h.output,lo,hi,resultHeads,resultNativeHeads,resultNativeCells,resultCycle⟩

/-- Actual reset, table lookup and parked read along a certified native run. -/
def contract (B : ℕ) (origin terminal : M.Config) (k : ℕ)
    (run : callbackRun M (source G x) origin k = some terminal)
    (halt : callbackStep M (source G x) terminal = none)
    (space : ∀ j c, j ≤ k → callbackRun M (source G x) origin j = some c →
      (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤
        (encUSTCON (instanceOf G (fun _ => true) x.val x)).length ∧
      ∀ i, (c.workHead i).natAbs ≤ B)
    (clockBound : ticks.length+1 ≤ B) (window : width n+1 ≤ B) :
    FramedReaderContract M (callback M) (playbackBanks M) (raw G) (source G x) B (width n) where
  ready := Ready G x ticks B origin k
  windowBase := 0
  window := by intro j lo hi; omega
  call := by
    intro native start h
    obtain ⟨j,hj,reached⟩ := h.reached
    obtain ⟨nlo,nhi,nativeBound⟩ := space j native hj reached
    let p := (native.inputHead+1).toNat
    obtain ⟨a,result,physical,stopRead,returned,out,lo,hi,resultHeads,
      resultNativeHeads,resultNativeCells,resultCycle⟩ :=
      executeCell G x ticks h nlo nhi nativeBound clockBound
    let pointer := result.workCell (readerBank M address)
    have pointerExact : pointer = work (encodeLabel (width n) p) :=
      pointer_of_ready (old := fun i => result.workCell (readerBank M i)) resultCycle
    have output : native.outputReversed = result.outputReversed := out.symm
    have aligned : acceptCell M (callback M) (playbackBanks M) native.state result =
        (routed M).bankConfig (playbackBanks M)
          (routedReady M native ((callback M).returnCell result.state) result.inputHead 0 pointer)
          result.workHead result.workCell := by
      apply cfgEq
      · rfl
      · rfl
      · funext i
        by_cases im : i ∈ Set.range (playbackBanks M)
        · obtain ⟨v,rfl⟩ := im
          rw [bankConfig_head_image]
          refine Fin.lastCases ?_ (fun q => ?_) v
          · rw [show Fin.last M.workTapes = pointerBank M from rfl]
            simp only [acceptCell, VirtualTapeStep.routedReady_pointerHead]
            change result.workHead (playbackBanks M (pointerBank M)) = 0
            rw [playbackPointer]
            exact resultHeads address
          · simp only [acceptCell, VirtualTapeStep.routedReady_nativeHead]
            change result.workHead (playbackBanks M q.castSucc) = native.workHead q
            rw [playbackNative]
            exact resultNativeHeads q
        · exact ((routed M).bankConfig_frame _ _ _ _ im).1.symm
      · funext i
        by_cases im : i ∈ Set.range (playbackBanks M)
        · obtain ⟨v,rfl⟩ := im
          rw [bankConfig_cell_image]
          refine Fin.lastCases ?_ (fun q => ?_) v
          · rw [show Fin.last M.workTapes = pointerBank M from rfl]
            simp only [acceptCell, VirtualTapeStep.routedReady_pointerCell]
            change result.workCell (playbackBanks M (pointerBank M)) = pointer
            rw [playbackPointer]
          · simp only [acceptCell, VirtualTapeStep.routedReady_nativeCell]
            change result.workCell (playbackBanks M q.castSucc) = native.workCell q
            rw [playbackNative]
            exact resultNativeCells q
        · exact ((routed M).bankConfig_frame _ _ _ _ im).2.symm
      · exact output.symm
    have stepTrace (next : M.Config) (step : callbackStep M (source G x) native = some next) :
        j+1 ≤ k ∧ callbackRun M (source G x) origin (j+1) = some next := by
      refine ⟨?_,?_⟩
      · by_contra! eq
        have same : j = k := by omega
        rw [same,run] at reached
        have sameConfig := Option.some.inj reached
        rw [← sameConfig,halt] at step
        cases step
      · rw [callbackRun,reached,Option.bind_some,step]
    refine ⟨a,result,result.inputHead,pointer,physical,stopRead,returned,output,?_,?_,?_,
      aligned,lo,hi,nativeBound,nlo,?_,?_⟩
    · rw [pointerExact]
      exact blankExterior (width n) p 0 (.inl le_rfl)
    · rw [pointerExact]
      simpa only [zero_add] using blankExterior (width n) p ((width n : Int)+1) (.inr (by omega))
    · simpa only [zero_add,pointerExact] using scannedBlock (width n) p
    · intro next step
      have pr := stepTrace next step
      have b := space (j+1) next pr.1 pr.2
      exact ⟨b.1,b.2.2⟩
    · intro next nextOut atAddress exterior nativeStep
      let tagged := (routed M).bankConfig (playbackBanks M) nextOut result.workHead result.workCell
      let requested := requestCell M (callback M) (playbackBanks M) tagged
      have ptrBlank : ∀ z, z ≤ 0 ∨ (width n : Int) < z → pointer z = none := by
        rw [pointerExact]
        exact blankExterior (width n) p
      have newPointer := atAddress.pointer_eq_work exterior ptrBlank
      have unchanged (i : Fin 74) (ne : i ≠ address) :
          requested.workCell (readerBank M i) = result.workCell (readerBank M i) :=
        ((routed M).bankConfig_frame (playbackBanks M) nextOut result.workHead result.workCell (reader_not_playback M i ne)).2
      have newAddress : requested.workCell (readerBank M address) =
          work (encodeLabel (width n) (next.inputHead+1).toNat) := by
        rw [← playbackPointer M]
        exact ((routed M).bankConfig_cell_image (playbackBanks M) nextOut result.workHead result.workCell _).trans newPointer
      refine ⟨⟨j+1,(stepTrace next nativeStep).1,(stepTrace next nativeStep).2⟩,
        rfl,?_,atAddress.output,?_,?_,?_,changeAddress resultCycle unchanged newAddress⟩
      · change (-1 : Int) ≤ tagged.inputHead ∧ tagged.inputHead ≤ (raw G).length
        exact ⟨lo.trans_eq atAddress.realPosition.symm, atAddress.realPosition.trans_le hi⟩
      · intro i
        by_cases a : i = address
        · subst i
          rw [← playbackPointer M]
          exact ((routed M).bankConfig_head_image (playbackBanks M) nextOut result.workHead result.workCell _).trans atAddress.restored
        · exact ((routed M).bankConfig_frame (playbackBanks M) nextOut result.workHead result.workCell (reader_not_playback M i a)).1.trans (resultHeads i)
      · intro i
        rw [← playbackNative M i]
        exact ((routed M).bankConfig_head_image (playbackBanks M) nextOut result.workHead result.workCell _).trans (atAddress.nativeHead i)
      · intro i
        rw [← playbackNative M i]
        exact ((routed M).bankConfig_cell_image (playbackBanks M) nextOut result.workHead result.workCell _).trans (atAddress.nativeTape i)

end Mathproof.MinimumGeneration.NativePhysicalReader
