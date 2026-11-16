import Mathproof.MinimumGenerationPhysicalGreedyFirstOrdinal
import Mathproof.MinimumGenerationPhysicalGreedyNativeLeaf
import Mathproof.MinimumGenerationNativePhysicalPrefix

namespace Mathproof.MinimumGeneration.PhysicalGreedyNativeOrdinal

open SearchTransducer
open PhysicalGreedyNativeLeaf (Ready Core call room stageBanks nativeBanks memory)
open CayleyReaderCandidate (readerView headerView)
open PhysicalGreedyOrdinalSetup (Bank label order ordinal zero prepared)
open PhysicalGreedyHeaderInstall (wordAt)
open PhysicalGreedyTape (kept)
open PhysicalGreedyTemplateCompose (configEq)
open NativePhysicalReader (nativeBank)
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private abbrev W (M : SearchTransducer) := PhysicalGreedyNativeLeaf.W M

theorem initialReady (M : SearchTransducer) {n : Nat} (G : Group (Fin n)) (B : Nat) :
    Ready M G (CayleyReaderClock.bits n) B (prepared M.workTapes n G.toOne.one.val) := by
  let m := prepared M.workTapes n G.toOne.one.val
  have r : PhysicalGreedyCycleInvariant.Ready G (CayleyReaderClock.bits n) B
      (PhysicalGreedyOrdinalSetup.reader M.workTapes)
      (PhysicalGreedyOrdinalSetup.native M.workTapes) m :=
    PhysicalGreedyOrdinalSetup.stateInitialized G M.workTapes B
  have frame (j : PhysicalGreedyHeaderInstall.Bank) :
      headerView (memory M m) j = PhysicalGreedyTemplateSetup.outputData n G.toOne.one.val 0
        (PhysicalGreedyTemplateSetup.checkoutBanks j) := by
    let i := PhysicalGreedyTemplateSetup.checkoutBanks j
    have h : stageBanks M (CayleyReaderCandidate.header j) =
      PhysicalGreedyOrdinalSetup.header M.workTapes i := Fin.ext rfl
    change m (stageBanks M (CayleyReaderCandidate.header j)) = _
    rw [h]
    exact (PhysicalGreedyOrdinalSetup.prepared_image M.workTapes n G.toOne.one.val
      (PhysicalGreedyReaderSetup.header i)).trans (PhysicalGreedyReaderSetup.header_preserved n _ i)
  have header := PhysicalGreedyTemplateSetup.output_ready n G.toOne.one.val 0
  refine ⟨?_,?_,(frame 2).trans header.rawIdentity,
    fun j => (frame _).trans (header.constants j),?_⟩
  · obtain ⟨c,x,p,_,_,h⟩ := r.1
    exact ⟨c,x,p,h⟩
  · intro i p h
    have eq : nativeBanks M (nativeBank M i) = PhysicalGreedyOrdinalSetup.native M.workTapes i :=
      Fin.ext (PhysicalGreedyNativeLeaf.nativeBanks_write M i)
    rw [eq]
    exact r.2 i p h
  · intro j hj
    rw [frame]
    exact header.scratch j hj

theorem stable (M : SearchTransducer) {n B : Nat} (G : Group (Fin n)) (ticks : List Bool)
    (bank : Bank M.workTapes) (which : bank.val = 75 ∨ bank.val = 93) :
    GreedyTapeScanInvariant.Stable bank (Ready M G ticks B) := by
  intro old new frame R
  have r (i : Fin 74) : readerView (memory M new) i = readerView (memory M old) i := by
    apply frame
    intro same
    have e := congrArg Fin.val same
    change i.val = bank.val at e
    have := i.isLt
    omega
  have c (i : PhysicalGreedyHeaderInstall.Bank) (hi : 2 ≤ i.val) :
      headerView (memory M new) i = headerView (memory M old) i := by
    apply frame
    intro same
    have e := congrArg Fin.val same
    change 74+i.val = bank.val at e
    have h := i.isLt
    change i.val < 17 at h
    omega
  refine ⟨?_,?_,(c 2 (by decide)).trans R.headerId,?_,?_⟩
  · have eq : readerView (memory M new) = readerView (memory M old) := funext r
    rw [eq]
    exact R.reader
  · intro i p hp
    have neq : nativeBanks M (nativeBank M i) ≠ bank := fun same => by
      have e := congrArg Fin.val same
      rw [PhysicalGreedyNativeLeaf.nativeBanks_write] at e
      omega
    rw [frame _ neq]
    exact R.native i p hp
  · intro i
    have hi : 2 ≤ (PhysicalGreedyHeaderInstall.constBank i).val := by change 2≤3+i.val; omega
    exact (c _ hi).trans (R.headerConstants i)
  · intro i hi
    rw [c i (by omega)]
    exact R.headerScratch i hi

private theorem entryLayout (M : SearchTransducer) (p : Int) (prior : List Bool)
    (m : Fin (W M) → Int → Option Bool) :
    let a := PhysicalGreedyNativeLeaf.entry M p prior m
    a.state = (PhysicalGreedyNativeLeaf.machine M).initialState ∧
      a.inputHead=p ∧ a.workHead=(fun _ => 0) ∧ a.workCell=m ∧ a.outputReversed=prior := by
  let D := PhysicalGreedyNativeLeaf.D
  let f := stageBanks M
  let c := PhysicalGreedyTemplateCompose.cfg CayleyReaderRetarget.machine D.initialState p prior (memory M m)
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · funext j
    by_cases h : j ∈ Set.range f
    · obtain ⟨i,rfl⟩ := h
      exact D.bankConfig_head_image f c (fun _ => 0) m i
    · exact (D.bankConfig_frame f c (fun _ => 0) m h).1
  · funext j
    by_cases h : j ∈ Set.range f
    · obtain ⟨i,rfl⟩ := h
      exact D.bankConfig_cell_image f c (fun _ => 0) m i
    · exact (D.bankConfig_frame f c (fun _ => 0) m h).2

abbrev allowed (M : SearchTransducer) := PhysicalGreedyRaw.allowAll (W := W M) (room M)

abbrev rawQuery {n : Nat} (G : Group (Fin n)) :=
  RawGreedyMembership.query (@encodeCayley n G.toMul) G.toOne.one

/-- Turn the concrete recurrent native prefix execution into the single
candidate membership leaf. The changing reader workspace is the invariant,
while the ordinal and zero registers are physically protected. -/
theorem leaf (M : SearchTransducer) {n B : Nat} (G : Group (Fin n)) (ticks : List Bool)
    (budget : ticks.length+1 ≤ B) (core : ∀ x : Fin n, Core M G x ticks B) :
    GreedyTapeScanInvariant.Leaf (label M.workTapes) (order M.workTapes) (room M)
      (allowed M) (call M) (B := B) (@encodeCayley n G.toMul) 2
      (fun x => rawQuery G (GreedyGenerator.before (fun _ => true) x.val) x) (call M).answer
      (kept ∅ (ordinal M.workTapes) (zero M.workTapes)) (Ready M G ticks B) := by
  intro x c hEntry preparation hInv
  obtain ⟨k,d,result⟩ :=
    PhysicalGreedyNativeLeaf.execute G x ticks B budget (core x) c.inputHead c.outputReversed
      c.workCell ⟨preparation.inputLo,preparation.inputHi⟩ hInv preparation.order preparation.cursor
  obtain ⟨run,halt,answer,output,heads,ready,headers,ordinals⟩ := result
  have layout := entryLayout M c.inputHead c.outputReversed c.workCell
  have start : PhysicalGreedyNativeLeaf.entry M c.inputHead c.outputReversed c.workCell = c :=
    configEq _ _ (layout.1.trans hEntry.symm) layout.2.1
      (layout.2.2.1.trans preparation.heads.symm) layout.2.2.2.1 layout.2.2.2.2
  rw [start] at run
  have bound := run.2 k le_rfl d run.1
  refine ⟨k,d,run,halt,?_,⟨bound.1,bound.2.1,heads,
    (headers 1 (by decide)).trans preparation.cursor,
    (headers 0 (by decide)).trans preparation.order⟩,output,ready,?_⟩
  · rw [answer]
    exact BipartiteCayley.rawPrefixQuery_eq_ordinary G (fun _ => true) x.val x
  · intro j hj
    change j ∈ (∅ : Set (Bank M.workTapes)) ∨ j = ordinal M.workTapes ∨ j = zero M.workTapes at hj
    rcases hj with h | rfl | rfl
    · exact h.elim
    · exact ordinals _ (by change 93≤93; decide) (by change 93<95; decide)
    · exact ordinals _ (by change 93≤94; decide) (by change 94<95; decide)

/-- Compute any physically requested ordinal through the full invariant-
preserving recurrent controller, keeping its state ready for another call. -/
theorem executeOrdinal (M : SearchTransducer) {n B : Nat} (G : Group (Fin n)) (ticks : List Bool)
    (budget : ticks.length+1 ≤ B) (core : ∀ x : Fin n, Core M G x ticks B)
    (source : Bank M.workTapes) (m : Bank M.workTapes → Int → Option Bool)
    (k i : Nat) (fits : i < 2^TableIO.width n) {p : Int} {prior : List Bool}
    (orderWord : m (order M.workTapes) = wordAt (TableIO.width n) n)
    (labelWord : m (label M.workTapes) = wordAt (TableIO.width n) k)
    (requestWord : m source = wordAt (TableIO.width n) i)
    (zeroWord : m (zero M.workTapes) = wordAt (TableIO.width n) 0)
    (oldWord : ∃ j, m (ordinal M.workTapes) = wordAt (TableIO.width n) j)
    (legal : (-1 : Int) ≤ p ∧ p ≤ (@encodeCayley n G.toMul).length)
    (fit : TableIO.width n+1 ≤ B) (ready : Ready M G ticks B m) :
    let R := PhysicalGreedyOrdinalRequested.machine (room M) (allowed M) (call M) source
    let raw := @encodeCayley n G.toMul
    let expected := (GreedyOrdinal.collect (GreedyGenerator.accept (rawQuery G) (fun _ => true)) 0 n)[i]?
    ∃ (len : Nat) (d : R.Config),
      R.BoundedSegment raw B (PhysicalGreedyOrdinalRequested.entry (room M) (allowed M) (call M)
        source p prior m) d len ∧ R.step raw d = none ∧
      PhysicalGreedyOrdinalRequested.returned (room M) (allowed M) (call M) source d = expected.isSome ∧
      d.workCell (label M.workTapes) = wordAt (TableIO.width n) (expected.elim n Fin.val) ∧
      d.workHead = (fun _ => 0) ∧ d.outputReversed = prior ∧ Ready M G ticks B d.workCell ∧
      (∃ rem, d.workCell (ordinal M.workTapes) = wordAt (TableIO.width n) rem) ∧
      d.workCell (zero M.workTapes) = wordAt (TableIO.width n) 0 ∧
      d.workCell (order M.workTapes) = wordAt (TableIO.width n) n := by
  dsimp only
  have run := PhysicalGreedyOrdinalRequested.executeWithRegisters (room M) (allowed M) (call M)
    (prior := prior) (rawQuery G) (fun _ => true) ∅ (Ready M G ticks B)
    (stable M G ticks (label M.workTapes) (.inl rfl))
    (stable M G ticks (ordinal M.workTapes) (.inr rfl))
    (by simp) (by simp)
    (PhysicalGreedyCycleInvariant.allowAll _ _ (room M) (call M) _ _)
    (leaf M G ticks budget core) source m k i fits orderWord labelWord requestWord zeroWord
    oldWord legal fit ready
  obtain ⟨l,d,steps,stop,answer,word,head,out,last,indexOut,zeroOut,orderOut,_⟩ := run
  rw [GreedyOrdinal.ordinal_exact] at answer word
  exact ⟨l,d,steps,stop,answer,word,head,out,last,indexOut,zeroOut,orderOut⟩

/-- A fixed native prefix machine and one logarithmic space factor. -/
abbrev CoreFamily (M : SearchTransducer) (K : Nat) : Prop :=
    ∀ {n : Nat} (G : Group (Fin n)) (x : Fin n) (ticks : List Bool) (B : Nat),
    K * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1) ≤ B →
    ticks.length + 1 ≤ B → CayleyQueryPrefixModel.width n + 1 ≤ B →
    PhysicalGreedyNativeLeaf.Core M G x ticks B

/-- Choose one finite native prefix controller uniformly for all valid Cayley inputs. -/
theorem existsCore : ∃ (M : SearchTransducer) (K : Nat), CoreFamily M K := by
  obtain ⟨M,K,run⟩ := NativePhysicalReader.executePrepared
  exact ⟨M,K,fun G x ticks B size clock width => run G x ticks B size clock width⟩


private theorem clockBound {n : Nat} (G : Group (Fin n)) :
    (CayleyReaderClock.bits n).length+1 ≤ 17*(Nat.log2 ((@encodeCayley n G.toMul).length+1)+1) := by
  let raw := @encodeCayley n G.toMul
  let L := Nat.log2 (raw.length+1)+1
  have ln : n ≤ raw.length := by
    change n ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have ll : n.log2 ≤ (raw.length+1).log2 :=
    (Nat.le_log2 (by omega)).2
      ((Nat.log2_self_le (by have := G.toOne.one.isLt; omega)).trans (by omega))
  have lg : n.log2 + 1 ≤ L := Nat.succ_le_succ ll
  have Lpos : 1 ≤ L := Nat.succ_le_succ (Nat.zero_le _)
  change (CayleyReaderClock.bits n).length+1 ≤ 17*L
  rw [CayleyReaderClock.bits,length_encodeLabel,TableIO.width]
  omega

/-- Blank-start execution on the raw Cayley input, retaining the live request and reader banks. -/
abbrev FirstContract (M : SearchTransducer) (C : Nat) : Prop :=
    ∀ {n : Nat} (G : Group (Fin n)),
      let raw := @encodeCayley n G.toMul
      let B := C*(Nat.log2 (raw.length+1)+1)
      let P := PhysicalGreedyFirstOrdinal.machine (room M) (allowed M) (call M)
      let expected := (GreedyOrdinal.collect (GreedyGenerator.accept (rawQuery G) (fun _ => true)) 0 n)[0]?
      ∃ (len : Nat) (d : P.Config), P.BoundedSegment raw B P.initial d len ∧
        P.step raw d = none ∧ P.logarithmicWorkspace C raw ∧
        PhysicalGreedyFirstOrdinal.returned (room M) (allowed M) (call M) d = expected.isSome ∧
        d.workCell (label M.workTapes) = wordAt (TableIO.width n) (expected.elim n Fin.val) ∧
        d.workHead = (fun _ => 0) ∧ d.outputReversed = [] ∧
        Ready M G (CayleyReaderClock.bits n) B d.workCell ∧
        (∃ i, d.workCell (ordinal M.workTapes) = wordAt (TableIO.width n) i) ∧
        d.workCell (zero M.workTapes) = wordAt (TableIO.width n) 0 ∧
        d.workCell (order M.workTapes) = wordAt (TableIO.width n) n

private theorem firstWithCore (M : SearchTransducer) (K : Nat) (run : CoreFamily M K) :
    FirstContract M (max 17 K) := by
  let C := max 17 K
  intro n G
  let raw := @encodeCayley n G.toMul
  let L := Nat.log2 (raw.length+1)+1
  let B := C*L
  let ticks := CayleyReaderClock.bits n
  have cap : 17 ≤ C := le_max_left _ _
  have size : K*L ≤ B := Nat.mul_le_mul_right L (le_max_right _ _)
  have clock : ticks.length+1 ≤ B := (clockBound G).trans (Nat.mul_le_mul_right L cap)
  have width : CayleyQueryPrefixModel.width n+1 ≤ B :=
    (CayleyQueryPrefixModel.width_le G).trans
      (Nat.mul_le_mul_right L ((by decide : 5 ≤ 17).trans cap))
  exact PhysicalGreedyFirstOrdinal.execute (room M) (allowed M) (call M) G cap
    (rawQuery G) (fun _ => true) (Ready M G ticks B)
    (stable M G ticks (label M.workTapes) (.inl rfl))
    (stable M G ticks (ordinal M.workTapes) (.inr rfl))
    (initialReady M G B) (PhysicalGreedyCycleInvariant.allowAll _ _ (room M) (call M) _ _)
    (leaf M G ticks clock (fun x => run G x ticks B size clock width))

/-- Replay a raw-width ordinal on the retained layout. The finite controller's source bank is chosen at its calling site. -/
abbrev ReplayContract (M : SearchTransducer) (C : Nat) : Prop :=
    ∀ {n : Nat} (G : Group (Fin n)) (source : Bank M.workTapes)
      (m : Bank M.workTapes → Int → Option Bool) (k i : Nat) (_fits : i < 2^TableIO.width n)
      (p : Int) (prior : List Bool),
      let raw := @encodeCayley n G.toMul
      let ticks := CayleyReaderClock.bits n
      let B := C*(Nat.log2 (raw.length+1)+1)
      let P := PhysicalGreedyOrdinalRequested.machine (room M) (allowed M) (call M) source
      let expected := (GreedyOrdinal.collect (GreedyGenerator.accept (rawQuery G) (fun _ => true)) 0 n)[i]?
      m (order M.workTapes) = wordAt (TableIO.width n) n →
      m (label M.workTapes) = wordAt (TableIO.width n) k →
      m source = wordAt (TableIO.width n) i →
      m (zero M.workTapes) = wordAt (TableIO.width n) 0 →
      (∃ j, m (ordinal M.workTapes) = wordAt (TableIO.width n) j) →
      (-1 : Int) ≤ p ∧ p ≤ raw.length → Ready M G ticks B m →
      ∃ (len : Nat) (d : P.Config),
        P.BoundedSegment raw B (PhysicalGreedyOrdinalRequested.entry (room M) (allowed M) (call M)
          source p prior m) d len ∧ P.step raw d = none ∧
        PhysicalGreedyOrdinalRequested.returned (room M) (allowed M) (call M) source d = expected.isSome ∧
        d.workCell (label M.workTapes) = wordAt (TableIO.width n) (expected.elim n Fin.val) ∧
        d.workHead = (fun _ => 0) ∧ d.outputReversed = prior ∧ Ready M G ticks B d.workCell ∧
        (∃ rem, d.workCell (ordinal M.workTapes) = wordAt (TableIO.width n) rem) ∧
        d.workCell (zero M.workTapes) = wordAt (TableIO.width n) 0 ∧
        d.workCell (order M.workTapes) = wordAt (TableIO.width n) n

private theorem replayWithCore (M : SearchTransducer) (K : Nat) (run : CoreFamily M K) :
    ReplayContract M (max 17 K) := by
  let C := max 17 K
  intro n G source m k i fits p prior
  dsimp only
  intro orderWord labelWord requestWord zeroWord oldWord legal ready
  let raw := @encodeCayley n G.toMul
  let L := Nat.log2 (raw.length+1)+1
  let B := C*L
  let ticks := CayleyReaderClock.bits n
  have cap : 17 ≤ C := le_max_left _ _
  have size : K*L ≤ B := Nat.mul_le_mul_right L (le_max_right _ _)
  have clock : ticks.length+1 ≤ B := (clockBound G).trans (Nat.mul_le_mul_right L cap)
  have wide : CayleyQueryPrefixModel.width n+1 ≤ B :=
    (CayleyQueryPrefixModel.width_le G).trans (Nat.mul_le_mul_right L ((by decide : 5 ≤ 17).trans cap))
  have narrow : TableIO.width n+1 ≤ B := by
    refine (Nat.succ_le_succ ?_).trans wide
    unfold CayleyQueryPrefixModel.width
    omega
  exact executeOrdinal M G ticks clock (fun x => run G x ticks B size clock wide) source m
    k i fits (p := p) (prior := prior) orderWord labelWord requestWord zeroWord oldWord legal narrow ready


/-- Blank-start initialization and arbitrary ordinal replay use the same
finite Reingold machine, physical bank layout, and logarithmic space factor. -/
theorem existsUniformOrdinal : ∃ (M : SearchTransducer) (C : Nat),
    FirstContract M C ∧ ReplayContract M C := by
  obtain ⟨M,K,run⟩ := existsCore
  exact ⟨M,max 17 K,firstWithCore M K run,replayWithCore M K run⟩

/-- On the promised raw Cayley encoding, one finite controller finds the first
greedy generator, including the empty-list sentinel, in logarithmic workspace. -/
theorem existsFirstOrdinal : ∃ (M : SearchTransducer) (C : Nat), FirstContract M C := by
  obtain ⟨M,C,first,_⟩ := existsUniformOrdinal
  exact ⟨M,C,first⟩

/-- The same finite machine works across all group orders and requested ordinal
values, given a raw-width request and the retained initialized workspace. -/
theorem existsOrdinalReplay : ∃ (M : SearchTransducer) (C : Nat), ReplayContract M C := by
  obtain ⟨M,C,_,replay⟩ := existsUniformOrdinal
  exact ⟨M,C,replay⟩

/-- The ordered generator list whose individual entries the controller replays. -/
abbrev rawGreedy {n : Nat} (G : Group (Fin n)) : List (Fin n) :=
  GreedyOrdinal.collect (GreedyGenerator.accept (rawQuery G) (fun _ => true)) 0 n

theorem rawGreedy_generates {n : Nat} (G : Group (Fin n)) :
    @Generates (Fin n) G (rawGreedy G) := by
  have exactClosure := @GreedyOrdinal.collect_closure n G (rawQuery G)
    (RawGreedyMembership.query_correct G) (fun _ => true)
  change @Subgroup.closure (Fin n) G {x | x ∈ rawGreedy G} = ⊤
  rw [exactClosure]
  have all : {x : Fin n | (fun _ : Fin n => true) x = true} = Set.univ := by
    ext x
    simp
  rw [all]
  exact @Subgroup.closure_univ (Fin n) G

theorem rawGreedy_length {n : Nat} (G : Group (Fin n)) :
    (rawGreedy G).length ≤ Nat.log2 n :=
  @GreedyOrdinal.collect_log_length n G (rawQuery G)
    (RawGreedyMembership.query_correct G) (fun _ => true)

end Mathproof.MinimumGeneration.PhysicalGreedyNativeOrdinal
