import Mathproof.MinimumGenerationCayleyReaderRetarget
import Mathproof.MinimumGenerationNativePhysicalReader

namespace Mathproof.MinimumGeneration.PhysicalGreedyNativeLeaf

open SearchTransducer NativePhysicalReader
open PhysicalGreedyTemplateCompose (Run cfg configEq)
open CayleyReaderCandidate (readerView headerView)
open PhysicalGreedyHeaderInstall (outside outside_word)
open BipartiteCayley (left)
open GreedyTapeScan (BitCall)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000


abbrev prefixMachine (M : SearchTransducer) :=
  NativeBipartiteReingold.callMachine M (callback M) (playbackBanks M)
abbrev prefixBit (M : SearchTransducer) :=
  NativeBipartiteReingold.resultBit M (callback M) (playbackBanks M)
abbrev W (M : SearchTransducer) := 95 + M.workTapes
abbrev D := CayleyReaderRetarget.machine.native

def stageBanks (M : SearchTransducer) : Fin D.workTapes ↪ Fin (W M) :=
  ⟨Fin.castLE (by change 93 ≤ 95 + M.workTapes; omega),
    fun _ _ e => Fin.ext (congrArg (fun i : Fin (W M) => i.val) e)⟩

def nativeBanks (M : SearchTransducer) : Fin (prefixMachine M).workTapes ↪ Fin (W M) where
  toFun i := ⟨if i.val < 74 then i.val else i.val+21, by
    have hi := i.isLt
    change i.val < 74 + M.workTapes at hi
    change _ < 95 + M.workTapes
    split <;> omega⟩
  inj' i j e := by
    have h := congrArg (fun k : Fin (W M) => k.val) e
    change (if i.val < 74 then i.val else i.val+21) =
      (if j.val < 74 then j.val else j.val+21) at h
    exact Fin.ext (by split at h <;> split at h <;> omega)

theorem nativeBanks_read (M : SearchTransducer) (i : Fin 74) :
    nativeBanks M (readerBank M i) = stageBanks M (CayleyReaderCandidate.reader i) := by
  apply Fin.ext
  exact if_pos i.isLt

theorem nativeBanks_write (M : SearchTransducer) (i : Fin M.workTapes) :
    (nativeBanks M (nativeBank M i)).val = 95+i.val := by
  change (if 74+i.val < 74 then 74+i.val else 74+i.val+21) = _
  rw [if_neg (by omega)]
  omega

abbrev machine (M : SearchTransducer) := thenMachine D (prefixMachine M) (stageBanks M) (nativeBanks M)

def call (M : SearchTransducer) : BitCall (machine M).states (W M) where
  entry := (machine M).initialState
  transition := (machine M).transition
  answer q := (finSumFinEquiv.symm q).elim (fun _ => false) (prefixBit M)

abbrev width := CayleyQueryPrefixModel.width

def memory (M : SearchTransducer) (m : Fin (W M) → Int → Option Bool) (i : Fin 93) : Int → Option Bool :=
  m (stageBanks M i)

def entry (M : SearchTransducer) (input : Int) (prior : List Bool)
    (m : Fin (W M) → Int → Option Bool) : (machine M).Config :=
  thenLeft D (prefixMachine M) (stageBanks M) (nativeBanks M)
    (D.bankConfig (stageBanks M)
      (cfg CayleyReaderRetarget.machine D.initialState input prior (memory M m))
      (fun _ => 0) m)

structure Ready (M : SearchTransducer) {n : Nat} (G : Group (Fin n)) (ticks : List Bool) (B : Nat)
    (m : Fin (W M) → Int → Option Bool) : Prop where
  reader : ∃ (cut : Nat) (x : Fin n) (p : Nat),
    CayleyReaderCycle.Ready G cut (left G.toOne.one) (left x) p ticks (readerView (memory M m))
  native : ∀ (i : Fin M.workTapes) (p : Int), p.natAbs ≤ B →
    m (nativeBanks M (nativeBank M i)) p = none
  headerId : headerView (memory M m) 2 = PhysicalGreedyHeaderInstall.wordAt (TableIO.width n) G.toOne.one.val
  headerConstants : ∀ i,
    headerView (memory M m) (PhysicalGreedyHeaderInstall.constBank i) =
      PhysicalGreedyHeaderInstall.wordAt (width n) (PhysicalGreedyHeader.fixed n G.toOne.one.val i)
  headerScratch : ∀ j, 11 ≤ j.val → outside (width n) (headerView (memory M m) j)

private theorem scratchAfter {n i x : Nat} {h : PhysicalGreedyHeaderInstall.Bank → Int → Option Bool}
    (R : PhysicalGreedyHeaderInstall.Ready n i x h) (j : PhysicalGreedyHeaderInstall.Bank)
    (hj : 11 ≤ j.val) : outside (width n) (PhysicalGreedyHeaderDriver.final n i x h j) := by
  obtain ⟨u,v,w⟩ := PhysicalGreedyHeaderSums.finalMarkers (n := n) (id := i) (x := x)
    (PhysicalGreedyHeaderInstall.afterCopy n h)
  have narrow : TableIO.width n ≤ PhysicalGreedyHeader.width n := by unfold PhysicalGreedyHeader.width; omega
  intro p hp
  have low : ¬ (1 ≤ p ∧ p ≤ (PhysicalGreedyHeader.width n : Int)) := by change p < 1 ∨ (PhysicalGreedyHeader.width n : Int) < p at hp; omega
  have low' : ¬ (1 ≤ p ∧ p ≤ (TableIO.width n : Int)) := by omega
  by_cases keep : j.val ≤ 12 ∨ j.val = 16
  · unfold PhysicalGreedyHeaderDriver.final
    rw [PhysicalGreedyHeaderSums.finalFrame _ _ keep]
    simp only [PhysicalGreedyHeaderInstall.afterCopy, PhysicalGreedyHeaderInstall.afterReset,
      TapeInstall.installed, if_neg low, if_neg low']
    exact R.scratch j hj p hp
  · have e : j = 13 ∨ j = 14 ∨ j = 15 := by
      have lt := j.isLt
      change j.val < 17 at lt
      have a : j.val = 13 ∨ j.val = 14 ∨ j.val = 15 := by omega
      rcases a with a | a | a
      · exact Or.inl (Fin.ext a)
      · exact Or.inr (Or.inl (Fin.ext a))
      · exact Or.inr (Or.inr (Fin.ext a))
    unfold PhysicalGreedyHeaderDriver.final
    rcases e with rfl | rfl | rfl
    · rw [u]; exact outside_word _ _ p hp
    · rw [v]; exact outside_word _ _ p hp
    · rw [w]; exact outside_word _ _ p hp

private theorem liftedCfg (A : SearchTransducer) {W : Nat} (e : Fin A.workTapes ↪ Fin W)
    (m : Fin W → Int → Option Bool) (q : Fin A.states) (pos : Int) (out : List Bool) :
    let c : A.Config := ⟨q,pos,fun _ => 0,fun i => m (e i),out⟩
    A.bankConfig e c (fun _ => 0) m =
      ⟨q,pos,fun _ => 0,m,out⟩ := by
  dsimp only
  apply configEq
  · rfl
  · rfl
  · funext i
    by_cases h : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := h
      exact A.bankConfig_head_image e _ _ _ j
    · exact (A.bankConfig_frame e _ _ _ h).1
  · funext i
    by_cases h : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := h
      exact A.bankConfig_cell_image e _ _ _ j
    · exact (A.bankConfig_frame e _ _ _ h).2
  · rfl

private theorem after_header {M : SearchTransducer} (i : Fin (W M)) (hi : 74 ≤ i.val)
    (hj : i.val < 95) : i ∉ Set.range (nativeBanks M) := by
  rintro ⟨j,eq⟩
  have v := congrArg (fun z : Fin (W M) => z.val) eq
  change (if j.val < 74 then j.val else j.val+21) = i.val at v
  split at v <;> omega

private theorem native_out {M : SearchTransducer} (i : Fin M.workTapes) :
    nativeBanks M (nativeBank M i) ∉ Set.range (stageBanks M) := by
  rintro ⟨j,eq⟩
  have e := congrArg (fun k : Fin (W M) => k.val) eq
  rw [nativeBanks_write] at e
  change j.val = 95+i.val at e
  have hj := j.isLt
  change j.val < 93 at hj
  omega

def setStage (M : SearchTransducer) (m : Fin (W M) → Int → Option Bool)
    (updated : Fin 93 → Int → Option Bool) (j : Fin (W M)) : Int → Option Bool :=
  if h : j.val < 93 then updated ⟨j.val,h⟩ else m j

private theorem setStage_on {M : SearchTransducer} (m : Fin (W M) → Int → Option Bool)
    (v : Fin 93 → Int → Option Bool) (j : Fin 93) :
    setStage M m v (stageBanks M j) = v j := by
  unfold setStage
  have h : (stageBanks M j).val < 93 := j.isLt
  rw [dif_pos h]
  rfl

private theorem setStage_off {M : SearchTransducer} (m : Fin (W M) → Int → Option Bool)
    (v : Fin 93 → Int → Option Bool) (j : Fin (W M)) (hj : j ∉ Set.range (stageBanks M)) :
    setStage M m v j = m j := by
  apply dif_neg
  intro h
  exact hj ⟨⟨j.val,h⟩,Fin.ext rfl⟩

theorem room (M : SearchTransducer) : 7 ≤ (machine M).states := by
  have h : 7 ≤ D.states := by decide
  exact h.trans (Nat.le_add_right _ _)

def Core (M : SearchTransducer) {n : Nat} (G : Group (Fin n)) (x : Fin n)
    (ticks : List Bool) (B : Nat) : Prop :=
  ∀ (c : (prefixMachine M).Config), c.state = (prefixMachine M).initialState →
    c.workHead = (fun _ => 0) → (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (@encodeCayley n G.toMul).length →
    (∀ i p, p.natAbs ≤ B → c.workCell (nativeBank M i) p = none) →
    CayleyReaderCycle.Ready G x.val (left G.toOne.one) (left x) 1 ticks (fun i => c.workCell (readerBank M i)) →
    ∃ k d, (prefixMachine M).BoundedSegment (@encodeCayley n G.toMul) B c d k ∧
      (prefixMachine M).step (@encodeCayley n G.toMul) d = none ∧
      prefixBit M d.state = PhysicalGreedyPrefixCall.prefixVerdict G x ∧
      d.outputReversed = c.outputReversed ∧ d.workHead = (fun _ => 0) ∧
      (∀ i, d.workCell (nativeBank M i) = c.workCell (nativeBank M i)) ∧
      CayleyReaderCycle.Ready G x.val (left G.toOne.one) (left x) 1 ticks (fun i => d.workCell (readerBank M i))

structure Outcome (M : SearchTransducer) {n : Nat} (G : Group (Fin n)) (x : Fin n)
    (ticks : List Bool) (B : Nat) (pos : Int) (prior : List Bool)
    (m : Fin (W M) → Int → Option Bool) (k : Nat) (d : (machine M).Config) : Prop where
  bounded : (machine M).BoundedSegment (@encodeCayley n G.toMul) B (entry M pos prior m) d k
  halted : (machine M).step (@encodeCayley n G.toMul) d = none
  answer : (call M).answer d.state = PhysicalGreedyPrefixCall.prefixVerdict G x
  priorOutput : d.outputReversed = prior
  parked : d.workHead = (fun _ => 0)
  ready : Ready M G ticks B d.workCell
  headerFrame : ∀ j : PhysicalGreedyHeaderInstall.Bank, j.val < 11 →
    headerView (memory M d.workCell) j = headerView (memory M m) j
  callerFrame : ∀ j : Fin (W M), 93 ≤ j.val → j.val < 95 → d.workCell j = m j
private theorem joinPrepared (A P : SearchTransducer) {W : Nat}
    (e : Fin A.workTapes ↪ Fin W) (f : Fin P.workTapes ↪ Fin W)
    (d : A.Config) (m mid : Fin W → Int → Option Bool)
    (heads : d.workHead = (fun _ => 0)) (inside : ∀ j, d.workCell j = mid (e j))
    (outside : ∀ j ∉ Set.range e, m j = mid j) :
    let c : P.Config := ⟨P.initialState,d.inputHead,fun _ => 0,fun i => mid (f i),d.outputReversed⟩
    thenEntry A P e f (A.bankConfig e d (fun _ => 0) m) = P.bankConfig f c (fun _ => 0) mid := by
  dsimp only
  rw [liftedCfg P f mid P.initialState d.inputHead d.outputReversed]
  apply configEq
  · rfl
  · rfl
  · funext i
    by_cases h : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := h
      exact (A.bankConfig_head_image e d (fun _ => 0) m j).trans (congrFun heads j)
    · exact (A.bankConfig_frame e d (fun _ => 0) m h).1
  · funext i
    by_cases h : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := h
      exact (A.bankConfig_cell_image e d (fun _ => 0) m j).trans (inside j)
    · exact (A.bankConfig_frame e d (fun _ => 0) m h).2.trans (outside i h)
  · rfl

private theorem joinedSegment (A P : SearchTransducer) {W : Nat}
    (e : Fin A.workTapes ↪ Fin W) (f : Fin P.workTapes ↪ Fin W)
    {word : List Bool} {B a b : Nat} {initial d : A.Config} {c last : P.Config}
    (m mid : Fin W → Int → Option Bool)
    (r : A.BoundedSegment word B initial d a) (done : A.step word d = none)
    (s : P.BoundedSegment word B c last b)
    (handoff : thenEntry A P e f (A.bankConfig e d (fun _ => 0) m) =
      P.bankConfig f c (fun _ => 0) mid) :
    (thenMachine A P e f).BoundedSegment word B
      (thenLeft A P e f (A.bankConfig e initial (fun _ => 0) m))
      (thenRight A P e f (P.bankConfig f last (fun _ => 0) mid)) (a+1+b) := by
  have pre := A.relocateBanks_segment e r (heads := fun _ => 0) (cells := m) (by simp)
  have post := P.relocateBanks_segment f s (heads := fun _ => 0) (cells := mid) (by simp)
  have dh : (A.relocateBanks e).step word (A.bankConfig e d (fun _ => 0) m) = none := by
    rw [relocateBanks_step,done]
    rfl
  rw [← handoff] at post
  exact thenSegment A P e f pre dh post
private theorem postconditions {M : SearchTransducer} {n : Nat} (G : Group (Fin n)) (x : Fin n)
    (ticks : List Bool) (B : Nat) (m : Fin (W M) → Int → Option Bool)
    (v : Fin 93 → Int → Option Bool) (R : Ready M G ticks B m)
    (H : PhysicalGreedyHeaderInstall.Ready n G.toOne.one.val x.val (headerView (memory M m)))
    (header : headerView v = PhysicalGreedyHeaderDriver.final n G.toOne.one.val x.val (headerView (memory M m)))
    (d : (prefixMachine M).Config) (heads : d.workHead = (fun _ => 0))
    (unchanged : ∀ i, d.workCell (nativeBank M i) = setStage M m v (nativeBanks M (nativeBank M i)))
    (final : CayleyReaderCycle.Ready G x.val (left G.toOne.one) (left x) 1 ticks
      (fun i => d.workCell (readerBank M i))) :
    let mid := setStage M m v
    let pF := (prefixMachine M).bankConfig (nativeBanks M) d (fun _ => 0) mid
    let z := thenRight D (prefixMachine M) (stageBanks M) (nativeBanks M) pF
    z.workHead = (fun _ => 0) ∧ Ready M G ticks B z.workCell ∧
    (∀ j : PhysicalGreedyHeaderInstall.Bank, j.val < 11 →
      headerView (memory M z.workCell) j = headerView (memory M m) j) ∧
    (∀ j : Fin (W M), 93 ≤ j.val → j.val < 95 → z.workCell j = m j) := by
  let P := prefixMachine M
  let e := stageBanks M
  let f := nativeBanks M
  let mid := setStage M m v
  let pF := P.bankConfig f d (fun _ => 0) mid
  let z := thenRight D P e f pF

  have frame (j : PhysicalGreedyHeaderInstall.Bank) :
      headerView (memory M z.workCell) j = PhysicalGreedyHeaderDriver.final n G.toOne.one.val x.val
        (headerView (memory M m)) j := by
    let i := CayleyReaderCandidate.header j
    have untouched := (P.bankConfig_frame f d (fun _ => 0) mid
      (after_header (e i) (by change 74 ≤ 74+j.val; omega) (by
        change 74+j.val < 95; have := j.isLt; omega))).2
    exact untouched.trans ((setStage_on m v i).trans (congrFun header j))
  refine ⟨?_,?_,?_,?_⟩
  · as_aux_lemma =>
      funext i
      by_cases h : i ∈ Set.range f
      · obtain ⟨j,rfl⟩ := h
        exact (P.bankConfig_head_image f d (fun _ => 0) mid j).trans (congrFun heads j)
      · exact (P.bankConfig_frame f d (fun _ => 0) mid h).1
  · as_aux_lemma =>
      refine ⟨⟨x.val,x,1,?_⟩,?_,?_,?_,?_⟩
      · have eq : readerView (memory M z.workCell) = fun i => d.workCell (readerBank M i) := by
          funext i
          change pF.workCell (e (CayleyReaderCandidate.reader i)) = _
          rw [← nativeBanks_read]
          exact P.bankConfig_cell_image f d (fun _ => 0) mid _
        exact eq.symm ▸ final
      · intro i p hp
        change pF.workCell (f (nativeBank M i)) p = none
        rw [P.bankConfig_cell_image,unchanged]
        change setStage M m v (nativeBanks M (nativeBank M i)) p = none
        rw [setStage_off m v _ (native_out i)]
        exact R.native i p hp
      · exact (frame 2).trans ((PhysicalGreedyHeaderDriver.untouched 2 (by decide)).trans R.headerId)
      · intro i
        let j := PhysicalGreedyHeaderInstall.constBank i
        have lt : j.val < 11 := by change 3+i.val < 11; have := i.isLt; omega
        exact (frame j).trans ((PhysicalGreedyHeaderDriver.untouched j lt).trans (R.headerConstants i))
      · intro j hj
        rw [frame j]
        exact scratchAfter H j hj
  · intro j hj
    exact (frame j).trans (PhysicalGreedyHeaderDriver.untouched j hj)
  · intro j hj h95
    have notStage : j ∉ Set.range e := by
      rintro ⟨i,rfl⟩
      change 93 ≤ i.val at hj
      have h := i.isLt
      change i.val < 93 at h
      omega
    exact (P.bankConfig_frame f d (fun _ => 0) mid (after_header j (by omega) h95)).2.trans
      (setStage_off m v j notStage)



private theorem joinedHalt (A P : SearchTransducer) {W : Nat}
    (e : Fin A.workTapes ↪ Fin W) (f : Fin P.workTapes ↪ Fin W)
    (word : List Bool) (d : P.Config) (m : Fin W → Int → Option Bool)
    (halt : P.step word d = none) :
    (thenMachine A P e f).step word
      (thenRight A P e f (P.bankConfig f d (fun _ => 0) m)) = none := by
  rw [thenStep_right,relocateBanks_step,halt]
  rfl

private theorem joinedOutput (A P : SearchTransducer) {W : Nat}
    (e : Fin A.workTapes ↪ Fin W) (f : Fin P.workTapes ↪ Fin W)
    (d : P.Config) (m : Fin W → Int → Option Bool) :
    (thenRight A P e f (P.bankConfig f d (fun _ => 0) m)).outputReversed =
      d.outputReversed := rfl

private theorem splitBit {a b : Nat} (q : Fin b) (test : Fin b → Bool) :
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr q) : Fin (a+b))).elim
      (fun _ => false) test = test q := by rw [Equiv.symm_apply_apply]; rfl
private def prefixStart (M : SearchTransducer) (pos : Int) (prior : List Bool)
    (mid : Fin (W M) → Int → Option Bool) : (prefixMachine M).Config :=
  ⟨(prefixMachine M).initialState,pos,fun _ => 0,fun i => mid (nativeBanks M i),prior⟩

private theorem prepareCore {M : SearchTransducer} {n : Nat} (G : Group (Fin n)) (x : Fin n)
    (ticks : List Bool) (B : Nat) (pos : Int) (prior : List Bool)
    (m : Fin (W M) → Int → Option Bool) (v : Fin 93 → Int → Option Bool)
    (R : Ready M G ticks B m)
    (legal : (-1 : Int) ≤ pos ∧ pos ≤ (@encodeCayley n G.toMul).length)
    (ready : CayleyReaderCycle.Ready G x.val (left G.toOne.one) (left x) 1 ticks (readerView v))
    (core : Core M G x ticks B) :
    let c := prefixStart M pos prior (setStage M m v)
    ∃ k d, (prefixMachine M).BoundedSegment (@encodeCayley n G.toMul) B c d k ∧
      (prefixMachine M).step (@encodeCayley n G.toMul) d = none ∧
      prefixBit M d.state = PhysicalGreedyPrefixCall.prefixVerdict G x ∧
      d.outputReversed = prior ∧ d.workHead = (fun _ => 0) ∧
      (∀ i, d.workCell (nativeBank M i) = setStage M m v (nativeBanks M (nativeBank M i))) ∧
      CayleyReaderCycle.Ready G x.val (left G.toOne.one) (left x) 1 ticks (fun i => d.workCell (readerBank M i)) := by
  let P := prefixMachine M
  let mid := setStage M m v
  let f := nativeBanks M
  let c : P.Config := ⟨P.initialState,pos,fun _ => 0,fun i => mid (f i),prior⟩
  have cp : (fun i => c.workCell (readerBank M i)) = readerView v := by
    funext i
    change mid (f (readerBank M i)) = v (CayleyReaderCandidate.reader i)
    rw [nativeBanks_read]
    exact setStage_on (M := M) m v _
  have cb (i : Fin M.workTapes) (p : Int) (hp : p.natAbs ≤ B) :
      c.workCell (nativeBank M i) p = none := by
    change setStage M m v (nativeBanks M (nativeBank M i)) p = none
    rw [setStage_off m v _ (native_out i)]
    exact R.native i p hp
  exact core c rfl rfl legal cb (cp.symm ▸ ready)

private theorem finish {M : SearchTransducer} {n : Nat} (G : Group (Fin n)) (x : Fin n)
    (ticks : List Bool) (B : Nat) (budget : ticks.length+1 ≤ B)
    (pos : Int) (prior : List Bool) (m : Fin (W M) → Int → Option Bool)
    (R : Ready M G ticks B m)
    (H : PhysicalGreedyHeaderInstall.Ready n G.toOne.one.val x.val (headerView (memory M m)))
    (v : Fin 93 → Int → Option Bool)
    (header : headerView v = PhysicalGreedyHeaderDriver.final n G.toOne.one.val x.val (headerView (memory M m)))
    (a b : Nat) (q : Fin D.states) (d : (prefixMachine M).Config)
    (pr : D.BoundedSegment (@encodeCayley n G.toMul) (ticks.length+1)
      (cfg CayleyReaderRetarget.machine D.initialState pos prior (memory M m))
      (cfg CayleyReaderRetarget.machine q pos prior v) a)
    (halt : D.step (@encodeCayley n G.toMul) (cfg CayleyReaderRetarget.machine q pos prior v) = none)
    (s : (prefixMachine M).BoundedSegment (@encodeCayley n G.toMul) B
      (prefixStart M pos prior (setStage M m v)) d b)
    (stop : (prefixMachine M).step (@encodeCayley n G.toMul) d = none)
    (answer : prefixBit M d.state = PhysicalGreedyPrefixCall.prefixVerdict G x)
    (out : d.outputReversed = prior) (heads : d.workHead = (fun _ => 0))
    (unchanged : ∀ i, d.workCell (nativeBank M i) = setStage M m v (nativeBanks M (nativeBank M i)))
    (final : CayleyReaderCycle.Ready G x.val (left G.toOne.one) (left x) 1 ticks
      (fun i => d.workCell (readerBank M i))) :
    ∃ (k : Nat) (d : (machine M).Config), Outcome M G x ticks B pos prior m k d := by
  let word := @encodeCayley n G.toMul
  let P := prefixMachine M
  let e := stageBanks M
  let f := nativeBanks M
  let mid := setStage M m v
  let endD := cfg CayleyReaderRetarget.machine q pos prior v
  let pD := D.bankConfig e endD (fun _ => 0) m
  let c := prefixStart M pos prior mid
  let pC := P.bankConfig f c (fun _ => 0) mid
  have hand : thenEntry D P e f pD = pC :=
    joinPrepared D P e f endD m mid rfl (fun j => (setStage_on m v j).symm)
      (fun j no => (setStage_off m v j no).symm)
  let z := thenRight D P e f (P.bankConfig f d (fun _ => 0) mid)
  have joint : (machine M).BoundedSegment word B (entry M pos prior m) z (a+1+b) :=
    joinedSegment D P e f m mid (PhysicalEntry.segment_mono pr budget) halt s hand
  obtain ⟨park,restore,keep,caller⟩ := postconditions G x ticks B m v R H header d heads
    (fun i => unchanged i) final
  have hHalt := joinedHalt D P e f word d mid stop
  have hAnswer : (call M).answer z.state = PhysicalGreedyPrefixCall.prefixVerdict G x :=
    (splitBit d.state (prefixBit M)).trans answer
  have hOut := (joinedOutput D P e f d mid).trans out
  have outcome : Outcome M G x ticks B pos prior m (a+1+b) z :=
    ⟨joint,hHalt,hAnswer,hOut,park,restore,keep,caller⟩
  exact ⟨a+1+b,z,outcome⟩

private theorem assemble {M : SearchTransducer} {n : Nat} (G : Group (Fin n)) (x : Fin n)
    (ticks : List Bool) (B : Nat) (budget : ticks.length+1 ≤ B) (core : Core M G x ticks B)
    (pos : Int) (prior : List Bool) (m : Fin (W M) → Int → Option Bool)
    (legal : (-1 : Int) ≤ pos ∧ pos ≤ (@encodeCayley n G.toMul).length)
    (R : Ready M G ticks B m)
    (H : PhysicalGreedyHeaderInstall.Ready n G.toOne.one.val x.val (headerView (memory M m)))
    (v : Fin 93 → Int → Option Bool)
    (ready : CayleyReaderCycle.Ready G x.val (left G.toOne.one) (left x) 1 ticks (readerView v))
    (header : headerView v = PhysicalGreedyHeaderDriver.final n G.toOne.one.val x.val (headerView (memory M m)))
    (prepared : Run CayleyReaderRetarget.machine (@encodeCayley n G.toMul) (ticks.length+1)
      pos prior (memory M m) v) :
    ∃ (k : Nat) (d : (machine M).Config), Outcome M G x ticks B pos prior m k d := by

  obtain ⟨a,q,pr,halt⟩ := prepared
  obtain ⟨b,d,s,stop,answer,out,heads,unchanged,final⟩ :=
    prepareCore G x ticks B pos prior m v R legal ready core
  exact finish G x ticks B budget pos prior m R H v header a b q d
    pr halt s stop answer out heads unchanged final

/-- Compose the checked header update, the candidate installation, and a
concrete recurrent prefix controller on the shared 95-bank caller layout. -/
theorem execute {M : SearchTransducer} {n : Nat} (G : Group (Fin n)) (x : Fin n)
    (ticks : List Bool) (B : Nat) (budget : ticks.length+1 ≤ B) (core : Core M G x ticks B)
    (pos : Int) (prior : List Bool) (m : Fin (W M) → Int → Option Bool)
    (legal : (-1 : Int) ≤ pos ∧ pos ≤ (@encodeCayley n G.toMul).length)
    (R : Ready M G ticks B m)
    (ord : headerView (memory M m) 0 = PhysicalGreedyHeaderInstall.wordAt (TableIO.width n) n)
    (lab : headerView (memory M m) 1 = PhysicalGreedyHeaderInstall.wordAt (TableIO.width n) x.val) :
    ∃ (k : Nat) (d : (machine M).Config), Outcome M G x ticks B pos prior m k d := by
  obtain ⟨cut,oldX,p,R0⟩ := R.reader
  let H : PhysicalGreedyHeaderInstall.Ready n G.toOne.one.val x.val (headerView (memory M m)) :=
    ⟨ord,lab,R.headerId,R.headerConstants,R.headerScratch⟩
  obtain ⟨prepared,reader,header⟩ :=
    CayleyReaderRetarget.execute G cut p oldX x ticks prior pos (memory M m) R0 H legal
  exact assemble G x ticks B budget core pos prior m legal R H _ reader header prepared

end Mathproof.MinimumGeneration.PhysicalGreedyNativeLeaf
