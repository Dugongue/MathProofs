import Mathproof.MinimumGenerationPhysicalGreedyTape
import Mathproof.MinimumGenerationGreedyTapeScanInvariant
import Batteries.Tactic.OpenPrivate

namespace Mathproof.MinimumGeneration.PhysicalGreedyOrdinalInvariant

open SearchTransducer
open GreedyTapeScan (BitCall Prepared)
open PhysicalGreedyTape (Live found kept)
open PhysicalGreedyRegisters (Parked)

open private inner nativeEntry pad padHead padCell transfer nextAt atFound from Mathproof.MinimumGenerationPhysicalGreedyTape

open InputPosition (work)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable {S W : Nat} {label order ordinal zero : Fin W}
variable {widthStates : 7 ≤ S} {allowed member : BitCall S W}

local notation "T" => PhysicalGreedyTape.stages label order ordinal zero widthStates allowed member

local notation "Pad0" => pad (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 0)
local notation "Head0" => padHead (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 0)
local notation "Cell0" => padCell (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 0)
local notation "Entry0" => nativeEntry (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 0)
local notation "NextAt0" => nextAt (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 0)
local notation "Pad1" => pad (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 1)
local notation "Head1" => padHead (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 1)
local notation "Cell1" => padCell (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 1)
local notation "Entry1" => nativeEntry (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 1)
local notation "NextAt1" => nextAt (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 1)
local notation "Pad2" => pad (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 2)
local notation "Head2" => padHead (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 2)
local notation "Cell2" => padCell (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 2)
local notation "Entry2" => nativeEntry (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 2)
local notation "NextAt2" => nextAt (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 2)
local notation "Pad3" => pad (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 3)
local notation "Head3" => padHead (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 3)
local notation "Cell3" => padCell (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 3)
local notation "Entry3" => nativeEntry (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 3)
local notation "NextAt3" => nextAt (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 3)
local notation "Pad4" => pad (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 4)
local notation "Head4" => padHead (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 4)
local notation "Cell4" => padCell (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 4)
local notation "Entry4" => nativeEntry (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 4)
local notation "NextAt4" => nextAt (label := label) (order := order) (ordinal := ordinal) (zero := zero) (widthStates := widthStates) (allowed := allowed) (member := member) (i := 4)

private theorem iter {word : List Bool} {n B : Nat}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Fin W)) (invariant : (Fin W → Int → Option Bool) → Prop)
    (stableLabel : GreedyTapeScanInvariant.Stable label invariant)
    (stableOrdinal : GreedyTapeScanInvariant.Stable ordinal invariant)
    (hl : label ∉ kept keep ordinal zero) (ho : ordinal ∉ keep)
    (hlo : label ≠ order) (hoo : ordinal ≠ order) (hoz : ordinal ≠ zero)
    (bound : TableIO.width n + 1 ≤ B)
    (eligibleRun : GreedyTapeScanInvariant.Leaf label order widthStates allowed member (B := B)
      word 1 eligible allowed.answer (kept keep ordinal zero) invariant)
    (memberRun : GreedyTapeScanInvariant.Leaf label order widthStates allowed member (B := B) word 2
      (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer (kept keep ordinal zero) invariant)
    (k i : Nat) (hk : k ≤ n) (hi : i < 2^(TableIO.width n))
    (c : ((T).component 0).Config) (entry : c.state = (T).entry 0)
    (live : Live word n k i label order ordinal zero c)
    (hInv : invariant c.workCell) :
    ∃ (k' : Nat) (j : Fin 5) (d : ((T).component j).Config),
      (T).Routed word B 0 c j d k' ∧ ((T).component j).step word d = none ∧
      (T).next j d.state = none ∧ found ((T).tag j d) = (PhysicalGreedyReplay.byNext query eligible k i).isSome ∧
      (∀ x : Fin n, PhysicalGreedyReplay.byNext query eligible k i = some x →
        Prepared word n x.val label order d) ∧
      (PhysicalGreedyReplay.byNext query eligible k i = none → Prepared word n n label order d) ∧
      d.outputReversed = c.outputReversed ∧ invariant d.workCell ∧
      (∃ r, d.workCell ordinal = work (encodeLabel (TableIO.width n) r)) ∧
      d.workCell zero = work (encodeLabel (TableIO.width n) 0) ∧
      ∀ j ∈ keep, d.workCell j = c.workCell j := by
  let A := inner label order widthStates allowed member
  let entry0 : (A.component 0).Config := ⟨A.entry 0, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩
  have hEntry : A.tag 0 entry0 = Entry0 c := rfl
  have hInit : Prepared word n k label order entry0 := ⟨live.base.inputLo, live.base.inputHi, live.base.heads,
      live.base.cursor, live.base.order⟩
  obtain ⟨sc, out, run, halt, yes, onYes, onNo, untouched, inv, frame⟩ :=
    GreedyTapeScanInvariant.execute label order widthStates allowed member query eligible
      (kept keep ordinal zero) invariant stableLabel hl hlo bound
      eligibleRun memberRun k hk entry0 rfl hInit hInv
  rw [hEntry] at run
  obtain ⟨hScan, hStop⟩ := transfer entry run halt
  have onYes' (x : Fin n) (h : GreedyGenerator.next query eligible k = some x) :
      Prepared word n x.val label order (Pad0 out) := by
    have q := onYes x h
    exact ⟨q.inputLo,q.inputHi,funext fun j =>
      (Head0 out j).trans (congrFun q.heads j),
      (Cell0 out label).trans q.cursor,(Cell0 out order).trans q.order⟩
  have onNo' (h : GreedyGenerator.next query eligible k = none) :
      Prepared word n n label order (Pad0 out) := by
    have q := onNo h
    exact ⟨q.inputLo,q.inputHi,funext fun j =>
      (Head0 out j).trans (congrFun q.heads j),
      (Cell0 out label).trans q.cursor,(Cell0 out order).trans q.order⟩
  have hNext : (T).next 0 (Pad0 out).state =
      if (GreedyGenerator.next query eligible k).isSome then some 1 else none := by
    rw [NextAt0]
    change (if (finProdFinEquiv.symm out.state).1 = (2 : Fin 4) then some 1 else none) = _
    change decide ((finProdFinEquiv.symm out.state).1 = (2 : Fin 4)) = _ at yes
    rw [← yes]
    simp
  have frame0 (j : Fin W) (hj : j ∈ kept keep ordinal zero) :
      (Pad0 out).workCell j = c.workCell j := (Cell0 out j).trans (frame j hj)
  have inv0 : invariant (Pad0 out).workCell := by
    rw [show (Pad0 out).workCell = out.workCell from funext (Cell0 out)]
    exact inv
  cases hn : GreedyGenerator.next query eligible k with
  | none =>
    have hNone : PhysicalGreedyReplay.byNext query eligible k i = none := by
      cases i <;> simp [PhysicalGreedyReplay.byNext, hn]
    refine ⟨sc, 0, Pad0 out, .finish hScan, hStop, by simp [hNext, hn],
      by simp [atFound, hNone], by simp [hNone], fun _ => onNo' hn,
      untouched, inv0, ⟨i,(frame0 ordinal (.inr (.inl rfl))).trans live.index⟩,
      (frame0 zero (.inr (.inr rfl))).trans live.zeros, fun j hj => frame0 j (.inl hj)⟩
  | some x =>
    have hMore : (T).next 0 (Pad0 out).state = some 1 := by simp [hNext, hn]
    let c1 := (T).enter (1 : Fin 5) (Pad0 out)
    have hp := onYes' x hn
    have p1 : Parked word (Entry1 c1) := ⟨hp.inputLo,hp.inputHi,hp.heads⟩
    have idx1 : (Entry1 c1).workCell ordinal =
        work (encodeLabel (TableIO.width n) i) :=
      (frame0 ordinal (.inr (.inl rfl))).trans live.index
    have zero1 : (Entry1 c1).workCell zero = work (encodeLabel (TableIO.width n) 0) :=
      (frame0 zero (.inr (.inr rfl))).trans live.zeros
    obtain ⟨d1, r1, s1, isZero, in1, heads1, cells1, out1⟩ :=
      PhysicalGreedyRegisters.compareZero ordinal zero (Entry1 c1) rfl p1 i hi idx1 zero1 bound
    obtain ⟨seg1, stop1⟩ := transfer (c := c1) rfl r1 s1
    have n1 : (T).next 1 (Pad1 d1).state = if i = 0 then none else some 2 := by
      rw [NextAt1]
      change (if d1.state.val = (TapeRegisters.done true).val then none else some 2) = _
      simp only [show d1.state.val = (TapeRegisters.done true).val ↔ i = 0 from
        ⟨fun h => isZero.mp (Fin.ext h), fun h => congrArg Fin.val (isZero.mpr h)⟩]
    have back1 : Prepared word n x.val label order (Pad1 d1) := by
      refine ⟨?_,?_,funext fun j => (Head1 d1 j).trans (congrFun (heads1.trans hp.heads) j),
        (Cell1 d1 label).trans ((congrFun cells1 label).trans hp.cursor),
        (Cell1 d1 order).trans ((congrFun cells1 order).trans hp.order)⟩
      · change _ ≤ d1.inputHead
        rw [in1]
        exact hp.inputLo
      · change d1.inputHead ≤ _
        rw [in1]
        exact hp.inputHi
    have frame1 (j : Fin W) (hj : j ∈ kept keep ordinal zero) :
        (Pad1 d1).workCell j = c.workCell j := (Cell1 d1 j).trans ((congrFun cells1 j).trans (frame0 j hj))
    have inv1 : invariant (Pad1 d1).workCell := by
      rw [show (Pad1 d1).workCell = (Pad0 out).workCell from funext (fun j =>
        (Cell1 d1 j).trans (congrFun cells1 j))]
      exact inv0
    cases i with
    | zero =>
      have hSome : PhysicalGreedyReplay.byNext query eligible k 0 = some x := hn
      refine ⟨_,1,Pad1 d1,.call hScan hStop hMore (.finish seg1),stop1,by simp [n1],
        by simp [atFound,hSome],?_,by simp [hSome],out1.trans untouched,inv1,⟨0,(frame1 ordinal (.inr (.inl rfl))).trans live.index⟩,
        (frame1 zero (.inr (.inr rfl))).trans live.zeros,fun j hj => frame1 j (.inl hj)⟩
      intro y hy
      rw [hSome] at hy
      cases hy
      exact back1
    | succ i =>
      have n1' : (T).next 1 (Pad1 d1).state = some 2 := by simp [n1]
      let c2 := (T).enter (2 : Fin 5) (Pad1 d1)
      have p2 : Parked word (Entry2 c2) := ⟨back1.inputLo,back1.inputHi,back1.heads⟩
      have idx2 : (Entry2 c2).workCell ordinal =
          work (encodeLabel (TableIO.width n) (i+1)) :=
        (frame1 ordinal (.inr (.inl rfl))).trans live.index
      obtain ⟨d2,r2,s2,in2,heads2,idxDone,out2,frame2⟩ :=
        PhysicalGreedyRegisters.change ordinal .decrement (Entry2 c2) rfl p2 (i+1)
          (by omega) idx2 bound
      obtain ⟨seg2,stop2⟩ := transfer (c := c2) rfl r2 s2
      have n2 : (T).next 2 (Pad2 d2).state = some 3 := by rw [NextAt2]; rfl
      have back2 : Prepared word n x.val label order (Pad2 d2) := by
        refine ⟨?_,?_,funext fun j => (Head2 d2 j).trans (congrFun (heads2.trans back1.heads) j),
          (Cell2 d2 label).trans ((frame2 label (by exact fun h => hl (.inr (.inl h)))).trans back1.cursor),
          (Cell2 d2 order).trans ((frame2 order hoo.symm).trans back1.order)⟩
        · change _ ≤ d2.inputHead
          rw [in2]
          exact back1.inputLo
        · change d2.inputHead ≤ _
          rw [in2]
          exact back1.inputHi
      let c3 := (T).enter (3 : Fin 5) (Pad2 d2)
      have p3 : Parked word (Entry3 c3) := ⟨back2.inputLo,back2.inputHi,back2.heads⟩
      obtain ⟨d3,r3,s3,in3,heads3,labelDone,out3,frame3⟩ :=
        PhysicalGreedyRegisters.change label .increment (Entry3 c3) rfl p3 x.val
          (by intro h; contradiction) back2.cursor bound
      obtain ⟨seg3,stop3⟩ := transfer (c := c3) rfl r3 s3
      have n3 : (T).next 3 (Pad3 d3).state = some 0 := by rw [NextAt3]; rfl
      let c0 := (T).enter (0 : Fin 5) (Pad3 d3)
      have back3 : Live word n (x.val+1) i label order ordinal zero c0 := by
        refine ⟨⟨?_,?_,funext fun j => (Head3 d3 j).trans (congrFun (heads3.trans back2.heads) j),
          (Cell3 d3 label).trans labelDone,
          (Cell3 d3 order).trans ((frame3 order hlo.symm).trans back2.order)⟩,?_,?_⟩
        · change _ ≤ d3.inputHead
          rw [in3]
          exact back2.inputLo
        · change d3.inputHead ≤ _
          rw [in3]
          exact back2.inputHi
        · exact (Cell3 d3 ordinal).trans ((frame3 ordinal (fun h => hl (.inr (.inl h.symm)))).trans
            ((Cell2 d2 ordinal).trans (by simpa [PhysicalGreedyRegisters.nextValue] using idxDone)))
        · exact (Cell3 d3 zero).trans ((frame3 zero (fun h => hl (.inr (.inr h.symm)))).trans
            ((Cell2 d2 zero).trans ((frame2 zero hoz.symm).trans
              ((frame1 zero (.inr (.inr rfl))).trans live.zeros))))
      have carried (j : Fin W) (hj : j ∈ keep) : c0.workCell j = c.workCell j :=
        (Cell3 d3 j).trans ((frame3 j (fun h => hl (h ▸ Or.inl hj))).trans
          ((Cell2 d2 j).trans ((frame2 j (fun h => ho (h ▸ hj))).trans (frame1 j (.inl hj)))))
      have inv2 : invariant (Pad2 d2).workCell :=
        stableOrdinal (Pad1 d1).workCell (Pad2 d2).workCell
          (fun j hj => (Cell2 d2 j).trans (frame2 j hj)) inv1
      have inv3 : invariant c0.workCell :=
        stableLabel (Pad2 d2).workCell c0.workCell
          (fun j hj => (Cell3 d3 j).trans (frame3 j hj)) inv2
      obtain ⟨ticks,j,d,route,done,noNext,foundRest,someRest,noneRest,keepOut,invOut,indexOut,zeroOut,last⟩ :=
        iter query eligible keep invariant stableLabel stableOrdinal hl ho hlo hoo hoz bound eligibleRun memberRun (x.val+1) i
          (Nat.succ_le_of_lt x.isLt) (lt_trans (Nat.lt_succ_self i) hi) c0 rfl back3 inv3
      have recur : PhysicalGreedyReplay.byNext query eligible k (i+1) =
          PhysicalGreedyReplay.byNext query eligible (x.val+1) i := by
        simp [PhysicalGreedyReplay.byNext, hn]
      refine ⟨_,j,d,.call hScan hStop hMore (.call seg1 stop1 n1' (.call seg2 stop2 n2
        (.call seg3 stop3 n3 route))),done,noNext,
        by simpa only [recur] using foundRest,
        fun y hy => someRest y (recur.symm.trans hy),
        fun hy => noneRest (recur.symm.trans hy),
        keepOut.trans (out3.trans (out2.trans (out1.trans untouched))),invOut,indexOut,zeroOut,?_⟩
      intro j hj
      exact (last j hj).trans (carried j hj)
termination_by i

/-- Clear the live label register, then perform the requested ordinal query.
The terminal label bank contains the exact chosen label or the order sentinel.
Only eligibility and prefix membership for one candidate enter as call ports. -/
theorem executeWithRegisters {word : List Bool} {n B : Nat}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Fin W)) (invariant : (Fin W → Int → Option Bool) → Prop)
    (stableLabel : GreedyTapeScanInvariant.Stable label invariant)
    (stableOrdinal : GreedyTapeScanInvariant.Stable ordinal invariant)
    (hl : label ∉ keep ∧ label ≠ ordinal ∧ label ≠ zero)
    (ho : ordinal ∉ keep) (hlo : label ≠ order)
    (hoo : ordinal ≠ order) (hoz : ordinal ≠ zero)
    (bound : TableIO.width n + 1 ≤ B)
    (eligibleRun : GreedyTapeScanInvariant.Leaf label order widthStates allowed member (B := B)
      word 1 eligible allowed.answer (kept keep ordinal zero) invariant)
    (memberRun : GreedyTapeScanInvariant.Leaf label order widthStates allowed member (B := B) word 2
      (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer (kept keep ordinal zero) invariant)
    (k i : Nat) (hi : i < 2^(TableIO.width n))
    (c : ((T).component 4).Config) (entry : c.state = (T).entry 4)
    (live : Live word n k i label order ordinal zero c)
    (hInv : invariant c.workCell) :
    let expected := GreedyOrdinal.ordinal (GreedyGenerator.accept query eligible) 0 n i
    ∃ (ticks : Nat) (d : (T).machine.Config),
      (T).machine.BoundedSegment word B ((T).tag 4 c) d ticks ∧
      (T).machine.step word d = none ∧
      found (label := label) (order := order) (ordinal := ordinal) (zero := zero)
        (widthStates := widthStates) (allowed := allowed) (member := member) d = expected.isSome ∧
      d.workCell label = work (encodeLabel (TableIO.width n) (expected.elim n Fin.val)) ∧
      d.workHead = (fun _ => 0) ∧
      d.outputReversed = c.outputReversed ∧ invariant d.workCell ∧
      (∃ r, d.workCell ordinal = work (encodeLabel (TableIO.width n) r)) ∧
      d.workCell zero = work (encodeLabel (TableIO.width n) 0) ∧
      d.workCell order = work (encodeLabel (TableIO.width n) n) ∧
      ∀ j ∈ keep, d.workCell j = c.workCell j := by
  have hp : Parked word (Entry4 c) := ⟨live.base.inputLo,live.base.inputHi,live.base.heads⟩
  obtain ⟨d,r,h,inp,heads,clear,out,frame⟩ :=
    PhysicalGreedyRegisters.clear label (Entry4 c) rfl hp
      (encodeLabel (TableIO.width n) k) (length_encodeLabel _ _) live.base.cursor bound
  obtain ⟨seg,stop⟩ := transfer (c := c) entry r h
  have next0 : (T).next 4 (Pad4 d).state = some 0 := by rw [NextAt4]; rfl
  let c0 := (T).enter (0 : Fin 5) (Pad4 d)
  have hp0 : Live word n 0 i label order ordinal zero c0 := by
    refine ⟨⟨?_,?_,funext fun j => (Head4 d j).trans (congrFun (heads.trans live.base.heads) j),
      (Cell4 d label).trans clear,(Cell4 d order).trans ((frame order hlo.symm).trans live.base.order)⟩,
      (Cell4 d ordinal).trans ((frame ordinal hl.2.1.symm).trans live.index),
      (Cell4 d zero).trans ((frame zero hl.2.2.symm).trans live.zeros)⟩
    · change _ ≤ d.inputHead
      rw [inp]
      exact live.base.inputLo
    · change d.inputHead ≤ _
      rw [inp]
      exact live.base.inputHi
  have hn : label ∉ kept keep ordinal zero := by
    rintro (h | h | h)
    · exact hl.1 h
    · exact hl.2.1 h
    · exact hl.2.2 h
  have inv0 : invariant c0.workCell := stableLabel c.workCell c0.workCell
    (fun j hj => (Cell4 d j).trans (frame j hj)) hInv
  obtain ⟨ticks,j,z,route,done,none,answer,yes,no,output,invOut,indexOut,zeroOut,rest⟩ :=
    iter query eligible keep invariant stableLabel stableOrdinal hn ho hlo hoo hoz bound eligibleRun memberRun 0 i
      (Nat.zero_le n) hi c0 rfl hp0 inv0
  obtain ⟨joined,halt⟩ := (T).routed_stop (.call seg stop next0 route) done none
  let expected := GreedyOrdinal.ordinal (GreedyGenerator.accept query eligible) 0 n i
  have exactAnswer : PhysicalGreedyReplay.byNext query eligible 0 i = expected := by
    simp [expected, PhysicalGreedyReplay.byNext_eq_ordinal]
  rw [exactAnswer] at answer yes no
  have labelBank : z.workCell label =
      work (encodeLabel (TableIO.width n) (expected.elim n Fin.val)) ∧
      z.workHead = (fun _ => 0) ∧ z.workCell order = work (encodeLabel (TableIO.width n) n) := by
    cases he : expected with
    | none =>
      have q := no he
      exact ⟨q.cursor,q.heads,q.order⟩
    | some x =>
      have q := yes x he
      exact ⟨q.cursor,q.heads,q.order⟩
  refine ⟨_,(T).tag j z,joined,halt,answer,labelBank.1,labelBank.2.1,output.trans out,invOut,
    indexOut,zeroOut,labelBank.2.2,?_⟩
  intro j hj
  exact (rest j hj).trans ((Cell4 d j).trans (frame j (fun h => hl.1 (h ▸ hj))))


theorem execute {word : List Bool} {n B : Nat}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Fin W)) (invariant : (Fin W → Int → Option Bool) → Prop)
    (stableLabel : GreedyTapeScanInvariant.Stable label invariant)
    (stableOrdinal : GreedyTapeScanInvariant.Stable ordinal invariant)
    (hl : label ∉ keep ∧ label ≠ ordinal ∧ label ≠ zero)
    (ho : ordinal ∉ keep) (hlo : label ≠ order)
    (hoo : ordinal ≠ order) (hoz : ordinal ≠ zero)
    (bound : TableIO.width n + 1 ≤ B)
    (eligibleRun : GreedyTapeScanInvariant.Leaf label order widthStates allowed member (B := B)
      word 1 eligible allowed.answer (kept keep ordinal zero) invariant)
    (memberRun : GreedyTapeScanInvariant.Leaf label order widthStates allowed member (B := B) word 2
      (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer (kept keep ordinal zero) invariant)
    (k i : Nat) (hi : i < 2^(TableIO.width n))
    (c : ((T).component 4).Config) (entry : c.state = (T).entry 4)
    (live : Live word n k i label order ordinal zero c)
    (hInv : invariant c.workCell) :
    let expected := GreedyOrdinal.ordinal (GreedyGenerator.accept query eligible) 0 n i
    ∃ (ticks : Nat) (d : (T).machine.Config),
      (T).machine.BoundedSegment word B ((T).tag 4 c) d ticks ∧
      (T).machine.step word d = none ∧
      found (label := label) (order := order) (ordinal := ordinal) (zero := zero)
        (widthStates := widthStates) (allowed := allowed) (member := member) d = expected.isSome ∧
      d.workCell label = work (encodeLabel (TableIO.width n) (expected.elim n Fin.val)) ∧
      d.workHead = (fun _ => 0) ∧
      d.outputReversed = c.outputReversed ∧ invariant d.workCell ∧ ∀ j ∈ keep, d.workCell j = c.workCell j := by
  obtain ⟨ticks,d,run,halt,answer,cell,heads,out,inv,_,_,_,frame⟩ :=
    executeWithRegisters query eligible keep invariant stableLabel stableOrdinal hl ho hlo hoo hoz
      bound eligibleRun memberRun k i hi c entry live hInv
  exact ⟨ticks,d,run,halt,answer,cell,heads,out,inv,frame⟩

end Mathproof.MinimumGeneration.PhysicalGreedyOrdinalInvariant
