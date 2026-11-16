import Mathproof.MinimumGenerationPhysicalGreedyHeaderCheckout
import Mathproof.MinimumGenerationPhysicalGreedyRaw

namespace Mathproof.MinimumGeneration.PhysicalGreedyPrefixCall

open SearchTransducer GreedyTapeScan PhysicalGreedyHeader
open PhysicalGreedyHeaderInstall (Bank Ready wordAt outside constBank outside_word)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev H := PhysicalGreedyHeaderDriver.machine
abbrev C := PhysicalGreedyHeaderCheckout.machine

variable (P : SearchTransducer) (e : Bank ↪ Fin P.workTapes)
variable (verdict : Fin P.states → Bool)

private def sameBanks : Fin P.workTapes ↪ Fin P.workTapes := Function.Embedding.refl _

abbrev pre := thenMachine H P e (sameBanks P)

def stageSize := (pre P e).states + C.states

def readVerdict (q : Fin (pre P e).states) : Bool :=
  if h : H.states ≤ q.val then verdict ⟨q.val-H.states, by
    have ht := q.isLt
    change q.val < H.states+P.states at ht
    omega⟩ else false

private theorem hPre : (pre P e).states ≤ stageSize P e := Nat.le_add_right _ _

private theorem hC : C.states ≤ stageSize P e := Nat.le_add_left _ _

/-- Prepare and run one native query. Two copies of the same checkout program
carry the answer across scratch restoration in finite control. -/
abbrev stages : Stages 3 (stageSize P e) P.workTapes where
  first := 0
  entry i := if i=0 then (pre P e).initialState.castLE (hPre P e)
    else C.initialState.castLE (hC P e)
  transition i := if i=0 then (pre P e).padTransition (hPre P e) (sameBanks P)
    else C.padTransition (hC P e) e
  next i q := if i=0 then
    if h : q.val < (pre P e).states then
      if readVerdict P e verdict ⟨q.val,h⟩ then some 2 else some 1
    else none
    else none

abbrev machine := (stages P e verdict).machine

def call : BitCall (machine P e verdict).states P.workTapes where
  entry := (machine P e verdict).initialState
  transition := (machine P e verdict).transition
  answer q := decide ((finProdFinEquiv.symm q).1 = (2 : Fin 3))

theorem room : 7 ≤ (machine P e verdict).states := by
  change 7 ≤ 3 * ((pre P e).states + 4)
  omega

def view (m : Fin P.workTapes → Int → Option Bool) : Bank → Int → Option Bool :=
  fun j => m (e j)

def scratch : Set (Fin P.workTapes) := {j | ∃ i : Bank, 11 ≤ i.val ∧ e i = j}

def required : Set (Fin P.workTapes) := {j | ∃ i : Bank, 2 ≤ i.val ∧ e i = j}

private def template (n id : Nat) (i : Bank) : Int → Option Bool :=
  if i=2 then wordAt (TableIO.width n) id
  else if hi : 3 ≤ i.val ∧ i.val < 11 then wordAt (width n) (fixed n id ⟨i.val-3,by omega⟩)
  else wordAt (width n) 0

noncomputable def saved (n id : Nat) (j : Fin P.workTapes) : Int → Option Bool :=
  if h : j ∈ Set.range e then template n id (Classical.choose h) else fun _ => none

private theorem saved_image (n id : Nat) (i : Bank) :
    saved P e n id (e i) =
      if i=2 then wordAt (TableIO.width n) id
      else if h : 3 ≤ i.val ∧ i.val < 11 then wordAt (width n) (fixed n id ⟨i.val-3,by omega⟩)
      else wordAt (width n) 0 := by
  classical
  unfold saved
  have hh : e i ∈ Set.range e := ⟨i,rfl⟩
  rw [dif_pos hh]
  have prop : Classical.choose hh = i := e.injective (Classical.choose_spec hh)
  exact congrArg (template n id) prop

theorem ready_of_frame {n id x : Nat} {m : Fin P.workTapes → Int → Option Bool}
    (ord : m (e 0) = wordAt (TableIO.width n) n)
    (lab : m (e 1) = wordAt (TableIO.width n) x)
    (imm : ∀ j ∈ required P e, m j = saved P e n id j) :
    Ready n id x (view P e m) := by
  refine ⟨ord,lab,?_,?_,?_⟩
  · change m (e 2) = _
    rw [imm (e 2) ⟨2,by decide,rfl⟩, saved_image]
    rfl
  · intro i
    change m (e (constBank i)) = _
    rw [imm _ ⟨constBank i,by change 2 ≤ 3+i.val; omega,rfl⟩, saved_image]
    have n2 : constBank i ≠ 2 := fun h => by
      have z := congrArg (fun j : Bank => j.val) h
      rcases i with ⟨i,hi⟩
      change 3+i=2 at z
      omega
    have h : 3 ≤ (constBank i).val ∧ (constBank i).val < 11 := by
      change 3 ≤ 3+i.val ∧ 3+i.val < 11
      omega
    rw [if_neg n2, dif_pos h]
    suffices same : (⟨(constBank i).val-3,by omega⟩ : Fin 8) = i by rw [same]
    apply Fin.ext
    change 3+i.val-3 = i.val
    omega
  · intro i hi
    change outside (width n) (m (e i))
    rw [imm _ ⟨i,by omega,rfl⟩, saved_image]
    have n2 : i ≠ 2 := fun h => by subst i; contradiction
    have nb : ¬(3 ≤ i.val ∧ i.val < 11) := by omega
    rw [if_neg n2, dif_neg nb]
    exact outside_word _ _

def rawWord {n : Nat} (G : Group (Fin n)) := @encodeCayley n G.toMul

def prefixVerdict {n : Nat} (G : Group (Fin n)) (x : Fin n) : Bool :=
  BipartiteCayley.rawPrefixQuery (rawWord G) G.toOne.one (fun _ => true) x.val x

/-- The sole query implementation premise is execution of the native reader
from an already installed bipartite query. It returns its Boolean in control.
The marked scratch windows stay delimited for the actual checkout sweep. -/
def Core {n : Nat} (G : Group (Fin n)) (B : Nat) (keep : Set (Fin P.workTapes)) : Prop :=
  ∀ (x : Fin n) (c : P.Config),
    c.state = P.initialState →
    c.workHead = (fun _ => 0) →
    (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (rawWord G).length →
    PhysicalGreedyHeaderDriver.Live n G.toOne.one.val x.val (view P e c.workCell) →
    ∃ (ticks : Nat) (d : P.Config), P.BoundedSegment (rawWord G) B c d ticks ∧
      P.step (rawWord G) d = none ∧ verdict d.state = prefixVerdict G x ∧
      d.workHead = (fun _ => 0) ∧ d.outputReversed = c.outputReversed ∧
      (∀ j ∈ keep, j ∉ scratch P e → d.workCell j = c.workCell j) ∧
      (∀ i : Bank, 11 ≤ i.val → outside (width n) (d.workCell (e i)))

private theorem configEq {M : SearchTransducer} (c d : M.Config)
    (hq : c.state = d.state) (hi : c.inputHead = d.inputHead)
    (hh : c.workHead = d.workHead) (hc : c.workCell = d.workCell)
    (ho : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem same_head (M : SearchTransducer) (c : M.Config) (h : Fin M.workTapes → Int)
    (m : Fin M.workTapes → Int → Option Bool) :
    (M.bankConfig (sameBanks M) c h m).workHead = c.workHead := by
  funext j
  exact M.bankConfig_head_image (sameBanks M) c h m j

private theorem same_cell (M : SearchTransducer) (c : M.Config) (h : Fin M.workTapes → Int)
    (m : Fin M.workTapes → Int → Option Bool) :
    (M.bankConfig (sameBanks M) c h m).workCell = c.workCell := by
  funext j
  exact M.bankConfig_cell_image (sameBanks M) c h m j

private theorem headerStart (input : Int) (cells : Bank → Int → Option Bool) (prior : List Bool) :
    let c := PhysicalGreedyHeaderDriver.start input cells prior
    c.state = H.initialState ∧ c.inputHead = input ∧ c.workHead = (fun _ => 0) ∧
      c.workCell = cells ∧ c.outputReversed = prior := by
  let M := PhysicalGreedyHeaderInstall.machine
  let e := PhysicalGreedyHeaderDriver.banks
  let a := PhysicalGreedyHeaderInstall.start input cells prior
  obtain ⟨hi,hh,hc,ho⟩ := PhysicalGreedyHeaderInstall.start_layout input cells prior
  refine ⟨rfl,hi,?_,?_,ho⟩
  · funext j
    exact (M.bankConfig_head_image e a (fun _ => 0) cells j).trans (congrFun hh j)
  · funext j
    exact (M.bankConfig_cell_image e a (fun _ => 0) cells j).trans (congrFun hc j)

private theorem relocated_heads (M : SearchTransducer) {W : Nat} (e : Fin M.workTapes ↪ Fin W)
    (c : M.Config) (m : Fin W → Int → Option Bool)
    (hh : c.workHead = fun _ => 0) : (M.bankConfig e c (fun _ => 0) m).workHead = fun _ => 0 := by
  funext j
  by_cases h : j ∈ Set.range e
  · obtain ⟨i,rfl⟩ := h
    exact (M.bankConfig_head_image e c _ _ i).trans (congrFun hh i)
  · exact (M.bankConfig_frame e c _ _ h).1

private def padPre (c : (pre P e).Config) : ((stages P e verdict).component 0).Config :=
  (pre P e).padConfig (hPre P e) (sameBanks P)
    ((pre P e).bankConfig (sameBanks P) c (fun _ => 0) (fun _ _ => none))

private def nextStage (b : Bool) : Fin 3 := if b then 2 else 1

private theorem nextStage_ne (b : Bool) : nextStage b ≠ 0 := by cases b <;> decide

private def padCheckout (b : Bool) (c : C.Config)
    (m : Fin P.workTapes → Int → Option Bool) : ((stages P e verdict).component (nextStage b)).Config := by
  cases b <;> exact C.padConfig (hC P e) e (C.bankConfig e c (fun _ => 0) m)

def preStart (input : Int) (cells : Fin P.workTapes → Int → Option Bool) (prior : List Bool) :
    (pre P e).Config :=
  thenLeft H P e (sameBanks P)
    (H.bankConfig e (PhysicalGreedyHeaderDriver.start input (view P e cells) prior)
      (fun _ => 0) cells)

private theorem preStart_layout (input : Int) (cells : Fin P.workTapes → Int → Option Bool)
    (prior : List Bool) :
    (preStart P e input cells prior).inputHead = input ∧
    (preStart P e input cells prior).workHead = (fun _ => 0) ∧
    (preStart P e input cells prior).workCell = cells ∧
    (preStart P e input cells prior).outputReversed = prior := by
  let a := PhysicalGreedyHeaderDriver.start input (view P e cells) prior
  obtain ⟨_,hi,hh,hc,ho⟩ := headerStart input (view P e cells) prior
  refine ⟨hi,relocated_heads H e a cells hh,?_,ho⟩
  funext j
  by_cases h : j ∈ Set.range e
  · obtain ⟨i,rfl⟩ := h
    exact (H.bankConfig_cell_image e a (fun _ => 0) cells i).trans (congrFun hc i)
  · exact (H.bankConfig_frame e a (fun _ => 0) cells h).2

def entry (input : Int) (cells : Fin P.workTapes → Int → Option Bool) (prior : List Bool) :
    (machine P e verdict).Config :=
  (stages P e verdict).tag 0 (padPre P e verdict (preStart P e input cells prior))

private theorem entry_layout (input : Int) (cells : Fin P.workTapes → Int → Option Bool)
    (prior : List Bool) :
    (entry P e verdict input cells prior).state = (machine P e verdict).initialState ∧
    (entry P e verdict input cells prior).inputHead = input ∧
    (entry P e verdict input cells prior).workHead = (fun _ => 0) ∧
    (entry P e verdict input cells prior).workCell = cells ∧
    (entry P e verdict input cells prior).outputReversed = prior := by
  have ⟨hi,hh,hc,ho⟩ := preStart_layout P e input cells prior
  refine ⟨rfl,hi,(same_head (pre P e) _ (fun _ => 0) (fun _ _ => none)).trans hh,
    (same_cell (pre P e) _ (fun _ => 0) (fun _ _ => none)).trans hc,ho⟩

private theorem pre_execute {n B : Nat} (G : Group (Fin n)) (x : Fin n)
    (keep : Set (Fin P.workTapes)) (core : Core P e verdict G B keep)
    (Bsize : width n + 1 ≤ B) (input : Int) (prior : List Bool)
    (m : Fin P.workTapes → Int → Option Bool)
    (hin : (-1 : Int) ≤ input ∧ input ≤ (rawWord G).length)
    (R : Ready n G.toOne.one.val x.val (view P e m)) :
    ∃ (ticks : Nat) (d : (pre P e).Config),
      (pre P e).BoundedSegment (rawWord G) B (preStart P e input m prior) d ticks ∧
      (pre P e).step (rawWord G) d = none ∧
      readVerdict P e verdict d.state = prefixVerdict G x ∧
      d.workHead = (fun _ => 0) ∧ d.outputReversed = prior ∧
      (∀ j ∈ keep, j ∉ scratch P e → d.workCell j = m j) ∧
      (∀ i : Bank, 11 ≤ i.val → outside (width n) (d.workCell (e i))) := by
  let raw := rawWord G
  obtain ⟨k,h,hs,hh,hi,hp,hc,ho,live⟩ := PhysicalGreedyHeaderDriver.execute
    (raw := raw) (prior := prior) R hin (x.isLt.trans Nat.lt_log2_self)
  let lifted := H.bankConfig e h (fun _ => 0) m
  let arg : P.Config := ⟨P.initialState,lifted.inputHead,lifted.workHead,lifted.workCell,
    lifted.outputReversed⟩
  have first := H.relocateBanks_segment e (PhysicalEntry.segment_mono hs Bsize)
    (heads := fun _ => 0) (cells := m) (by simp)
  have firstStop : (H.relocateBanks e).step raw lifted = none := by
    unfold lifted
    rw [relocateBanks_step,hh]
    rfl
  have hview : view P e arg.workCell = h.workCell := by
    funext i
    exact H.bankConfig_cell_image e h (fun _ => 0) m i
  have contents (j : Fin P.workTapes) (hj : j ∉ scratch P e) :
      arg.workCell j = m j := by
    by_cases he : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := he
      have small : i.val < 11 := by
        by_contra! rr
        exact hj ⟨i,rr,rfl⟩
      exact (H.bankConfig_cell_image e h (fun _ => 0) m i).trans
        ((congrFun hc i).trans (PhysicalGreedyHeaderDriver.untouched i small))
    · exact (H.bankConfig_frame e h (fun _ => 0) m he).2
  obtain ⟨l,d,runP,haltP,answer,heads,out,unchanged,clean⟩ :=
    core x arg rfl (relocated_heads H e h m hp) (by change (-1 : Int) ≤ h.inputHead ∧ h.inputHead ≤ (rawWord G).length; rwa [hi])
      (by rw [hview]; exact live)
  let c := P.bankConfig (sameBanks P) arg (fun _ => 0) m
  let z := P.bankConfig (sameBanks P) d (fun _ => 0) m
  have tr := P.relocateBanks_segment (sameBanks P) runP (heads := fun _ => 0) (cells := m) (by simp)
  change (P.relocateBanks (sameBanks P)).BoundedSegment raw B c z l at tr
  have enter : thenEntry H P e (sameBanks P) lifted = c :=
    configEq _ _ rfl rfl (same_head P arg (fun _ => 0) m).symm (same_cell P arg (fun _ => 0) m).symm rfl
  rw [← enter] at tr
  have stopZ : (P.relocateBanks (sameBanks P)).step raw z = none := by
    unfold z
    rw [relocateBanks_step,haltP]
    rfl
  let last := thenRight H P e (sameBanks P) z
  refine ⟨_,last,thenSegment H P e (sameBanks P) first firstStop tr,?_,?_ ,
    (same_head P d (fun _ => 0) m).trans heads, out.trans ho,?_,?_⟩
  · change (pre P e).step raw last = none
    rw [thenStep_right,stopZ]
    rfl
  · have hv : H.states ≤ last.state.val := by
      change H.states ≤ H.states + d.state.val
      omega
    unfold readVerdict
    rw [dif_pos hv]
    have idx : (⟨last.state.val-H.states,by
        have h := last.state.isLt
        change last.state.val < H.states + P.states at h
        omega⟩ : Fin P.states) = d.state := by
      apply Fin.ext
      change H.states+d.state.val-H.states = d.state.val
      omega
    rw [idx,answer]
  · intro j hj hsc
    exact ((congrFun (same_cell P d (fun _ => 0) m) j).trans (unchanged j hj hsc)).trans (contents j hsc)
  · intro i hs
    simpa only [last,thenRight,show z.workCell = d.workCell from same_cell P d (fun _ => 0) m] using clean i hs

private theorem finishStage {raw : List Bool} {B n : Nat}
    (d : (pre P e).Config) (inputBounds : (-1 : Int) ≤ d.inputHead ∧ d.inputHead ≤ raw.length)
    (parked : d.workHead = (fun _ => 0)) (zero : d.workCell (e 3) = wordAt (width n) 0)
    (clean : ∀ i : Bank, 11 ≤ i.val → outside (width n) (d.workCell (e i)))
    (Bsize : width n+1 ≤ B) :
    let T := stages P e verdict
    let b := readVerdict P e verdict d.state
    let j := nextStage b
    ∃ (ticks : Nat) (z : (T.component j).Config),
      (T.component j).BoundedSegment raw B (T.enter j (padPre P e verdict d)) z ticks ∧
      (T.component j).step raw z = none ∧
      z.inputHead = d.inputHead ∧ z.workHead = (fun _ => 0) ∧
      z.outputReversed = d.outputReversed ∧
      (∀ k ∉ scratch P e, z.workCell k = d.workCell k) ∧
      (∀ i : Bank, 11 ≤ i.val → z.workCell (e i) = wordAt (width n) 0) := by
  let T := stages P e verdict
  let b := readVerdict P e verdict d.state
  let j := nextStage b
  let m := view P e d.workCell
  let r := PhysicalGreedyHeaderCheckout.restore
  let a := TapeInstall.start 3 r d.inputHead m d.outputReversed
  let z := TapeInstall.stop 3 r d.inputHead m d.outputReversed (width n)
  obtain ⟨k,run,halt,hi,hh,ho,frame,washed⟩ := PhysicalGreedyHeaderCheckout.execute
    (n := n) (raw := raw) (old := m) zero clean inputBounds
  let first := C.bankConfig e a (fun _ => 0) d.workCell
  let last := C.bankConfig e z (fun _ => 0) d.workCell
  have R := C.relocateBanks_segment e (PhysicalEntry.segment_mono run Bsize)
    (heads := fun _ => 0) (cells := d.workCell) (by simp)
  have padded := C.padMachine_segment (hC P e) e R
  have hhalt : (C.padMachine (hC P e) e).step raw (C.padConfig (hC P e) e last) = none := by
    rw [C.padMachine_step, C.relocateBanks_step,halt]
    rfl
  have lifted : (T.component j).BoundedSegment raw B
      (padCheckout P e verdict b a d.workCell) (padCheckout P e verdict b z d.workCell) k ∧
      (T.component j).step raw (padCheckout P e verdict b z d.workCell) = none := by
    dsimp only [j]
    generalize b = bit
    cases bit <;> exact ⟨padded,hhalt⟩
  have padA :
      (padCheckout P e verdict b a d.workCell).inputHead = d.inputHead ∧
      (padCheckout P e verdict b a d.workCell).workHead = first.workHead ∧
      (padCheckout P e verdict b a d.workCell).workCell = first.workCell ∧
      (padCheckout P e verdict b a d.workCell).outputReversed = d.outputReversed := by
    generalize b = bit
    cases bit <;> exact ⟨rfl,rfl,rfl,rfl⟩
  have padZ :
      (padCheckout P e verdict b z d.workCell).inputHead = z.inputHead ∧
      (padCheckout P e verdict b z d.workCell).workHead = last.workHead ∧
      (padCheckout P e verdict b z d.workCell).workCell = last.workCell ∧
      (padCheckout P e verdict b z d.workCell).outputReversed = z.outputReversed := by
    generalize b = bit
    cases bit <;> exact ⟨rfl,rfl,rfl,rfl⟩
  have hStartCells : first.workCell = d.workCell := by
    funext p
    by_cases hp : p ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hp
      exact C.bankConfig_cell_image e a (fun _ => 0) d.workCell i
    · exact (C.bankConfig_frame e a (fun _ => 0) d.workCell hp).2
  have jump : T.enter j (padPre P e verdict d) = padCheckout P e verdict b a d.workCell := by
    apply configEq
    · dsimp only [j]
      generalize b = bit
      cases bit <;> rfl
    · exact padA.1.symm
    · apply ((same_head (pre P e) d (fun _ => 0) (fun _ _ => none)).trans parked).trans
      exact (padA.2.1.trans (relocated_heads C e a d.workCell rfl)).symm
    · exact (same_cell (pre P e) d (fun _ => 0) (fun _ _ => none)).trans
        (padA.2.2.1.trans hStartCells).symm
    · exact padA.2.2.2.symm
  rw [← jump] at lifted
  refine ⟨k,padCheckout P e verdict b z d.workCell,lifted.1,lifted.2,padZ.1.trans hi,
    padZ.2.1.trans (relocated_heads C e z d.workCell hh),padZ.2.2.2.trans ho,?_,?_⟩
  · intro p h
    by_cases hp : p ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hp
      have small : i.val < 11 := by by_contra! hbig; exact h ⟨i,hbig,rfl⟩
      exact (congrFun padZ.2.2.1 (e i)).trans
        ((C.bankConfig_cell_image e z (fun _ => 0) d.workCell i).trans (frame i small))
    · exact (congrFun padZ.2.2.1 p).trans (C.bankConfig_frame e z (fun _ => 0) d.workCell hp).2
  · intro i h
    exact (congrFun padZ.2.2.1 (e i)).trans
      ((C.bankConfig_cell_image e z (fun _ => 0) d.workCell i).trans (washed i h))

private theorem zero_of_frame {n id : Nat} {m : Fin P.workTapes → Int → Option Bool}
    (imm : ∀ j ∈ required P e, m j = saved P e n id j) {i : Bank} (hi : 11 ≤ i.val) :
    m (e i) = wordAt (width n) 0 := by
  rw [imm _ ⟨i,by omega,rfl⟩,saved_image]
  have a : i ≠ 2 := fun h => by subst i; contradiction
  have b : ¬(3 ≤ i.val ∧ i.val < 11) := by omega
  rw [if_neg a,dif_neg b]

def guard (keep : Set (Fin P.workTapes)) :=
  {j | j ∈ keep ∨ j = e 0 ∨ j = e 1}

private theorem unscratch (i : Bank) (hi : i.val < 11) : e i ∉ scratch P e := by
  rintro ⟨j,h,hij⟩
  have same := e.injective hij
  rw [same] at h
  omega

/-- One physical prefix-membership call with setup, native query and cleanup.
The only uncompiled component required here is execution of the native query
from its concrete, prepared register layout. -/
theorem execute {n B : Nat} (G : Group (Fin n)) (x : Fin n)
    (keep : Set (Fin P.workTapes)) (need : required P e ⊆ keep)
    (core : Core P e verdict G B (guard P e keep)) (Bsize : width n+1 ≤ B)
    (input : Int) (prior : List Bool) (m : Fin P.workTapes → Int → Option Bool)
    (hin : (-1 : Int) ≤ input ∧ input ≤ (rawWord G).length)
    (order : m (e 0) = wordAt (TableIO.width n) n)
    (candidate : m (e 1) = wordAt (TableIO.width n) x.val)
    (imm : ∀ j ∈ required P e, m j = saved P e n G.toOne.one.val j) :
    ∃ (ticks : Nat) (d : (machine P e verdict).Config),
      (machine P e verdict).BoundedSegment (rawWord G) B (entry P e verdict input m prior) d ticks ∧
      (machine P e verdict).step (rawWord G) d = none ∧
      (call P e verdict).answer d.state = prefixVerdict G x ∧
      d.workHead = (fun _ => 0) ∧ d.outputReversed = prior ∧
      ∀ j ∈ guard P e keep, d.workCell j = m j := by
  let M := pre P e
  let raw := rawWord G
  let T := stages P e verdict
  obtain ⟨k,d,run,done,bit,heads,out,frame,clean⟩ := pre_execute P e verdict G x (guard P e keep)
    core Bsize input prior m hin (ready_of_frame P e order candidate imm)
  let b := readVerdict P e verdict d.state
  let j := nextStage b
  have bd := run.2 k le_rfl d run.1
  have zero : d.workCell (e 3) = wordAt (width n) 0 :=
    (frame (e 3) (.inl (need ⟨3,by decide,rfl⟩)) (unscratch P e 3 (by decide))).trans
      ((ready_of_frame P e order candidate imm).constants 0)
  obtain ⟨l,z,rz,sz,iz,hz,oz,frameZ,scratchZ⟩ :=
    finishStage P e verdict d ⟨bd.1,bd.2.1⟩ heads zero clean Bsize
  have runRel := M.relocateBanks_segment (sameBanks P) run
    (heads := fun _ => 0) (cells := fun _ _ => none) (by simp)
  have pr := M.padMachine_segment (hPre P e) (sameBanks P) runRel
  change (T.component 0).BoundedSegment raw B (padPre P e verdict (preStart P e input m prior))
    (padPre P e verdict d) k at pr
  have stop : (T.component 0).step raw (padPre P e verdict d) = none := by
    change (M.padMachine (hPre P e) (sameBanks P)).step raw (padPre P e verdict d) = none
    unfold padPre
    rw [M.padMachine_step,M.relocateBanks_step,done]
    rfl
  have step : T.next 0 (padPre P e verdict d).state = some j := by
    change (if h : d.state.val < M.states then
      if readVerdict P e verdict ⟨d.state.val,h⟩ then some 2 else some 1 else none) = _
    rw [dif_pos d.state.isLt,Fin.eta]
    change (if b then some 2 else some 1) = some (nextStage b)
    cases b <;> rfl
  have finalStop : T.next j z.state = none := by
    simp [T,j,nextStage_ne b]
  have route : T.Routed raw B 0 (padPre P e verdict (preStart P e input m prior)) j z (k+1+l) :=
    .call pr stop step (.finish rz)
  obtain ⟨joined,halt⟩ := T.routed_stop route sz finalStop
  refine ⟨_,T.tag j z,joined,halt,?_,hz,oz.trans out,?_⟩
  · change decide ((finProdFinEquiv.symm (finProdFinEquiv (j,z.state))).1 = (2 : Fin 3)) = _
    rw [Equiv.symm_apply_apply,← bit]
    change decide (nextStage b = (2 : Fin 3)) = b
    cases b <;> decide
  · intro p hp
    by_cases h : p ∈ scratch P e
    · obtain ⟨i,hi,rfl⟩ := h
      exact (scratchZ i hi).trans (zero_of_frame P e imm hi).symm
    · exact (frameZ p h).trans (frame p hp h)

/-- Supply a ready-state native prefix query and get the actual membership leaf
consumed by the checked greedy candidate scan and ordinal selector. -/
theorem leaf {n B : Nat} (G : Group (Fin n)) (keep : Set (Fin P.workTapes))
    (need : required P e ⊆ keep)
    (core : Core P e verdict G B (guard P e keep)) (Bsize : width n+1 ≤ B) :
    FramedLeaf (e 1) (e 0) (room P e verdict) (PhysicalGreedyRaw.allowAll (room P e verdict))
      (call P e verdict) (B := B) (rawWord G) 2
      (fun x => RawGreedyMembership.query (rawWord G) G.toOne.one
        (GreedyGenerator.before (fun _ => true) x.val) x)
      (call P e verdict).answer keep (required P e) (saved P e n G.toOne.one.val) := by
  intro x c hEntry prepared imm
  obtain ⟨ticks,d,run,halt,answer,heads,out,frame⟩ :=
    execute P e verdict G x keep need core Bsize c.inputHead c.outputReversed c.workCell
      ⟨prepared.inputLo,prepared.inputHi⟩ prepared.order prepared.cursor imm
  have layout := entry_layout P e verdict c.inputHead c.workCell c.outputReversed
  have start : entry P e verdict c.inputHead c.workCell c.outputReversed = c :=
    configEq _ _ (layout.1.trans hEntry.symm) layout.2.1
      (layout.2.2.1.trans prepared.heads.symm) layout.2.2.2.1 layout.2.2.2.2
  rw [start] at run
  have bounds := run.2 ticks le_rfl d run.1
  refine ⟨ticks,d,run,halt,?_,⟨bounds.1,bounds.2.1,heads,
    (frame (e 1) (.inr (.inr rfl))).trans prepared.cursor,
    (frame (e 0) (.inr (.inl rfl))).trans prepared.order⟩,out,fun j hj => frame j (.inl hj)⟩
  rw [answer]
  exact BipartiteCayley.rawPrefixQuery_eq_ordinary G (fun _ => true) x.val x

/-- Run the raw generator ordinal from a live Cayley label and a framed
native prefix reader. Header setup, membership dispatch, scratch checkout,
and all ordinal arithmetic are part of the same finite controller. -/
theorem executeOrdinal {n B : Nat} (G : Group (Fin n))
    (ordinal zero : Fin P.workTapes) (keep : Set (Fin P.workTapes))
    (need : required P e ⊆ keep)
    (distinct : e 1 ∉ keep ∧ e 1 ≠ ordinal ∧ e 1 ≠ zero)
    (mutable : ordinal ∉ keep) (ordOrder : ordinal ≠ e 0) (ordZero : ordinal ≠ zero)
    (core : Core P e verdict G B (guard P e (PhysicalGreedyTape.kept keep ordinal zero)))
    (Bsize : width n+1 ≤ B) (k i : Nat) (hi : i < 2 ^ TableIO.width n) :
    let member := call P e verdict
    let allowed := PhysicalGreedyRaw.allowAll (room P e verdict)
    let T := PhysicalGreedyTape.stages (e 1) (e 0) ordinal zero (room P e verdict) allowed member
    let raw := rawWord G
    let accept := GreedyGenerator.accept (RawGreedyMembership.query raw G.toOne.one) (fun _ => true)
    let expected := (GreedyOrdinal.collect accept 0 n)[i]?
    ∀ (c : (T.component 4).Config), c.state = T.entry 4 →
      PhysicalGreedyTape.Live (M := T.component 4) raw n k i (e 1) (e 0) ordinal zero c →
      (∀ j ∈ required P e, c.workCell j = saved P e n G.toOne.one.val j) →
      ∃ (ticks : Nat) (d : T.machine.Config),
        T.machine.BoundedSegment raw B (T.tag 4 c) d ticks ∧ T.machine.step raw d = none ∧
        PhysicalGreedyTape.found (label := e 1) (order := e 0) (ordinal := ordinal)
          (zero := zero) (widthStates := room P e verdict) (allowed := allowed) (member := member) d =
          expected.isSome ∧
        d.workCell (e 1) = wordAt (TableIO.width n) (expected.elim n Fin.val) ∧
        d.workHead = (fun _ => 0) ∧ d.outputReversed = c.outputReversed ∧
        ∀ j ∈ keep, d.workCell j = c.workCell j := by
  have diff : e 1 ≠ e 0 := fun h => (by decide : (1 : Bank) ≠ 0) (e.injective h)
  exact PhysicalGreedyRaw.executeFramed G (e 1) (e 0) ordinal zero (room P e verdict) (call P e verdict)
    keep (required P e) (saved P e n G.toOne.one.val) need distinct mutable diff ordOrder ordZero
    (by unfold width at Bsize; omega)
    (leaf P e verdict G (PhysicalGreedyTape.kept keep ordinal zero) (fun _ hj => .inl (need hj)) core Bsize)
    k i hi

end Mathproof.MinimumGeneration.PhysicalGreedyPrefixCall
