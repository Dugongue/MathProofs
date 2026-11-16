import Mathproof.MinimumGenerationCayleyQueryGuard
import Mathproof.MinimumGenerationCayleyQueryCoordinates

namespace Mathproof.MinimumGeneration.CayleyQueryRouter

open SearchTransducer CayleyQueryGuard
open InputPosition (work)
open Connectivity (ustconCell ustconHeaderLength)
open CayleyQueryDispatch
open VirtualMarkerScan (boundaryAddresses)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- A fixed physical caller for any pair of endpoint-bank identifiers. -/
structure CrossBranch (S W : ℕ) where
  entry : Fin 5 × Fin 5 → Fin S
  transition : Fin 5 × Fin 5 → MacroTransition S W
  answer : Fin 5 × Fin 5 → Fin S → Bool

def fork (ab : Fin 5 × Fin 5) : Fin 27 := Fin.natAdd 2 (finProdFinEquiv ab)

def unfork (i : Fin 27) : Fin 5 × Fin 5 :=
  (finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm ⟨i.val-2, by have := i.isLt; omega⟩

private theorem unfork_fork (ab : Fin 5 × Fin 5) : unfork (fork ab) = ab := by
  unfold unfork
  have h : (⟨(fork ab).val-2, by have := (fork ab).isLt; omega⟩ : Fin 25) =
      finProdFinEquiv ab := by
    apply Fin.ext
    change (2+(finProdFinEquiv ab).val)-2 = (finProdFinEquiv ab).val
    omega
  rw [h]
  exact Equiv.symm_apply_apply finProdFinEquiv ab

private theorem fork_nonzero (ab : Fin 5 × Fin 5) : fork ab ≠ 0 := by
  intro eq
  have h := congrArg (fun i : Fin 27 => i.val) eq
  change 2 + (finProdFinEquiv ab).val = 0 at h
  omega

private theorem fork_nonone (ab : Fin 5 × Fin 5) : fork ab ≠ 1 := by
  intro eq
  have h := congrArg (fun i : Fin 27 => i.val) eq
  change 2 + (finProdFinEquiv ab).val = 1 at h
  omega

variable {S W : ℕ} (address : Fin W) (markers : Fin 5 → Fin W) (guardBanks : Fin 2 ↪ Fin W)
    (coordBanks : Fin 10 ↪ Fin W) (cross : CrossBranch S W)
    (fit : CayleyQueryCoordinates.machine.states ≤ S)

private abbrev A := CayleyQueryGuard.machine address markers guardBanks
private abbrev D := CayleyQueryCoordinates.machine

private theorem guardCap (fit : CayleyQueryCoordinates.machine.states ≤ S) : (A address markers guardBanks).states ≤ S :=
  Nat.le_trans (by decide : 70 ≤ 105) fit

private def allBanks : Fin W ↪ Fin W := Function.Embedding.refl _

private def guardValue (q : Fin S) : Option InputCell :=
  if h : q.val < (A address markers guardBanks).states then
    CayleyQueryGuard.result address markers guardBanks ⟨⟨q.val,h⟩,0,fun _ => 0,fun _ _ => none,[]⟩
  else none

private def coordValue (q : Fin S) : Option (Fin 5 × Fin 5) :=
  if h : q.val < D.states then CayleyQueryCoordinates.orientation ⟨q.val,h⟩ else none

private theorem guardValue_exact (c : (A address markers guardBanks).Config) :
    guardValue address markers guardBanks (c.state.castLE (guardCap address markers guardBanks fit)) =
      CayleyQueryGuard.result address markers guardBanks c := by
  simp only [guardValue, Fin.val_castLE, dif_pos c.state.isLt, Fin.eta]
  rfl

private theorem coordValue_exact (q : Fin D.states) :
    coordValue (q.castLE fit) = CayleyQueryCoordinates.orientation q := by
  simp only [coordValue, Fin.val_castLE, dif_pos q.isLt, Fin.eta]

/-- One finite control routes the physical guard, coordinate machine and
the applicable oriented prefix leaf. -/
abbrev stages : Stages 27 S W where
  first := 0
  entry i :=
    if i = 0 then (A address markers guardBanks).initialState.castLE (guardCap address markers guardBanks fit)
    else if i = 1 then D.initialState.castLE fit else cross.entry (unfork i)
  transition i :=
    if i = 0 then (A address markers guardBanks).padTransition (guardCap address markers guardBanks fit) allBanks
    else if i = 1 then D.padTransition fit coordBanks
    else cross.transition (unfork i)
  next i q :=
    if i = 0 then if (guardValue address markers guardBanks q).isNone then some 1 else none
    else if i = 1 then (coordValue q).map fork else none

/-- The literal machine used by the selected pair of endpoint banks. -/
abbrev CrossBranch.machine (C : CrossBranch S W) (ab : Fin 5 × Fin 5) : SearchTransducer where
  states := S
  workTapes := W
  initialState := C.entry ab
  transition := C.transition ab

/-- The cross-side stage is exactly the selected call table. -/
theorem crossComponent (ab : Fin 5 × Fin 5) :
    (stages address markers guardBanks coordBanks cross fit).component (fork ab) =
      cross.machine ab := by
  simp only [Stages.component, fork_nonzero, fork_nonone, if_false, unfork_fork,
    CrossBranch.machine]

theorem crossEntry (ab : Fin 5 × Fin 5) :
    (stages address markers guardBanks coordBanks cross fit).entry (fork ab) = cross.entry ab := by
  simp only [fork_nonzero, fork_nonone, if_false, unfork_fork]


/-- Keep the data layout and tag the concrete machine with the selected
cross-side stage. -/
def liftCross (ab : Fin 5 × Fin 5) (c : (cross.machine ab).Config) :
    ((stages address markers guardBanks coordBanks cross fit).component (fork ab)).Config :=
  ⟨c.state,c.inputHead,c.workHead,c.workCell,c.outputReversed⟩

theorem liftCross_step (ab : Fin 5 × Fin 5) (raw : List Bool) (c : (cross.machine ab).Config) :
    ((stages address markers guardBanks coordBanks cross fit).component (fork ab)).step raw
      (liftCross address markers guardBanks coordBanks cross fit ab c) =
        ((cross.machine ab).step raw c).map (liftCross address markers guardBanks coordBanks cross fit ab) := by
  unfold SearchTransducer.step
  simp only [Stages.component, liftCross, CrossBranch.machine, Option.map_map,
    fork_nonzero, fork_nonone, if_false, unfork_fork]
  apply Option.map_congr
  intro x _
  obtain ⟨q,m,a,b⟩ := x
  rfl

theorem liftCross_run (ab : Fin 5 × Fin 5) (raw : List Bool) (c : (cross.machine ab).Config) (k : ℕ) :
    ((stages address markers guardBanks coordBanks cross fit).component (fork ab)).runFrom raw
      (liftCross address markers guardBanks coordBanks cross fit ab c) k =
        ((cross.machine ab).runFrom raw c k).map (liftCross address markers guardBanks coordBanks cross fit ab) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runFrom, ih]
    cases h : (cross.machine ab).runFrom raw c k with
    | none => rfl
    | some d => exact liftCross_step address markers guardBanks coordBanks cross fit ab raw d

theorem liftCross_segment (ab : Fin 5 × Fin 5) {raw : List Bool}
    {B k : ℕ} {c d : (cross.machine ab).Config}
    (h : (cross.machine ab).BoundedSegment raw B c d k) :
    ((stages address markers guardBanks coordBanks cross fit).component (fork ab)).BoundedSegment raw B
      (liftCross address markers guardBanks coordBanks cross fit ab c)
      (liftCross address markers guardBanks coordBanks cross fit ab d) k := by
  refine ⟨by rw [liftCross_run,h.1]; rfl,?_⟩
  intro n hn x hx
  rw [liftCross_run] at hx
  obtain ⟨a,b,rfl⟩ := Option.map_eq_some_iff.mp hx
  exact h.2 n hn a b


abbrev machine := (stages address markers guardBanks coordBanks cross fit).machine

def result (q : Fin (machine address markers guardBanks coordBanks cross fit).states) : InputCell :=
  let (i,c) := finProdFinEquiv.symm q
  if i = 0 then (guardValue address markers guardBanks c).getD (.data false)
  else if i = 1 then .data false else .data (cross.answer (unfork i) c)

abbrev callback : VirtualCallbackDriver.Callback where
  read := machine address markers guardBanks coordBanks cross fit
  returnCell := result address markers guardBanks coordBanks cross fit

private def putGuard (c : (A address markers guardBanks).Config) :
    ((stages address markers guardBanks coordBanks cross fit).component 0).Config :=
  (A address markers guardBanks).padConfig (guardCap address markers guardBanks fit) allBanks
    ((A address markers guardBanks).bankConfig allBanks c c.workHead c.workCell)

def start (input : Int) (cells : Fin W → Int → Option Bool) (out : List Bool) :
    (machine address markers guardBanks coordBanks cross fit).Config :=
  (stages address markers guardBanks coordBanks cross fit).tag 0
    (putGuard address markers guardBanks coordBanks cross fit
      (CayleyQueryGuard.start address markers guardBanks input cells out))

private def putCoord (c : D.Config) (heads : Fin W → Int) (cells : Fin W → Int → Option Bool) :
    ((stages address markers guardBanks coordBanks cross fit).component 1).Config :=
  D.padConfig fit coordBanks (D.bankConfig coordBanks c heads cells)

private theorem cfgEq {P : SearchTransducer} (a b : P.Config)
    (s : a.state = b.state) (p : a.inputHead = b.inputHead) (h : a.workHead = b.workHead)
    (z : a.workCell = b.workCell) (o : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

private theorem startCoord (d : ((stages address markers guardBanks coordBanks cross fit).component 0).Config)
    (w n offset : ℕ) (t0 : ∀ j, d.workHead j = 0)
    (tapes : ∀ j, d.workCell (coordBanks j) = CayleyQueryCoordinates.entryCells w n offset j) :
    let c := CayleyQueryCoordinates.start w n offset d.inputHead d.outputReversed
    (stages address markers guardBanks coordBanks cross fit).enter 1 d =
      putCoord address markers guardBanks coordBanks cross fit c d.workHead d.workCell := by
  intro c
  obtain ⟨control,hI,hO,hH,hC⟩ := CayleyQueryCoordinates.startSpec w n offset d.inputHead d.outputReversed
  let T := stages address markers guardBanks coordBanks cross fit
  refine cfgEq (T.enter (i := 0) 1 d) (putCoord address markers guardBanks coordBanks cross fit c d.workHead d.workCell)
    ?_ hI.symm ?_ ?_ hO.symm
  · change D.initialState.castLE fit = c.state.castLE fit
    rw [control]
  · funext j
    change d.workHead j = (D.bankConfig coordBanks c d.workHead d.workCell).workHead j
    by_cases hj : j ∈ Set.range coordBanks
    · obtain ⟨k,rfl⟩ := hj
      rw [bankConfig_head_image, t0, hH]
    · exact (bankConfig_frame D coordBanks c d.workHead d.workCell hj).1.symm
  · funext j
    change d.workCell j = (D.bankConfig coordBanks c d.workHead d.workCell).workCell j
    by_cases hj : j ∈ Set.range coordBanks
    · obtain ⟨k,rfl⟩ := hj
      rw [bankConfig_cell_image, hC]
      exact tapes k
    · exact (bankConfig_frame D coordBanks c d.workHead d.workCell hj).2.symm

/-- The graph matrix oracle when oriented original endpoint names are supplied. -/
def matrixBits {n : ℕ} (edge : Fin n → Fin n → Bool) (a b : Fin (n+n)) : Bool :=
  match BipartiteCayley.endpoints a b with
  | none => false
  | some (x,y) => edge x y

/-- Proof interface of the concrete cross-side stages. The output is one
state bit, and the caller's tracked frame remains available after the query. -/
def CrossPort {n : ℕ} (edge : Fin n → Fin n → Bool) (raw prior : List Bool)
    (w B : ℕ) (input : Int) (need keep : Set (Fin W)) (initial : Fin W → Int → Option Bool) :
    Prop :=
  let T := stages address markers guardBanks coordBanks cross fit
  ∀ (ab : Fin 5 × Fin 5) (x y : Fin n) (c : (T.component (fork ab)).Config),
    c.state = T.entry (fork ab) → c.inputHead = input → c.outputReversed = prior →
      (∀ j, c.workHead j = 0) →
      c.workCell (coordBanks (CayleyQueryCoordinates.slot ab.1)) = work (encodeLabel w x.val) →
      c.workCell (coordBanks (CayleyQueryCoordinates.slot ab.2)) = work (encodeLabel w y.val) →
      (∀ j ∈ need ∪ keep, c.workCell j = initial j) →
    ∃ (k : ℕ) (d : (T.component (fork ab)).Config), (T.component (fork ab)).BoundedSegment raw B c d k ∧
      (T.component (fork ab)).step raw d = none ∧ cross.answer ab d.state = edge x y ∧
      d.outputReversed = prior ∧ ∀ j ∈ keep, d.workHead j = 0 ∧ d.workCell j = initial j

private theorem offsetCell (w n p r : ℕ) (j : Fin 10) (neq : j ≠ 4) :
    CayleyQueryCoordinates.entryCells w n p j = CayleyQueryCoordinates.entryCells w n r j := by
  fin_cases j <;> first | rfl | contradiction

private theorem offsetSlot (w n r : ℕ) :
    CayleyQueryCoordinates.entryCells w n r (4 : Fin 10) = work (encodeLabel w r) := rfl

private theorem exactGuard {raw : List Bool} {B k : ℕ} {c d : (A address markers guardBanks).Config}
    (run : (A address markers guardBanks).BoundedSegment raw B c d k)
    (stop : (A address markers guardBanks).step raw d = none)
    (head0 : ∀ j, (c.workHead j).natAbs ≤ B) :
    let T := stages address markers guardBanks coordBanks cross fit
    let a := putGuard address markers guardBanks coordBanks cross fit c
    let b := (A address markers guardBanks).padConfig (guardCap address markers guardBanks fit) allBanks
      ((A address markers guardBanks).bankConfig allBanks d c.workHead c.workCell)
    (T.component 0).BoundedSegment raw B a b k ∧ (T.component 0).step raw b = none := by
  let P := A address markers guardBanks
  let f := guardCap address markers guardBanks fit
  have step := relocateBanks_segment P allBanks (heads := c.workHead) (cells := c.workCell) run
    (fun j _ => head0 j)
  have endRel := relocateBanks_step P allBanks raw d c.workHead c.workCell
  rw [stop] at endRel
  have endPad := P.padMachine_step f allBanks raw (P.bankConfig allBanks d c.workHead c.workCell)
  exact ⟨P.padMachine_segment f allBanks step,endPad.trans (congrArg _ endRel)⟩

private theorem exactCoord {raw : List Bool} {B k : ℕ} {c d : D.Config}
    (run : D.BoundedSegment raw B c d k) (stop : D.step raw d = none)
    (heads : Fin W → Int) (tapes : Fin W → Int → Option Bool)
    (hold : ∀ j, (heads j).natAbs ≤ B) :
    let T := stages address markers guardBanks coordBanks cross fit
    (T.component 1).BoundedSegment raw B (putCoord address markers guardBanks coordBanks cross fit c heads tapes)
      (putCoord address markers guardBanks coordBanks cross fit d heads tapes) k ∧
      (T.component 1).step raw (putCoord address markers guardBanks coordBanks cross fit d heads tapes) = none := by
  have step := relocateBanks_segment D coordBanks (heads := heads) (cells := tapes) run (fun j _ => hold j)
  have endRel := relocateBanks_step D coordBanks raw d heads tapes
  rw [stop] at endRel
  have endPad := D.padMachine_step fit coordBanks raw (D.bankConfig coordBanks d heads tapes)
  exact ⟨D.padMachine_segment fit coordBanks step,endPad.trans (congrArg _ endRel)⟩

/-- Execute the physical virtual reader on every legal shifted address.
The only supplied component is the independently executable cross-side leaf. -/
theorem execute {n : ℕ} (edge : Fin n → Fin n → Bool) (s t : Fin (n+n))
    {raw prior : List Bool} {B w p : ℕ} {input : Int} {cells : Fin W → Int → Option Bool}
    (layout : VirtualMarkerScan.Layout address markers raw B w p (boundaryAddresses s t)
      input (fun _ => 0) cells) (space : w+1 ≤ B)
    (addrCap : p ≤ ustconHeaderLength s t + (n+n)*(n+n) + 1)
    (mfit : n+n < 2^w) (matrixFit : (n+n)*(n+n) ≤ 2^w)
    (header : cells (guardBanks 0) = work (encodeLabel w (ustconHeaderLength s t + 1)))
    (trial : guardBanks 1 = coordBanks 4)
    (packed : ∀ j, cells (coordBanks j) = CayleyQueryCoordinates.entryCells w n p j)
    (need keep : Set (Fin W)) (disjoint : ∀ j ∈ need ∪ keep, j ∉ Set.range coordBanks)
    (ports : CrossPort address markers guardBanks coordBanks cross fit edge raw prior w B input need keep cells) :
    ∃ k d, (machine address markers guardBanks coordBanks cross fit).BoundedSegment raw B
      (start address markers guardBanks coordBanks cross fit input cells prior) d k ∧
      (machine address markers guardBanks coordBanks cross fit).step raw d = none ∧
      result address markers guardBanks coordBanks cross fit d.state =
        ustconCell (matrixBits edge) s t ((p : Int)-1) ∧ d.outputReversed = prior ∧
      ∀ j ∈ keep, d.workHead j = 0 ∧ d.workCell j = cells j := by
  let T := stages address markers guardBanks coordBanks cross fit
  let first := CayleyQueryGuard.start address markers guardBanks input cells prior
  have trialWord : cells (guardBanks 1) = work (encodeLabel w p) := by
    rw [trial, packed, offsetSlot]
  obtain ⟨a,c,guardRun,guardStop,gInput,gOutput,gHeads,gKeep,gAnswer⟩ :=
    CayleyQueryGuard.execute address markers guardBanks (matrixBits edge) s t
      (prior := prior) layout space header trialWord
  let guardExit := (A address markers guardBanks).padConfig (guardCap address markers guardBanks fit)
    allBanks ((A address markers guardBanks).bankConfig allBanks c first.workHead first.workCell)
  obtain ⟨ga,gs⟩ := exactGuard address markers guardBanks coordBanks cross fit guardRun guardStop
    (fun j => by change (0 : Int).natAbs ≤ B; simp)
  have guardFin := T.segment_component 0 ga
  have gState : guardValue address markers guardBanks guardExit.state =
      CayleyQueryGuard.result address markers guardBanks c :=
    guardValue_exact address markers guardBanks fit c
  have gHead (j : Fin W) : guardExit.workHead j = 0 :=
    (bankConfig_head_image (A address markers guardBanks) allBanks c first.workHead first.workCell j).trans
      (congrFun gHeads j)
  have gCell (j : Fin W) : guardExit.workCell j = c.workCell j :=
    bankConfig_cell_image (A address markers guardBanks) allBanks c first.workHead first.workCell j
  have gFrame (j : Fin W) (hj : j ∈ need ∪ keep) : guardExit.workCell j = cells j :=
    (gCell j).trans (gKeep j (fun equal => disjoint j hj ⟨4,trial.symm.trans equal.symm⟩))
  by_cases scope : p ≤ ustconHeaderLength s t ∨ p = ustconHeaderLength s t + (n+n)*(n+n)+1
  · rw [if_pos scope] at gAnswer
    have next : T.next 0 guardExit.state = none := by
      change (if (guardValue address markers guardBanks guardExit.state).isNone then some 1 else none) = _
      rw [gState,gAnswer]
      rfl
    have halt := T.step_halt 0 gs
    rw [next] at halt
    refine ⟨a,T.tag 0 guardExit,guardFin,halt,?_,gOutput,fun j hj => ⟨gHead j,gFrame j (.inr hj)⟩⟩
    simp only [result, Stages.tag, Equiv.symm_apply_apply, if_true, eq_self, gState, gAnswer,Option.getD_some]
  · rw [if_neg scope] at gAnswer
    have large : ustconHeaderLength s t + 1 ≤ p := by
      have h := (not_or.mp scope).1
      omega
    have small : p < ustconHeaderLength s t + (n+n)*(n+n) + 1 := by
      have h := (not_or.mp scope).2
      omega
    let r : Fin ((n+n)*(n+n)) := ⟨p-(ustconHeaderLength s t+1),by omega⟩
    let u := Division.rowOf s r
    let v := Division.colOf s r
    have packedNew (j : Fin 10) :
        guardExit.workCell (coordBanks j) = CayleyQueryCoordinates.entryCells w n r.val j := by
      rw [gCell]
      by_cases eq : j = 4
      · subst j
        rw [← trial, gAnswer.2, offsetSlot]
      · have ne : coordBanks j ≠ guardBanks 1 := fun q => eq (coordBanks.injective (q.trans trial))
        exact (gKeep _ ne).trans ((packed j).trans (offsetCell w n p r.val j eq))
    let mid := CayleyQueryCoordinates.start w n r.val input prior
    have inputBound : (-1 : Int) ≤ input ∧ input ≤ raw.length := layout.realBounds
    obtain ⟨b,e,coRun,coStop,eInput,eOutput,eHeads,ePort⟩ :=
      CayleyQueryCoordinates.executeLive s r (out := prior) inputBound mfit matrixFit
        (w := w)
    let coExit := putCoord address markers guardBanks coordBanks cross fit e guardExit.workHead guardExit.workCell
    obtain ⟨ca,cs⟩ := exactCoord address markers guardBanks coordBanks cross fit
      (PhysicalEntry.segment_mono coRun space) coStop guardExit.workHead guardExit.workCell
      (fun j => by rw [gHead]; simp)
    have coNext : T.next 0 guardExit.state = some 1 := by
      change (if (guardValue address markers guardBanks guardExit.state).isNone then some 1 else none) = _
      rw [gState,gAnswer.1]
      rfl
    have jump := T.segment_handoff (i := 0) (j := 1) gs coNext (ga.2 _ le_rfl _ ga.1)
    have coEntry := startCoord address markers guardBanks coordBanks cross fit guardExit w n r.val gHead packedNew
    rw [coEntry] at jump
    change T.machine.BoundedSegment raw B _ (T.tag 1
      (putCoord address markers guardBanks coordBanks cross fit
        (CayleyQueryCoordinates.start w n r.val c.inputHead c.outputReversed) guardExit.workHead guardExit.workCell)) 1 at jump
    rw [gInput,gOutput] at jump
    have toCoord := BoundedSegment.append _ (BoundedSegment.append _ guardFin jump)
      (T.segment_component 1 ca)
    have coHeads (j : Fin W) : coExit.workHead j = 0 := by
      by_cases hj : j ∈ Set.range coordBanks
      · obtain ⟨k,rfl⟩ := hj
        exact (bankConfig_head_image D coordBanks e guardExit.workHead guardExit.workCell k).trans (eHeads k)
      · exact (bankConfig_frame D coordBanks e guardExit.workHead guardExit.workCell hj).1.trans (gHead j)
    have coFrame (j : Fin W) (hj : j ∈ need ∪ keep) : coExit.workCell j = cells j :=
      (bankConfig_frame D coordBanks e guardExit.workHead guardExit.workCell (disjoint j hj)).2.trans
        (gFrame j hj)
    have coValue : coordValue coExit.state = CayleyQueryCoordinates.orientation e.state :=
      coordValue_exact fit e.state
    have cellEq : ustconCell (matrixBits edge) s t ((p : Int)-1) = .data (matrixBits edge u v) := by
      have ps : (p : Int)-1 = ((ustconHeaderLength s t + r.val : ℕ) : Int) := by dsimp [r]; omega
      rw [ps]
      exact Division.matrixCell (matrixBits edge) s t r
    cases ends : BipartiteCayley.endpoints (Division.rowOf s r) (Division.colOf s r) with
    | none =>
      have sides : CayleyQueryCoordinates.orientation e.state = none := by simpa only [ends] using ePort
      have next : T.next 1 coExit.state = none := by
        change (coordValue coExit.state).map fork = none
        rw [coValue,sides]
        rfl
      have halt := T.step_halt 1 cs
      rw [next] at halt
      refine ⟨_,T.tag 1 coExit,toCoord,halt,?_,eOutput,fun j hj => ⟨coHeads j,coFrame j (.inr hj)⟩⟩
      rw [cellEq]
      simp [result,Stages.tag,matrixBits,u,v,ends]
    | some pts =>
      obtain ⟨x,y⟩ := pts
      simp only [ends] at ePort
      obtain ⟨l,r,side,lword,rword⟩ := ePort
      let pair := (l,r)
      have next : T.next 1 coExit.state = some (fork pair) := by
        change (coordValue coExit.state).map fork = _
        rw [coValue,side]
        rfl
      let active := T.enter (fork pair) coExit
      have carried₁ : active.workCell (coordBanks (CayleyQueryCoordinates.slot l)) =
          work (encodeLabel w x.val) :=
        (bankConfig_cell_image D coordBanks e guardExit.workHead guardExit.workCell _).trans lword
      have carried₂ : active.workCell (coordBanks (CayleyQueryCoordinates.slot r)) =
          work (encodeLabel w y.val) :=
        (bankConfig_cell_image D coordBanks e guardExit.workHead guardExit.workCell _).trans rword
      obtain ⟨lastTicks,last,lastRun,lastHalt,lastBit,lastOut,lastFrame⟩ :=
        ports pair x y active rfl eInput eOutput coHeads carried₁ carried₂ coFrame
      have jumpCross := T.segment_handoff (i := 1) (j := fork pair) cs next (ca.2 _ le_rfl _ ca.1)
      have full := BoundedSegment.append _ (BoundedSegment.append _ toCoord jumpCross)
        (T.segment_component (fork pair) lastRun)
      have lastNext : T.next (fork pair) last.state = none := by
        simp [T, fork_nonzero, fork_nonone]
      have halt := T.step_halt (fork pair) lastHalt
      rw [lastNext] at halt
      refine ⟨_,T.tag (fork pair) last,full,halt,?_,lastOut,lastFrame⟩
      rw [cellEq,show matrixBits edge u v = edge x y from by simp [matrixBits,u,v,ends]]
      simp only [result,Stages.tag, Equiv.symm_apply_apply, fork_nonzero, fork_nonone, if_false,
        unfork_fork,lastBit]

end Mathproof.MinimumGeneration.CayleyQueryRouter
