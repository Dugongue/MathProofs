import Mathproof.MinimumGenerationCayleyReaderParked
import Mathproof.MinimumGenerationCayleyReaderRestoreSeek

namespace Mathproof.MinimumGeneration.CayleyReaderCycle

open SearchTransducer
open CayleyQueryPrefixModel (rawSpace)

set_option backward.isDefEq.respectTransparency false

abbrev A := CayleyReaderRestoreSeek.machine
abbrev B := CayleyReaderParked.machine

/-- Reader scratch and companion tracks occupy the first 70 banks. -/
def readerBanks : Fin B.workTapes ↪ Fin 74 :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun i : Fin 74 => i.val) h)⟩

/-- The restore helper's immutable clock, orders, and blank reference follow
the companion tracks. Its first 35 banks are the live reader data. -/
def restoreBanks : Fin A.workTapes ↪ Fin 74 where
  toFun i := ⟨if i.val < 35 then i.val else i.val+35, by
    have hi := i.isLt
    change i.val < 39 at hi
    split <;> omega⟩
  inj' i j h := by
    have e := congrArg (fun a : Fin 74 => a.val) h
    change (if i.val < 35 then i.val else i.val+35) =
      (if j.val < 35 then j.val else j.val+35) at e
    exact Fin.ext (by split at e <;> split at e <;> omega)

def originalBank (i : Fin 35) : Fin 74 := readerBanks (Fin.castAdd 35 i)
def shadowBank (i : Fin 35) : Fin 74 := readerBanks (Fin.natAdd 35 i)

private theorem originalBank_restore (i : Fin 35) :
    restoreBanks (CayleyReaderRestore.readerBanks i) = originalBank i := by
  apply Fin.ext
  change (if i.val < 35 then i.val else i.val+35) = i.val
  rw [if_pos i.isLt]

private theorem shadow_out (i : Fin 35) : shadowBank i ∉ Set.range restoreBanks := by
  rintro ⟨j,h⟩
  have e := congrArg (fun k : Fin 74 => k.val) h
  change (if j.val < 35 then j.val else j.val+35) = 35+i.val at e
  have hi := i.isLt
  split at e <;> omega

private theorem helper_out {j : Fin A.workTapes} (h : 35 ≤ j.val) :
    restoreBanks j ∉ Set.range readerBanks := by
  rintro ⟨i,he⟩
  have e := congrArg (fun k : Fin 74 => k.val) he
  change i.val = (if j.val < 35 then j.val else j.val+35) at e
  have hi := i.isLt
  change i.val < 70 at hi
  rw [if_neg (by omega)] at e
  omega

abbrev machine := thenMachine A B restoreBanks readerBanks

abbrev callback : VirtualCallbackDriver.Callback :=
  ⟨machine, fun state =>
    (finSumFinEquiv.symm state).elim (fun _ => .leftEnd) CayleyReaderParked.callback.returnCell⟩

structure Ready {n : Nat} (G : Group (Fin n)) (cut : Nat) (s t : Fin (n+n))
    (p : Nat) (ticks : List Bool) (old : Fin 74 → Int → Option Bool) : Prop where
  body : CayleyReaderRestore.Ready G cut s t p ticks (fun i => old (restoreBanks i))
  shadows : ∀ j, old (shadowBank j) = ParkOrigin.origin

def start (input : Int) (prior : List Bool) (old : Fin 74 → Int → Option Bool) :
    machine.Config :=
  thenLeft A B restoreBanks readerBanks
    (A.bankConfig restoreBanks (CayleyReaderRestoreSeek.start input prior (fun i => old (restoreBanks i)))
      (fun _ => 0) old)

private theorem eqConfig {R : SearchTransducer} (c d : R.Config)
    (s : c.state = d.state) (i : c.inputHead = d.inputHead) (h : c.workHead = d.workHead)
    (z : c.workCell = d.workCell) (o : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

theorem startSpec (input : Int) (prior : List Bool) (old : Fin 74 → Int → Option Bool) :
    let c := start input prior old
    c.state = machine.initialState ∧ c.inputHead = input ∧ c.outputReversed = prior ∧
      (∀ i, c.workHead i = 0) ∧ c.workCell = old := by
  let a := CayleyReaderRestoreSeek.start input prior (fun i => old (restoreBanks i))
  have spec := CayleyReaderRestoreSeek.startSpec input prior (fun i => old (restoreBanks i))
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro i
    change (A.bankConfig restoreBanks a (fun _ => 0) old).workHead i = 0
    by_cases hi : i ∈ Set.range restoreBanks
    · obtain ⟨j,rfl⟩ := hi
      exact (A.bankConfig_head_image restoreBanks a (fun _ => 0) old j).trans (spec.2.2.2.1 j)
    · exact (A.bankConfig_frame restoreBanks a (fun _ => 0) old hi).1
  · funext i
    change (A.bankConfig restoreBanks a (fun _ => 0) old).workCell i = old i
    by_cases hi : i ∈ Set.range restoreBanks
    · obtain ⟨j,rfl⟩ := hi
      exact (A.bankConfig_cell_image restoreBanks a (fun _ => 0) old j).trans (congrFun spec.2.2.2.2 j)
    · exact (A.bankConfig_frame restoreBanks a (fun _ => 0) old hi).2

/-- Reset the coordinate window, seek to the table, read one virtual cell
and park the reader. The same readiness invariant holds on return. -/
theorem execute {n : Nat} (G : Group (Fin n)) (cut : Nat) (hCut : cut ≤ n)
    (s t : Fin (n+n)) (p : Nat) (prior ticks : List Bool) (input : Int)
    (old : Fin 74 → Int → Option Bool) (ready : Ready G cut s t p ticks old)
    (inLegal : (-1 : Int) ≤ input ∧ input ≤ (@encodeCayley n G.toMul).length)
    (virtualLegal : p ≤ Connectivity.ustconHeaderLength s t+(n+n)*(n+n)+1) :
    let raw := @encodeCayley n G.toMul
    ∃ k d, machine.BoundedSegment raw (ticks.length+1) (start input prior old) d k ∧
      machine.step raw d = none ∧
      callback.returnCell d.state =
        Connectivity.ustconCell (BipartiteCayley.bits G (fun _ => true) cut) s t ((p : Int)-1) ∧
      d.outputReversed = prior ∧ (∀ j, d.workHead j = 0) ∧
      (-1 : Int) ≤ d.inputHead ∧ d.inputHead ≤ (raw.length : Int) ∧
      Ready G cut s t p ticks d.workCell := by
  let raw := @encodeCayley n G.toMul
  let parked : Fin 74 → Int := fun _ => 0
  obtain ⟨a, reset, resetRun, resetStop, resetInput, resetOut, resetHeads, initialized, saved⟩ :=
    CayleyReaderRestoreSeek.execute G cut s t p input prior ticks _ ready.body inLegal
  let mid := A.bankConfig restoreBanks reset parked old
  have first := A.relocateBanks_segment restoreBanks resetRun (heads := parked) (cells := old)
    (fun _ _ => Nat.zero_le _)
  have stopsA : (A.relocateBanks restoreBanks).step raw mid = none := by
    unfold mid
    rw [relocateBanks_step,resetStop]
    rfl
  have midHeads (j : Fin 74) : mid.workHead j = 0 := by
    by_cases h : j ∈ Set.range restoreBanks
    · obtain ⟨i,rfl⟩ := h
      exact (A.bankConfig_head_image restoreBanks reset parked old i).trans (resetHeads i)
    · exact (A.bankConfig_frame restoreBanks reset parked old h).1
  have midFixed (i : Fin A.workTapes) (hi : 35 ≤ i.val) :
      mid.workCell (restoreBanks i) = old (restoreBanks i) :=
    (A.bankConfig_cell_image restoreBanks reset parked old i).trans (saved i hi)
  have midOriginal (i : Fin 35) :
      mid.workCell (originalBank i) = CayleyQueryPrefixModel.cells G cut s t p i := by
    rw [← originalBank_restore, bankConfig_cell_image]
    exact initialized i
  have midShadow (i : Fin 35) : mid.workCell (shadowBank i) = ParkOrigin.origin :=
    (A.bankConfig_frame restoreBanks reset parked old (shadow_out i)).2.trans (ready.shadows i)
  obtain ⟨b, last, query, queryStop, answer, queryOut, queryHeads, kept, exterior, shadow, lo, hi⟩ :=
    CayleyReaderParked.execute G cut hCut s t p prior virtualLegal
  let launch := CayleyReaderParked.start G cut s t p prior
  have spec := CayleyReaderParked.startSpec G cut s t p prior
  let entry := B.bankConfig readerBanks launch mid.workHead mid.workCell
  let finish := B.bankConfig readerBanks last mid.workHead mid.workCell
  have afterRun := B.relocateBanks_segment readerBanks
    (PhysicalEntry.segment_mono query (Nat.le_succ_of_le ready.body.clockEnough))
    (heads := mid.workHead) (cells := mid.workCell) (fun j _ => by rw [midHeads]; exact Nat.zero_le _)
  have join : thenEntry A B restoreBanks readerBanks mid = entry := by
    apply eqConfig
    · exact spec.1.symm
    · exact resetInput.trans spec.2.1.symm
    · funext j
      by_cases h : j ∈ Set.range readerBanks
      · obtain ⟨i,rfl⟩ := h
        rw [show entry.workHead (readerBanks i) = launch.workHead i from
          B.bankConfig_head_image readerBanks launch _ _ i, spec.2.2.2.1]
        exact midHeads _
      · exact (B.bankConfig_frame readerBanks launch _ _ h).1.symm
    · funext j
      by_cases h : j ∈ Set.range readerBanks
      · obtain ⟨i,rfl⟩ := h
        rw [show entry.workCell (readerBanks i) = launch.workCell i from
          B.bankConfig_cell_image readerBanks launch _ _ i]
        refine Fin.addCases (fun r => ?_) (fun r => ?_) i
        · exact (midOriginal r).trans (spec.2.2.2.2.1 r).symm
        · exact (midShadow r).trans (spec.2.2.2.2.2 r).symm
      · exact (B.bankConfig_frame readerBanks launch _ _ h).2.symm
    · exact resetOut.trans spec.2.2.1.symm
  change (B.relocateBanks readerBanks).BoundedSegment raw _ entry finish b at afterRun
  rw [← join] at afterRun
  let d := thenRight A B restoreBanks readerBanks finish
  have fixed (j : Fin A.workTapes) (hj : 35 ≤ j.val) :
      d.workCell (restoreBanks j) = old (restoreBanks j) :=
    (B.bankConfig_frame readerBanks last mid.workHead mid.workCell (helper_out hj)).2.trans
      (midFixed j hj)
  have original (j : Fin 35) :
      d.workCell (originalBank j) = last.workCell (Fin.castAdd 35 j) :=
    B.bankConfig_cell_image readerBanks last mid.workHead mid.workCell _
  refine ⟨a+1+b,d,thenSegment A B restoreBanks readerBanks first stopsA afterRun,?_,?_,queryOut,?_,lo,hi,?_⟩
  · change machine.step raw (thenRight A B restoreBanks readerBanks finish) = none
    rw [thenStep_right]
    unfold finish
    rw [relocateBanks_step,queryStop]
    rfl
  · change (finSumFinEquiv.symm (Fin.natAdd A.states last.state)).elim
      (fun _ => InputCell.leftEnd) CayleyReaderParked.callback.returnCell = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    exact answer
  · intro j
    by_cases h : j ∈ Set.range readerBanks
    · obtain ⟨i,rfl⟩ := h
      exact (B.bankConfig_head_image readerBanks last mid.workHead mid.workCell i).trans (congrFun queryHeads i)
    · exact (B.bankConfig_frame readerBanks last mid.workHead mid.workCell h).1.trans (midHeads j)
  · constructor
    · exact ⟨(fixed 35 (by decide)).trans ready.body.clockWord, ready.body.clockEnough,
        (fixed 36 (by decide)).trans ready.body.cardinality,
        (fixed 37 (by decide)).trans ready.body.order, (fixed 38 (by decide)).trans ready.body.clean,
        fun j hj => by rw [originalBank_restore,original]; exact kept j hj,
        fun j z hz => by rw [originalBank_restore, original]; exact exterior j z hz⟩
    · intro i
      exact (B.bankConfig_cell_image readerBanks last mid.workHead mid.workCell (Fin.natAdd 35 i)).trans (shadow i)

end Mathproof.MinimumGeneration.CayleyReaderCycle
