import Mathproof.MinimumGenerationRawIdentity
import Mathproof.MinimumGenerationPhysicalGreedyTemplateSetup
import Mathproof.MinimumGenerationPhysicalGreedyPrefixCall

namespace Mathproof.MinimumGeneration.PhysicalGreedyTemplateFromRaw

open SearchTransducer
open PhysicalGreedyTemplateCompose (cfg configEq)
open PhysicalGreedyTemplateSetup (Bank entryData outputData checkoutBanks)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev R := RawIdentity.machine
abbrev S := PhysicalGreedyTemplateSetup.machine.native

def rawBanks : Fin R.workTapes ↪ Bank :=
  ⟨fun i => if i=0 then 0 else if i=1 then 1 else if i=2 then 17 else 2, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def setupBanks : Fin S.workTapes ↪ Bank := Function.Embedding.refl _

abbrev machine := thenMachine R S rawBanks setupBanks

private def parked : Bank → Int := fun _ => 0
private def blank : Bank → Int → Option Bool := fun _ _ => none

private theorem full_head (c : S.Config) :
    (S.bankConfig setupBanks c parked blank).workHead = c.workHead := by
  funext j
  exact S.bankConfig_head_image setupBanks c parked blank j

private theorem full_cell (c : S.Config) :
    (S.bankConfig setupBanks c parked blank).workCell = c.workCell := by
  funext j
  exact S.bankConfig_cell_image setupBanks c parked blank j

/-- From the actual encoded Cayley table and blank work tapes, install the
entire one-time header state. No order, identity, width or templates are
supplied on work tapes. -/
theorem execute {n : Nat} (G : Group (Fin n)) :
    let raw := @encodeCayley n G.toMul
    let B := 5*(Nat.log2 (raw.length+1)+1)
    ∃ (ticks : Nat) (d : machine.Config),
      machine.BoundedSegment raw B machine.initial d ticks ∧ machine.step raw d = none ∧
      machine.logarithmicWorkspace 5 raw ∧ d.workHead = (fun _ => 0) ∧ d.outputReversed = [] ∧
      d.workCell = outputData n G.toOne.one.val 0 := by
  let raw := @encodeCayley n G.toMul
  let L := Nat.log2 (raw.length+1)+1
  let B := 5*L
  obtain ⟨k,e,r,h,he,oe,ce⟩ := RawIdentity.physicalFrameFromRaw n G
  have h₀ := PhysicalEntry.segment_mono r (by show 2*L ≤ B; dsimp [B]; omega)
  have inState := r.2 k le_rfl e r.1
  obtain ⟨l,q,s,st⟩ := PhysicalGreedyTemplateSetup.execute G.toOne.one 0 (prior := [])
    (show (-1 : Int) ≤ e.inputHead ∧ e.inputHead ≤ raw.length from ⟨inState.1,inState.2.1⟩)
  let b := R.bankConfig rawBanks e parked blank
  let a := R.bankConfig rawBanks R.initial parked blank
  let c₀ := cfg PhysicalGreedyTemplateSetup.machine S.initialState e.inputHead []
    (entryData n G.toOne.one.val 0)
  let d₀ := cfg PhysicalGreedyTemplateSetup.machine q e.inputHead []
    (outputData n G.toOne.one.val 0)
  let c := S.bankConfig setupBanks c₀ parked blank
  let d := S.bankConfig setupBanks d₀ parked blank
  have setupBound : PhysicalGreedyHeader.width n+1 ≤ B := PhysicalGreedyHeaderDriver.raw_bound G
  have left := R.relocateBanks_segment rawBanks h₀ (heads := parked) (cells := blank) (by simp [parked])
  have right := S.relocateBanks_segment setupBanks (PhysicalEntry.segment_mono s setupBound)
    (heads := parked) (cells := blank) (by simp [parked])
  have leftStop : (R.relocateBanks rawBanks).step raw b = none := by
    unfold b
    rw [relocateBanks_step,h]
    rfl
  have rightStop : (S.relocateBanks setupBanks).step raw d = none := by
    unfold d d₀
    rw [relocateBanks_step,st]
    rfl
  have bpark : b.workHead = parked := by
    funext i
    by_cases hi : i ∈ Set.range rawBanks
    · obtain ⟨j,rfl⟩ := hi
      exact (R.bankConfig_head_image rawBanks e parked blank j).trans (congrFun he j)
    · exact (R.bankConfig_frame rawBanks e parked blank hi).1
  have bcells : b.workCell = entryData n G.toOne.one.val 0 := by
    funext i
    by_cases hi : i ∈ Set.range rawBanks
    · obtain ⟨j,rfl⟩ := hi
      rw [show b.workCell (rawBanks j) = e.workCell j from R.bankConfig_cell_image rawBanks e parked blank j,ce]
      fin_cases j <;> rfl
    · have h0 : i ≠ 0 := fun eq => hi ⟨0,eq.symm⟩
      have h1 : i ≠ 1 := fun eq => hi ⟨1,eq.symm⟩
      have h2 : i ≠ 2 := fun eq => hi ⟨3,eq.symm⟩
      have h17 : i ≠ 17 := fun eq => hi ⟨2,eq.symm⟩
      exact (R.bankConfig_frame rawBanks e parked blank hi).2.trans (by
        change (fun _ => (none : Option Bool)) = entryData n G.toOne.one.val 0 i
        simp [entryData,h0,h1,h2,h17])
  have blankStart : machine.initial = thenLeft R S rawBanks setupBanks a := by
    apply configEq
    · rfl
    · rfl
    · funext i
      by_cases hi : i ∈ Set.range rawBanks
      · obtain ⟨j,rfl⟩ := hi
        exact (R.bankConfig_head_image rawBanks R.initial parked blank j).symm
      · exact (R.bankConfig_frame rawBanks R.initial parked blank hi).1.symm
    · funext i
      by_cases hi : i ∈ Set.range rawBanks
      · obtain ⟨j,rfl⟩ := hi
        exact (R.bankConfig_cell_image rawBanks R.initial parked blank j).symm
      · exact (R.bankConfig_frame rawBanks R.initial parked blank hi).2.symm
    · rfl
  have handoff : thenEntry R S rawBanks setupBanks b = c := by
    apply configEq
    · rfl
    · rfl
    · exact bpark.trans (full_head c₀).symm
    · exact bcells.trans (full_cell c₀).symm
    · exact oe
  change (S.relocateBanks setupBanks).BoundedSegment raw B c d l at right
  rw [← handoff] at right
  have all := thenSegment R S rawBanks setupBanks left leftStop right
  change machine.BoundedSegment raw B (thenLeft R S rawBanks setupBanks a)
    (thenRight R S rawBanks setupBanks d) _ at all
  rw [← blankStart] at all
  have halt : machine.step raw (thenRight R S rawBanks setupBanks d) = none := by
    rw [thenStep_right,rightStop]
    rfl
  refine ⟨_,thenRight R S rawBanks setupBanks d,all,halt,
    (BoundedSegment.logspaceOutput machine all halt).1,full_head d₀,rfl,full_cell d₀⟩

/-- The initialized header projection matches the saved frame of the
physical prefix-call adapter under arbitrary relocation. -/
theorem saved_frame (P : SearchTransducer) (e : PhysicalGreedyHeaderInstall.Bank ↪ Fin P.workTapes)
    (n id label : Nat) (m : Fin P.workTapes → Int → Option Bool)
    (view : ∀ j, m (e j) = outputData n id label (checkoutBanks j)) :
    ∀ j ∈ PhysicalGreedyPrefixCall.required P e,
      m j = PhysicalGreedyPrefixCall.saved P e n id j := by
  classical
  intro j hj
  obtain ⟨i,lb,rfl⟩ := hj
  rw [view]
  unfold PhysicalGreedyPrefixCall.saved
  have inRange : e i ∈ Set.range e := ⟨i,rfl⟩
  rw [dif_pos inRange]
  have chooseI : Classical.choose inRange = i := e.injective (Classical.choose_spec inRange)
  rw [chooseI]
  fin_cases i <;> first | rfl | contradiction

end Mathproof.MinimumGeneration.PhysicalGreedyTemplateFromRaw
