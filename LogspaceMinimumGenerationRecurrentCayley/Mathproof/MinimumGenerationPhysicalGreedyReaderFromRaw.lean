import Mathproof.MinimumGenerationPhysicalGreedyReaderSetup

namespace Mathproof.MinimumGeneration.PhysicalGreedyReaderFromRaw

open SearchTransducer
open PhysicalGreedyTemplateCompose (cfg configEq)
open PhysicalGreedyReaderSetup (Bank reader header headerOnly outputData initialLabel)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4096

abbrev A := PhysicalGreedyTemplateFromRaw.machine
abbrev B := PhysicalGreedyReaderSetup.machine.native

def same : Fin B.workTapes ↪ Bank := Function.Embedding.refl _

abbrev machine := thenMachine A B header same

private def parked : Bank → Int := fun _ => 0
private def blank : Bank → Int → Option Bool := fun _ _ => none

private theorem headProjection (c : B.Config) :
    (B.bankConfig same c parked blank).workHead = c.workHead := by
  funext i
  exact B.bankConfig_head_image same c parked blank i

private theorem cellProjection (c : B.Config) :
    (B.bankConfig same c parked blank).workCell = c.workCell := by
  funext i
  exact B.bankConfig_cell_image same c parked blank i

private theorem spaceBound {n : Nat} (G : Group (Fin n)) :
    PhysicalGreedyReaderSetup.space n ≤
      17*(Nat.log2 ((@encodeCayley n G.toMul).length+1)+1) := by
  let raw := @encodeCayley n G.toMul
  have h : n ≤ raw.length := by
    change n ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have log : n.log2 ≤ (raw.length+1).log2 :=
    (Nat.le_log2 (by omega)).2
      ((Nat.log2_self_le (by have := G.toOne.one.isLt; omega)).trans (by omega))
  have eq : (CayleyReaderClock.bits n).length = 16*TableIO.width n := length_encodeLabel _ _
  rw [PhysicalGreedyReaderSetup.space,eq,TableIO.width]
  change 16*(n.log2+1)+1 ≤ 17*((raw.length+1).log2+1)
  omega

/-- A single blank-start transducer prepares the actual recurrent prefix
reader and the candidate-header source banks from the raw Cayley table. -/
theorem execute {n : Nat} (G : Group (Fin n)) :
    let raw := @encodeCayley n G.toMul
    let budget := 17*(Nat.log2 (raw.length+1)+1)
    ∃ (k : Nat) (d : machine.Config),
      machine.BoundedSegment raw budget machine.initial d k ∧ machine.step raw d = none ∧
      machine.logarithmicWorkspace 17 raw ∧ d.workHead = (fun _ => 0) ∧ d.outputReversed = [] ∧
      d.workCell = outputData n G.toOne.one.val ∧
      (∀ j, d.workCell (header j) = PhysicalGreedyTemplateSetup.outputData n G.toOne.one.val 0 j) ∧
      CayleyReaderCycle.Ready G 0 (BipartiteCayley.left G.toOne.one)
        (BipartiteCayley.left (initialLabel G)) 1 (CayleyReaderClock.bits n)
        (fun i => d.workCell (reader i)) := by
  let raw := @encodeCayley n G.toMul
  let id := G.toOne.one.val
  let L := Nat.log2 (raw.length+1)+1
  let cap := 17*L
  obtain ⟨k,a,init,done,_,heads,out,words⟩ := PhysicalGreedyTemplateFromRaw.execute G
  have pos := init.2 k le_rfl a init.1
  obtain ⟨l,q,r,stop⟩ := PhysicalGreedyReaderSetup.execute G (prior := [])
    (pos := a.inputHead) ⟨pos.1,pos.2.1⟩
  let a' := A.bankConfig header a parked blank
  let c := cfg PhysicalGreedyReaderSetup.machine B.initialState a.inputHead [] (headerOnly n id)
  let d := cfg PhysicalGreedyReaderSetup.machine q a.inputHead [] (outputData n id)
  let c' := B.bankConfig same c parked blank
  let d' := B.bankConfig same d parked blank
  have ra := A.relocateBanks_segment header (PhysicalEntry.segment_mono init (show 5*L ≤ cap by
    dsimp [cap]; omega)) (heads := parked) (cells := blank) (by simp [parked])
  have rb := B.relocateBanks_segment same (PhysicalEntry.segment_mono r (spaceBound G))
    (heads := parked) (cells := blank) (by simp [parked])
  have doneA : (A.relocateBanks header).step raw a' = none := by
    unfold a'
    rw [relocateBanks_step,done]
    rfl
  have doneB : (B.relocateBanks same).step raw d' = none := by
    unfold d' d
    rw [relocateBanks_step,stop]
    rfl
  have aHead : a'.workHead = parked := by
    funext i
    by_cases hi : i ∈ Set.range header
    · obtain ⟨j,rfl⟩ := hi
      exact (A.bankConfig_head_image header a parked blank j).trans (congrFun heads j)
    · exact (A.bankConfig_frame header a parked blank hi).1
  have aCell : a'.workCell = headerOnly n id := by
    funext i
    by_cases hi : i ∈ Set.range header
    · obtain ⟨j,rfl⟩ := hi
      exact (A.bankConfig_cell_image header a parked blank j).trans
        ((congrFun words j).trans (PhysicalGreedyReaderSetup.headerOnly_at n id j).symm)
    · have h : ¬(74 ≤ i.val ∧ i.val < 92) := fun h => by
        let j : Fin 18 := ⟨i.val-74,by omega⟩
        exact hi ⟨j,Fin.ext (by change 74+(i.val-74) = i.val; omega)⟩
      exact (A.bankConfig_frame header a parked blank hi).2.trans (by
        change (fun _ => (none : Option Bool)) = headerOnly n id i
        rw [headerOnly,dif_neg h])
  have initialState : machine.initial =
      thenLeft A B header same (A.bankConfig header A.initial parked blank) := by
    apply configEq
    · rfl
    · rfl
    · funext i
      by_cases hi : i ∈ Set.range header
      · obtain ⟨j,rfl⟩ := hi
        exact (A.bankConfig_head_image header A.initial parked blank j).symm
      · exact (A.bankConfig_frame header A.initial parked blank hi).1.symm
    · funext i
      by_cases hi : i ∈ Set.range header
      · obtain ⟨j,rfl⟩ := hi
        exact (A.bankConfig_cell_image header A.initial parked blank j).symm
      · exact (A.bankConfig_frame header A.initial parked blank hi).2.symm
    · rfl
  have handoff : thenEntry A B header same a' = c' := by
    apply configEq
    · rfl
    · rfl
    · exact aHead.trans (headProjection c).symm
    · exact aCell.trans (cellProjection c).symm
    · exact out
  change (B.relocateBanks same).BoundedSegment raw cap c' d' l at rb
  rw [← handoff] at rb
  have run := thenSegment A B header same ra doneA rb
  change machine.BoundedSegment raw cap
    (thenLeft A B header same (A.bankConfig header A.initial parked blank))
    (thenRight A B header same d') _ at run
  rw [← initialState] at run
  have halt : machine.step raw (thenRight A B header same d') = none := by
    rw [thenStep_right,doneB]
    rfl
  let e := thenRight A B header same d'
  have data : e.workCell = outputData n id := cellProjection d
  have logspace : machine.logarithmicWorkspace 17 raw := (BoundedSegment.logspaceOutput machine run halt).1
  refine ⟨_,e,run,halt,logspace,headProjection d,rfl,data,?_,?_⟩
  · intro j
    rw [data]
    exact PhysicalGreedyReaderSetup.header_preserved n id j
  · rw [data]
    exact PhysicalGreedyReaderSetup.ready G

end Mathproof.MinimumGeneration.PhysicalGreedyReaderFromRaw
