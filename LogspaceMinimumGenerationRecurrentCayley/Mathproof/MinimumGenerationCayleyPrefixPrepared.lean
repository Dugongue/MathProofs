import Mathproof.MinimumGenerationCayleyPrefixEntryInstall

namespace Mathproof.MinimumGeneration.CayleyPrefixLeaf

open SearchTransducer

set_option backward.isDefEq.respectTransparency false

private def allBanks : Fin 18 ↪ Fin 18 := Function.Embedding.refl _

abbrev preparedMachine := thenMachine installMachine machine allBanks prefixBanks

def preparedStart (n : Nat) (cells : Fin 18 → Int → Option Bool) (prior : List Bool) :
    preparedMachine.Config :=
  let c := TapeInstall.start (11 : Fin 18) copySource (↑(n+1 : Nat)) cells prior
  thenLeft installMachine machine allBanks prefixBanks
    (installMachine.bankConfig allBanks c c.workHead c.workCell)

def preparedBit (c : preparedMachine.Config) : Bool :=
  match finSumFinEquiv.symm c.state with
  | .inl _ => false
  | .inr q =>
    match finSumFinEquiv.symm q with
    | .inl _ => false
    | .inr v => bit v

private theorem eq_config {M : SearchTransducer} (c d : M.Config)
    (s : c.state = d.state) (i : c.inputHead = d.inputHead) (h : c.workHead = d.workHead)
    (t : c.workCell = d.workCell) (o : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem width_bound {n : Nat} (M : Mul (Fin n)) :
    2 * TableIO.width n + 1 ≤ 3 * (Nat.log2 ((@encodeCayley n M).length + 1) + 1) := by
  have hN : n ≤ (@encodeCayley n M).length := by
    rw [@length_encodeCayley n M]
    omega
  have z : n.log2 ≤ ((@encodeCayley n M).length + 1).log2 := by
    by_cases h : n = 0
    · simp [h]
    · apply (Nat.le_log2 (by omega)).2
      exact (Nat.log2_self_le h).trans (by omega)
  unfold TableIO.width
  omega

/-- A concrete controller joins register installation to the Cayley-table
lookup and its identity-or-prefix test. -/
theorem executeFromTemplates {n : Nat} (G : Group (Fin n)) (x y : Fin n) (cut : Nat)
    (hcut : cut ≤ n) (prior : List Bool) (cells : Fin 18 → Int → Option Bool)
    (ready : Templates n x.val y.val G.toOne.one.val cut cells) :
    let word := @encodeCayley n G.toMul
    let B := 3 * (Nat.log2 (word.length + 1) + 1)
    ∃ k d, preparedMachine.BoundedSegment word B (preparedStart n cells prior) d k ∧
      preparedMachine.step word d = none ∧
      (preparedBit d = true ↔
        ReingoldLiveInput.difference G x y = G.toOne.one ∨
          (ReingoldLiveInput.difference G x y).val < cut) ∧
      d.outputReversed = prior ∧ ∀ j : Fin 18, 11 ≤ j.val → d.workHead j = 0 ∧ d.workCell j = cells j := by
  let word := @encodeCayley n G.toMul
  let w := TableIO.width n
  let cursor : Int := ↑(n+1 : Nat)
  let init := TapeInstall.start (11 : Fin 18) copySource cursor cells prior
  let installed := TapeInstall.stop (11 : Fin 18) copySource cursor cells prior (2*w)
  obtain ⟨install, haltI, registers, frames⟩ := executeInstall G.toMul x.val y.val G.toOne.one.val cut cells prior ready
  have initSeg := installMachine.relocateBanks_segment allBanks
    (PhysicalEntry.segment_mono install (width_bound G.toMul))
        (heads := init.workHead) (cells := init.workCell) (by
      intro j _
      change (0 : Int).natAbs ≤ _
      exact Nat.zero_le _)
  let intermediate := installMachine.bankConfig allBanks installed init.workHead init.workCell
  have haltI' : (installMachine.relocateBanks allBanks).step word intermediate = none := by
    unfold intermediate
    rw [relocateBanks_step, haltI]
    rfl
  obtain ⟨k, v, out, run, hStop, state, answer, print⟩ := execute G x y cut hcut prior
  let entry' := entry n x.val y.val G.toOne.one.val cut prior
  have shape := entry_layout n x.val y.val G.toOne.one.val cut prior
  let framedIn := machine.bankConfig prefixBanks entry' intermediate.workHead intermediate.workCell
  let framedOut := machine.bankConfig prefixBanks out intermediate.workHead intermediate.workCell
  have installedHead (i : Fin 18) : intermediate.workHead i = 0 :=
    installMachine.bankConfig_head_image allBanks installed init.workHead init.workCell i
  have installedCell (i : Fin 18) : intermediate.workCell i = installed.workCell i :=
    installMachine.bankConfig_cell_image allBanks installed init.workHead init.workCell i
  have joined : thenEntry installMachine machine allBanks prefixBanks intermediate = framedIn := by
    apply eq_config
    · exact shape.1.symm
    · exact shape.2.1.symm
    · funext i
      by_cases hi : i ∈ Set.range prefixBanks
      · obtain ⟨j,rfl⟩ := hi
        rw [show framedIn.workHead (prefixBanks j) = entry'.workHead j from
          machine.bankConfig_head_image prefixBanks entry' _ _ j]
        exact (installedHead _).trans (congrFun shape.2.2.1 j).symm
      · exact (machine.bankConfig_frame prefixBanks entry' _ _ hi).1.symm
    · funext i
      by_cases hi : i ∈ Set.range prefixBanks
      · obtain ⟨j,rfl⟩ := hi
        rw [show framedIn.workCell (prefixBanks j) = entry'.workCell j from
          machine.bankConfig_cell_image prefixBanks entry' _ _ j]
        exact (installedCell _).trans ((registers j).trans (congrFun shape.2.2.2.1 j).symm)
      · exact (machine.bankConfig_frame prefixBanks entry' _ _ hi).2.symm
    · exact shape.2.2.2.2.symm
  have leafSeg := machine.relocateBanks_segment prefixBanks run
    (heads := intermediate.workHead) (cells := intermediate.workCell)
    (fun j _ => by rw [installedHead j]; simp)
  change (machine.relocateBanks prefixBanks).BoundedSegment word _ framedIn framedOut k at leafSeg
  rw [← joined] at leafSeg
  let d := thenRight installMachine machine allBanks prefixBanks framedOut
  refine ⟨_, d, thenSegment installMachine machine allBanks prefixBanks initSeg haltI' leafSeg,
    ?_, ?_, print, ?_⟩
  · change preparedMachine.step word (thenRight installMachine machine allBanks prefixBanks framedOut) = none
    rw [thenStep_right]
    unfold framedOut
    rw [relocateBanks_step, hStop]
    rfl
  · have state' : d.state = Fin.natAdd installMachine.states (Fin.natAdd
        OuterCayleyQuery.solver.states v) := congrArg (Fin.natAdd installMachine.states) state
    unfold preparedBit
    simpa only [state', finSumFinEquiv_symm_apply_natAdd] using answer
  · intro j jmin
    have notTarget : j ∉ Set.range prefixBanks := by
      rintro ⟨i, rfl⟩
      have small : (prefixBanks i).val < 11 := i.isLt
      omega
    obtain ⟨h, b⟩ := machine.bankConfig_frame prefixBanks out intermediate.workHead intermediate.workCell notTarget
    exact ⟨h.trans (installedHead j), b.trans ((installedCell j).trans (frames j jmin))⟩

end Mathproof.MinimumGeneration.CayleyPrefixLeaf
