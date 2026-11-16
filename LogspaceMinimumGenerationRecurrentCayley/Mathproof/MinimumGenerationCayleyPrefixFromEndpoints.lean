import Mathproof.MinimumGenerationCayleyPrefixEndpointInstall

namespace Mathproof.MinimumGeneration.CayleyPrefixLeaf

open SearchTransducer
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

variable {W : Nat} (e : Fin 18 ↪ Fin W) (leftSource rightSource : Fin W)

private def allBanks : Fin W ↪ Fin W := Function.Embedding.refl _

abbrev crossMachine := thenMachine (endpointsMachine e leftSource rightSource) preparedMachine allBanks e

def crossStart (n : Nat) (cells : Fin W → Int → Option Bool) (prior : List Bool) :
    (crossMachine e leftSource rightSource).Config :=
  let P := endpointsMachine e leftSource rightSource
  let c := endpointsStart e leftSource rightSource n cells prior
  thenLeft P preparedMachine allBanks e (P.bankConfig allBanks c c.workHead c.workCell)

def crossBit (q : Fin (crossMachine e leftSource rightSource).states) : Bool :=
  match finSumFinEquiv.symm q with
  | .inl _ => false
  | .inr p => preparedBit ⟨p, 0, fun _ => 0, fun _ _ => none, []⟩

/-- The stationary templates are held in the reader's own banks. Scratch
contents inside each marked register may be arbitrary before its update. -/
structure EndpointTemplates (n x y identity cut width : Nat)
    (cells : Fin W → Int → Option Bool) : Prop where
  wide : 2 * TableIO.width n ≤ width
  leftWord : cells leftSource = work (encodeLabel width x)
  rightWord : cells rightSource = work (encodeLabel width y)
  noTargetAlias : rightSource ≠ e 12
  immutable : ∀ i : Fin 18, 11 ≤ i.val → i ≠ 12 → i ≠ 15 →
    cells (e i) = template n x y identity cut i
  rowBoundary : ∀ p : Int, p < 1 ∨ (2 * TableIO.width n : Nat) < p → cells (e 12) p = none
  targetBoundary : ∀ p : Int, p < 1 ∨ (TableIO.width n : Nat) < p → cells (e 15) p = none
  scratchBoundary : ∀ i : Fin 18, i.val < 11 → ∀ p : Int,
    p < 1 ∨ (2 * TableIO.width n : Nat) < p → cells (e i) p = none

private theorem cfg_eq {P : SearchTransducer} (a b : P.Config)
    (s : a.state = b.state) (i : a.inputHead = b.inputHead) (h : a.workHead = b.workHead)
    (t : a.workCell = b.workCell) (o : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

/-- Execute both endpoint copies and the raw adjacency test in one machine. -/
theorem executeFromEndpoints {n : Nat} (G : Group (Fin n)) (x y : Fin n)
    (cut width B : Nat) (cutFit : cut ≤ n) (prior : List Bool)
    (cells : Fin W → Int → Option Bool)
    (ready : EndpointTemplates e leftSource rightSource n x.val y.val G.toOne.one.val cut width cells)
    (copyCap : 2 * TableIO.width n + 1 ≤ B)
    (queryCap : 3 * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1) ≤ B) :
    let word := @encodeCayley n G.toMul
    let M := crossMachine e leftSource rightSource
    ∃ k d, M.BoundedSegment word B (crossStart e leftSource rightSource n cells prior) d k ∧
      M.step word d = none ∧
      (crossBit e leftSource rightSource d.state = true ↔
        ReingoldLiveInput.difference G x y = G.toOne.one ∨
          (ReingoldLiveInput.difference G x y).val < cut) ∧
      d.outputReversed = prior ∧
      (∀ j ∉ Set.range e, d.workHead j = 0 ∧ d.workCell j = cells j) ∧
      ∀ i : Fin 18, 11 ≤ i.val → i ≠ 12 → i ≠ 15 →
        d.workHead (e i) = 0 ∧ d.workCell (e i) = cells (e i) := by
  let word := @encodeCayley n G.toMul
  let id := G.toOne.one.val
  let w := TableIO.width n
  let A := endpointsMachine e leftSource rightSource
  let q := endpointsStart e leftSource rightSource n cells prior
  have clockRow : cells (e 11) = work (encodeLabel (2*w) 0) :=
    ready.immutable 11 (by decide) (by decide) (by decide)
  have clockTarget : cells (e 14) = work (encodeLabel w 0) :=
    ready.immutable 14 (by decide) (by decide) (by decide)
  obtain ⟨a,mid,runA,stopA,inputA,outputA,headsA,cellsA,row,target⟩ :=
    executeEndpointCopies e leftSource rightSource G.toMul width x.val y.val ready.wide cells prior
      clockRow clockTarget ready.leftWord ready.rightWord ready.noTargetAlias ready.rowBoundary ready.targetBoundary
  have saved (j : Fin W) (notRow : j ≠ e 12) (notTarget : j ≠ e 15) : mid.workCell j = cells j :=
    (congrFun cellsA j).trans (endpointsOutside e leftSource rightSource n cells notRow notTarget)
  let region : Fin 18 → Int → Option Bool := fun i => mid.workCell (e i)
  have templates : Templates n x.val y.val id cut region := by
    constructor
    · intro i iHigh
      by_cases hRow : i = 12
      · subst i
        exact row
      by_cases hTarget : i = 15
      · subst i
        exact target
      exact (saved (e i) (fun h => hRow (e.injective h)) (fun h => hTarget (e.injective h))).trans
        (ready.immutable i iHigh hRow hTarget)
    · intro i iLow p hp
      have hRow : e i ≠ e 12 := fun h => by have := congrArg Fin.val (e.injective h); omega
      have hTarget : e i ≠ e 15 := fun h => by have := congrArg Fin.val (e.injective h); omega
      exact (congrFun (saved (e i) hRow hTarget) p).trans (ready.scratchBoundary i iLow p hp)
  obtain ⟨b,out,runB,stopB,answer,outputB,frameB⟩ :=
    executeFromTemplates G x y cut cutFit prior region templates
  let E := allBanks (W := W)
  let liftedMid := A.bankConfig E mid q.workHead q.workCell
  have liftedA := A.relocateBanks_segment E (PhysicalEntry.segment_mono runA copyCap)
    (heads := q.workHead) (cells := q.workCell) (by
      intro j hj
      exact (hj ⟨j,rfl⟩).elim)
  have haltA : (A.relocateBanks E).step word liftedMid = none := by
    unfold liftedMid
    rw [relocateBanks_step, stopA]
    rfl
  have hMid (i : Fin W) : liftedMid.workHead i = 0 :=
    (A.bankConfig_head_image E mid q.workHead q.workCell i).trans (congrFun headsA i)
  have cMid (i : Fin W) : liftedMid.workCell i = mid.workCell i :=
    A.bankConfig_cell_image E mid q.workHead q.workCell i
  let bStart := preparedStart n region prior
  let bIn := preparedMachine.bankConfig e bStart liftedMid.workHead liftedMid.workCell
  let bOut := preparedMachine.bankConfig e out liftedMid.workHead liftedMid.workCell
  have bHead (i : Fin 18) : bStart.workHead i = 0 := by fin_cases i <;> rfl
  have bCell (i : Fin 18) : bStart.workCell i = region i := by fin_cases i <;> rfl
  have tail := preparedMachine.relocateBanks_segment e (PhysicalEntry.segment_mono runB queryCap)
    (heads := liftedMid.workHead) (cells := liftedMid.workCell) (by
      intro j _
      rw [hMid]
      exact Nat.zero_le _)
  have handoff : thenEntry A preparedMachine E e liftedMid = bIn := by
    apply cfg_eq
    · rfl
    · exact inputA
    · funext j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i,rfl⟩ := hj
        rw [show bIn.workHead (e i) = bStart.workHead i from
          preparedMachine.bankConfig_head_image e bStart _ _ i, bHead]
        exact hMid _
      · exact (preparedMachine.bankConfig_frame e bStart _ _ hj).1.symm
    · funext j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i,rfl⟩ := hj
        rw [show bIn.workCell (e i) = bStart.workCell i from
          preparedMachine.bankConfig_cell_image e bStart _ _ i, bCell]
        exact cMid _
      · exact (preparedMachine.bankConfig_frame e bStart _ _ hj).2.symm
    · exact outputA
  change (preparedMachine.relocateBanks e).BoundedSegment word B bIn bOut b at tail
  rw [← handoff] at tail
  let result := thenRight A preparedMachine E e bOut
  refine ⟨a+1+b, result, thenSegment A preparedMachine E e liftedA haltA tail, ?_, ?_,
    outputB, ?_, ?_⟩
  · change (crossMachine e leftSource rightSource).step word (thenRight A preparedMachine E e bOut) = none
    rw [thenStep_right]
    unfold bOut
    rw [relocateBanks_step, stopB]
    rfl
  · change crossBit e leftSource rightSource (Fin.natAdd A.states out.state) = true ↔ _
    unfold crossBit
    rw [finSumFinEquiv_symm_apply_natAdd]
    exact answer
  · intro j hj
    obtain ⟨h,c⟩ := preparedMachine.bankConfig_frame e out liftedMid.workHead liftedMid.workCell hj
    exact ⟨h.trans (hMid j), c.trans ((cMid j).trans
      (saved j (fun eq => hj ⟨12,eq.symm⟩) (fun eq => hj ⟨15,eq.symm⟩)))⟩
  · intro i hI rn tn
    obtain ⟨h,c⟩ := frameB i hI
    refine ⟨(preparedMachine.bankConfig_head_image e out liftedMid.workHead liftedMid.workCell i).trans h,
      (preparedMachine.bankConfig_cell_image e out liftedMid.workHead liftedMid.workCell i).trans (c.trans ?_)⟩
    exact saved (e i) (fun eq => rn (e.injective eq)) (fun eq => tn (e.injective eq))

end Mathproof.MinimumGeneration.CayleyPrefixLeaf
