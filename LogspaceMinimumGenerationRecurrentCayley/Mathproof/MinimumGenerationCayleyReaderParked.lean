import Mathproof.MinimumGenerationCayleyReaderFrame
import Mathproof.MinimumGenerationParkOrigin

namespace Mathproof.MinimumGeneration.CayleyReaderParked

open SearchTransducer
open CayleyQueryPrefixModel (addressBank markerBank guardBanks coordBanks cells keep rawSpace)

private abbrev P := CayleyQueryPrefix.machine

abbrev machine := ParkOrigin.machine P

abbrev callback : VirtualCallbackDriver.Callback :=
  ⟨machine, fun s => CayleyQueryPrefix.callback.returnCell (ParkOrigin.resumedState P s)⟩

def sourceEntry {n : Nat} (G : Group (Fin n)) (cut : Nat) (s t : Fin (n+n))
    (p : Nat) (prior : List Bool) : P.Config :=
  CayleyQueryRouter.start addressBank markerBank guardBanks coordBanks CayleyQueryPrefix.cross
    CayleyQueryPrefix.fit (↑(n+1 : Nat) : Int) (cells G cut s t p) prior

def start {n : Nat} (G : Group (Fin n)) (cut : Nat) (s t : Fin (n+n))
    (p : Nat) (prior : List Bool) : machine.Config :=
  ParkOrigin.lift P 0 (sourceEntry G cut s t p prior) (fun _ => 0)

private theorem sourceHeads {n : Nat} (G : Group (Fin n)) (cut : Nat) (s t : Fin (n+n))
    (p : Nat) (prior : List Bool) (i : Fin P.workTapes) :
    (sourceEntry G cut s t p prior).workHead i = 0 := by
  let A := CayleyQueryGuard.machine addressBank markerBank guardBanks
  let C := CayleyQueryGuard.start addressBank markerBank guardBanks (↑(n+1 : Nat) : Int)
    (cells G cut s t p) prior
  let e : Fin A.workTapes ↪ Fin A.workTapes := Function.Embedding.refl _
  change (A.bankConfig e C C.workHead C.workCell).workHead (e i) = 0
  rw [bankConfig_head_image]
  rfl

/-- The finite entry state and both physical tape projections. -/
theorem startSpec {n : Nat} (G : Group (Fin n)) (cut : Nat) (s t : Fin (n+n))
    (p : Nat) (prior : List Bool) :
    let c := start G cut s t p prior
    c.state = machine.initialState ∧ c.inputHead = (↑(n+1 : Nat) : Int) ∧
      c.outputReversed = prior ∧ (∀ i, c.workHead i = 0) ∧
      (∀ j, c.workCell (Fin.castAdd P.workTapes j) = cells G cut s t p j) ∧
      (∀ j, c.workCell (Fin.natAdd P.workTapes j) = ParkOrigin.origin) := by
  let c := start G cut s t p prior
  let A := CayleyQueryGuard.machine addressBank markerBank guardBanks
  let C := CayleyQueryGuard.start addressBank markerBank guardBanks (↑(n+1 : Nat) : Int)
    (cells G cut s t p) prior
  let e : Fin A.workTapes ↪ Fin A.workTapes := Function.Embedding.refl _
  have h : ParkOrigin.parked P (sourceEntry G cut s t p prior) =
      sourceEntry G cut s t p prior := by
    generalize eq : sourceEntry G cut s t p prior = q
    have hq : q.workHead = fun _ => 0 := by
      rw [← eq]
      exact funext (sourceHeads G cut s t p prior)
    cases q
    simp_all [ParkOrigin.parked]
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
  · intro j
    unfold start
    rw [← h]
    exact congrFun (ParkOrigin.heads_lift_parked P _ _ _) j
  · intro j
    rw [start, ParkOrigin.originalCell_lift]
    change (A.bankConfig e C C.workHead C.workCell).workCell (e j) = _
    rw [bankConfig_cell_image]
    rfl
  · intro j
    exact ParkOrigin.shadowCell_lift P _ _ _ j

/-- Execute the actual all-address reader and physically park every work
head. The exact answer, tape frame, and blank exterior are retained. -/
theorem execute {n : Nat} (G : Group (Fin n)) (cut : Nat) (hCut : cut ≤ n)
    (s t : Fin (n+n)) (p : Nat) (prior : List Bool)
    (legal : p ≤ Connectivity.ustconHeaderLength s t + (n+n)*(n+n) + 1) :
    let raw := @encodeCayley n G.toMul
    let B := rawSpace raw
    ∃ k d, machine.BoundedSegment raw B (start G cut s t p prior) d k ∧
      machine.step raw d = none ∧
      callback.returnCell d.state =
        Connectivity.ustconCell (BipartiteCayley.bits G (fun _ => true) cut) s t ((p : Int)-1) ∧
      d.outputReversed = prior ∧ d.workHead = (fun _ => 0) ∧
      (∀ j ∈ keep, d.workCell (Fin.castAdd P.workTapes j) = cells G cut s t p j) ∧
      (∀ j pos, B < pos.natAbs → d.workCell (Fin.castAdd P.workTapes j) pos = none) ∧
      (∀ j, d.workCell (Fin.natAdd P.workTapes j) = ParkOrigin.origin) ∧
      (-1 : Int) ≤ d.inputHead ∧ d.inputHead ≤ (raw.length : Int) := by
  obtain ⟨k,d,run,halt,answer,printed,frame,bound,outside⟩ :=
    CayleyReaderFrame.execute G cut hCut s t p prior legal
  change P.BoundedSegment _ _ (sourceEntry G cut s t p prior) d k at run
  have init : ParkOrigin.valid P (sourceEntry G cut s t p prior) (fun _ => 0) := by
    intro i h
    exact (h (sourceHeads G cut s t p prior i)).elim
  obtain ⟨j,side,_,steps,stop⟩ := ParkOrigin.execute P init run halt
  refine ⟨k+1+j, _, steps, stop, ?_, printed, ParkOrigin.heads_lift_parked P _ _ _, ?_, ?_, ?_,
    bound.1, bound.2.1⟩
  · simpa only [callback, ParkOrigin.resumedState_lift, ParkOrigin.control_parked] using answer
  · intro i hi
    rw [ParkOrigin.originalCell_lift, ParkOrigin.cells_parked]
    exact (frame i hi).2
  · intro i pos hp
    rw [ParkOrigin.originalCell_lift, ParkOrigin.cells_parked]
    exact outside k le_rfl d run.1 i pos hp
  · intro i
    exact ParkOrigin.shadowCell_lift P _ _ _ i

end Mathproof.MinimumGeneration.CayleyReaderParked
