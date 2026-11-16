import Mathproof.MinimumGenerationCayleyReaderRestore
import Mathproof.MinimumGenerationPayloadSeekFrom

namespace Mathproof.MinimumGeneration.CayleyReaderRestoreSeek

open SearchTransducer
open CayleyReaderRestore (clock source readerBanks)
open CayleyQueryPrefixModel (cells)

set_option backward.isDefEq.respectTransparency false

private abbrev R := CayleyReaderRestore.machine
private abbrev S := PayloadSeek.machine 39
private def sameBanks : Fin 39 ↪ Fin 39 := Function.Embedding.refl _

/-- Reinstall the prepared reader frame, then park the read-only input at
the start of the actual Cayley payload. -/
abbrev machine := thenMachine R S sameBanks sameBanks

def start (input : Int) (out : List Bool) (old : Fin 39 → Int → Option Bool) :
    machine.Config :=
  let c := CayleyReaderReset.start clock source input out old
  thenLeft R S sameBanks sameBanks (R.bankConfig sameBanks c c.workHead c.workCell)

theorem startSpec (input : Int) (out : List Bool) (old : Fin 39 → Int → Option Bool) :
    let c := start input out old
    c.state = machine.initialState ∧ c.inputHead = input ∧ c.outputReversed = out ∧
      (∀ j, c.workHead j = 0) ∧ c.workCell = old := by
  let b := CayleyReaderReset.start clock source input out old
  refine ⟨rfl,rfl,rfl,fun j => ?_,funext (fun j => ?_)⟩
  · exact bankConfig_head_image R sameBanks b b.workHead b.workCell j
  · exact bankConfig_cell_image R sameBanks b b.workHead b.workCell j

private theorem cfgEq {P : SearchTransducer} (a b : P.Config)
    (s : a.state = b.state) (i : a.inputHead = b.inputHead) (h : a.workHead = b.workHead)
    (z : a.workCell = b.workCell) (o : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

/-- A single physical checkout handles arbitrary legal raw-head positions,
including both endmarkers, and reinstalls the exact next reader entry. -/
theorem execute {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    (input : Int) (prior ticks : List Bool) (old : Fin 39 → Int → Option Bool)
    (ready : CayleyReaderRestore.Ready G cut s t p ticks old)
    (legal : (-1 : Int) ≤ input ∧ input ≤ (@encodeCayley n G.toMul).length) :
    let raw := @encodeCayley n G.toMul
    ∃ k d, machine.BoundedSegment raw (ticks.length+1) (start input prior old) d k ∧
      machine.step raw d = none ∧ d.inputHead = (↑(n+1 : ℕ) : Int) ∧ d.outputReversed = prior ∧
      (∀ j, d.workHead j = 0) ∧
      (∀ j, d.workCell (readerBanks j) = cells G cut s t p j) ∧
      ∀ j : Fin 39, 35 ≤ j.val → d.workCell j = old j := by
  let raw := @encodeCayley n G.toMul
  let a := CayleyReaderReset.start clock source input prior old
  obtain ⟨k,mid,reset,resetHalt,midIn,midOut,midHead,midCells,midFrame⟩ :=
    CayleyReaderRestore.execute G cut s t p input prior ticks old ready legal
  let c := R.bankConfig sameBanks mid a.workHead a.workCell
  have first := relocateBanks_segment R sameBanks (heads := a.workHead) (cells := a.workCell) reset
    (fun j _ => by change (0:Int).natAbs ≤ _; exact Nat.zero_le _)
  have firstDone := relocateBanks_step R sameBanks raw mid a.workHead a.workCell
  rw [resetHalt] at firstDone
  have pointer : (-1 : Int) ≤ mid.inputHead ∧ mid.inputHead ≤ raw.length := by
    rw [midIn]
    exact legal
  obtain ⟨length,seek,seekHalt⟩ := PayloadSeek.executeFrom (B := ticks.length+1) mid.inputHead G.toMul
    mid.workHead mid.workCell mid.outputReversed pointer
      (fun j => by rw [midHead]; exact Nat.zero_le _)
  let pre := PayloadSeek.cfg 0 mid.inputHead mid.workHead mid.workCell mid.outputReversed
  let last := PayloadSeek.cfg 2 (n+1 : ℕ) mid.workHead mid.workCell mid.outputReversed
  have h₂ := relocateBanks_segment S sameBanks (heads := c.workHead) (cells := c.workCell) seek
    (fun j _ => by
      have atHead : c.workHead j = mid.workHead j :=
        bankConfig_head_image R sameBanks mid a.workHead a.workCell j
      rw [atHead,midHead]
      exact Nat.zero_le _)
  let pre' := S.bankConfig sameBanks pre c.workHead c.workCell
  let last' := S.bankConfig sameBanks last c.workHead c.workCell
  have entry : thenEntry R S sameBanks sameBanks c = pre' := by
    refine cfgEq _ _ rfl rfl ?_ ?_ rfl
    · funext j
      exact (bankConfig_head_image R sameBanks mid a.workHead a.workCell j).trans
        (bankConfig_head_image S sameBanks pre c.workHead c.workCell j).symm
    · funext j
      exact (bankConfig_cell_image R sameBanks mid a.workHead a.workCell j).trans
        (bankConfig_cell_image S sameBanks pre c.workHead c.workCell j).symm
  change (S.relocateBanks sameBanks).BoundedSegment raw (ticks.length+1) pre' last' length at h₂
  rw [← entry] at h₂
  have lastDone := relocateBanks_step S sameBanks raw last c.workHead c.workCell
  rw [seekHalt] at lastDone
  let d := thenRight R S sameBanks sameBanks last'
  refine ⟨k+1+length,d,thenSegment R S sameBanks sameBanks first firstDone h₂,?_,rfl,midOut,?_,?_,?_⟩
  · change machine.step raw (thenRight R S sameBanks sameBanks last') = none
    rw [thenStep_right,lastDone]
    rfl
  · intro j
    exact (bankConfig_head_image S sameBanks last c.workHead c.workCell j).trans (midHead j)
  · intro j
    exact (bankConfig_cell_image S sameBanks last c.workHead c.workCell (readerBanks j)).trans
      (midCells j)
  · intro j high
    exact (bankConfig_cell_image S sameBanks last c.workHead c.workCell j).trans (midFrame j high)

end Mathproof.MinimumGeneration.CayleyReaderRestoreSeek
