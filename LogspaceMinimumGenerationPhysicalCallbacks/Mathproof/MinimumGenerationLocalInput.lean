import Mathproof.MinimumGenerationTapeCompose

namespace Mathproof.MinimumGeneration.SearchTransducer

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)

variable (M : SearchTransducer)

private def dataTrack (word : List Bool) (i : Int) : Option Bool :=
  if i < 0 then none else word[i.toNat]?

private def leftTrack (i : Int) : Option Bool :=
  if i = -1 then some true else none

private def trackRead (bits marker : Option Bool) : InputCell :=
  if marker = some true then .leftEnd else bits.elim .rightEnd .data

private theorem trackRead_eq (word : List Bool) (i : Int) (hi : -1 ≤ i) :
    trackRead (dataTrack word i) (leftTrack i) = readInput word i := by
  by_cases hn : i < 0
  · have he : i = -1 := by omega
    subst i
    simp [trackRead, leftTrack, readInput]
  · have hne : i ≠ -1 := by omega
    simp [trackRead, dataTrack, leftTrack, readInput, hn, hne]

/-- Execute a binary subroutine on a word already held in two work banks.
Its own input-head moves advance the data and left-marker banks in lockstep.
The ambient raw input head stays parked for the entire execution. -/
@[reducible] def inputOnBanks : SearchTransducer where
  states := M.states
  workTapes := M.workTapes + 2
  initialState := M.initialState
  transition q _ scanned :=
    (M.transition q
      (trackRead (scanned (Fin.natAdd M.workTapes (0 : Fin 2)))
        (scanned (Fin.natAdd M.workTapes (1 : Fin 2))))
      (fun i => scanned (Fin.castAdd 2 i))).map
      (fun (next, move, actions, out) =>
        (next, .stay, Fin.addCases actions (fun _ => ⟨none, move⟩), out))

/-- The physical representation for a subroutine state. The left-marker track
occupies a single cell, including on an empty local input. -/
@[reducible] def inputBankConfig (localWord : List Bool) (parked : Int) (c : M.Config) :
    M.inputOnBanks.Config where
  state := c.state
  inputHead := parked
  workHead := Fin.addCases c.workHead (fun _ : Fin 2 => c.inputHead)
  workCell := Fin.addCases c.workCell (fun i : Fin 2 =>
    if i = 0 then dataTrack localWord else leftTrack)
  outputReversed := c.outputReversed

theorem inputOnBanks_step (outer localWord : List Bool) (parked : Int) (c : M.Config)
    (hc : -1 ≤ c.inputHead) :
    M.inputOnBanks.step outer (M.inputBankConfig localWord parked c) =
      (M.step localWord c).map (M.inputBankConfig localWord parked) := by
  unfold SearchTransducer.step
  simp only [inputOnBanks, inputBankConfig, Fin.addCases_left, Fin.addCases_right,
    if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
  rw [trackRead_eq localWord c.inputHead hc]
  cases ht : M.transition c.state (readInput localWord c.inputHead)
      (fun b => c.workCell b (c.workHead b)) with
  | none => rfl
  | some p =>
    rcases p with ⟨q, mov, acts, out⟩
    simp only [Option.map_some, Option.some.injEq, inputBankConfig, moveOffset, Int.add_zero]
    congr 1
    · funext b
      refine Fin.addCases (m := M.workTapes) (n := 2) (fun i => ?_) (fun i => ?_) b
      · simp only [Fin.addCases_left]
      · simp only [Fin.addCases_right]
    · funext b x
      refine Fin.addCases (m := M.workTapes) (n := 2) (fun i => ?_) (fun i => ?_) b
      · simp only [Fin.addCases_left]
      · simp only [Fin.addCases_right, Option.getD_none, ite_self]

private theorem inputBankConfig_bounded (outer localWord : List Bool) (parked : Int)
    {B : Nat} {c : M.Config} (hc : M.Bounded localWord B c)
    (hLeft : -1 ≤ parked) (hRight : parked ≤ (outer.length : Int)) :
    M.inputOnBanks.Bounded outer (max B (localWord.length + 1))
      (M.inputBankConfig localWord parked c) := by
  refine ⟨hLeft, hRight, ?_⟩
  intro b
  refine Fin.addCases (m := M.workTapes) (n := 2) (fun i => ?_) (fun i => ?_) b
  · simpa only [inputBankConfig, Fin.addCases_left] using
      (hc.2.2 i).trans (Nat.le_max_left B (localWord.length + 1))
  · have hn : c.inputHead.natAbs ≤ localWord.length + 1 := by
      have := hc.1
      have := hc.2.1
      omega
    simpa only [inputBankConfig, Fin.addCases_right] using
      hn.trans (Nat.le_max_right B (localWord.length + 1))

/-- The entire local read-only run is executed on the prepared data banks.
This transports a physical arithmetic subroutine to local operand storage
without moving the raw input pointer or increasing its asymptotic workspace. -/
theorem inputOnBanks_segment (outer localWord : List Bool) (parked : Int)
    {B steps : Nat} {c d : M.Config}
    (h : M.BoundedSegment localWord B c d steps)
    (hLeft : -1 ≤ parked) (hRight : parked ≤ (outer.length : Int)) :
    M.inputOnBanks.BoundedSegment outer (max B (localWord.length + 1))
      (M.inputBankConfig localWord parked c) (M.inputBankConfig localWord parked d) steps := by
  have prefixRun (k : Nat) (hk : k ≤ steps) :
      runFrom M.inputOnBanks outer (M.inputBankConfig localWord parked c) k =
        (runFrom M localWord c k).map (M.inputBankConfig localWord parked) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [runFrom, ih (by omega)]
      cases hx : runFrom M localWord c k with
      | none => rfl
      | some x =>
        simp only [Option.map_some, Option.bind_some]
        exact M.inputOnBanks_step outer localWord parked x (h.2 k (by omega) x hx).1
  refine ⟨by rw [prefixRun steps le_rfl, h.1, Option.map_some], ?_⟩
  intro k hk x hx
  rw [prefixRun k hk] at hx
  obtain ⟨u, hu, hux⟩ := Option.map_eq_some_iff.mp hx
  subst x
  exact M.inputBankConfig_bounded outer localWord parked (h.2 k hk u hu) hLeft hRight

theorem inputOnBanks_halt (outer localWord : List Bool) (parked : Int)
    {c : M.Config} (hc : -1 ≤ c.inputHead) (h : M.step localWord c = none) :
    M.inputOnBanks.step outer (M.inputBankConfig localWord parked c) = none := by
  rw [M.inputOnBanks_step outer localWord parked c hc, h]
  rfl

end Mathproof.MinimumGeneration.SearchTransducer
