import Mathproof.MinimumGenerationTapeRegisters
import Mathproof.MinimumGenerationRankPhysicalSubtract
import Mathproof.MinimumGenerationMacroDispatch

namespace Mathproof.MinimumGeneration.PrefixQuotientVerdict

open SearchTransducer
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

private abbrev C := TapeRegisters.machine (0 : Fin 3) 1 .compare
private abbrev P := RankPhysicalSubtract.machine
private def subBanks : Fin P.workTapes ↪ Fin 3 :=
  ⟨fun i => if i = 0 then 2 else 0, by
    intro i j h
    change Fin 2 at i j
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

/-- First accept the identity connector. Otherwise compare the live quotient
against the prefix boundary by running a physical unsigned subtraction. -/
abbrev routing : Stages 2 7 3 where
  first := 0
  entry _ := 0
  transition i := if i = 0 then C.transition else (P.relocateBanks subBanks).transition
  next i q := if i = 0 ∧ q = TapeRegisters.done false then some 1 else none

abbrev machine := routing.machine

def start (input : Int) (prior : List Bool) (labels : Fin 3 → List Bool) :
    machine.Config :=
  routing.tag 0 ⟨0, input, fun _ => 0, fun i => work (labels i), prior⟩

def answer (d : machine.Config) : Bool :=
  let (i, q) := finProdFinEquiv.symm d.state
  if i = 0 then q = TapeRegisters.done true else q = RankPhysicalSubtract.done true

private theorem work_block (xs : List Bool) : TapeArithmetic.block (work xs) 1 xs := by
  intro i
  simp [work, show ¬ (1 + (i.val : Int) ≤ 0) by omega,
    show 1 + (i.val : Int) - 1 = (i.val : Int) by omega]

def labels (w x identity cut : Nat) (i : Fin 3) : List Bool :=
  encodeLabel w (if i = 0 then x else if i = 1 then identity else cut)

private theorem labels_eq {w x y : Nat} (hx : x < 2^w) (hy : y < 2^w) :
    encodeLabel w x = encodeLabel w y ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg InputPosition.digits h
    rwa [InputPosition.digits_encodeLabel _ _ hx, InputPosition.digits_encodeLabel _ _ hy] at h'
  · rintro rfl
    rfl

private theorem identityOutside : (1 : Fin 3) ∉ Set.range subBanks := by
  rintro ⟨i, hi⟩
  change Fin 2 at i
  fin_cases i <;> contradiction

private theorem parkedLift (c : P.Config) (h : Fin 3 → Int)
    (cells : Fin 3 → Int → Option Bool)
    (hc : c.workHead = fun _ => 0) (hh : h = fun _ => 0) :
    (P.bankConfig subBanks c h cells).workHead = h := by
  funext i
  by_cases hi : i ∈ Set.range subBanks
  · obtain ⟨j,rfl⟩ := hi
    rw [bankConfig_head_image, hc, hh]
  · exact (P.bankConfig_frame subBanks c h cells hi).1

/-- The exact physical test for a prefix quotient from prepared registers. -/
theorem execute (word prior : List Bool) (input : Int) (w x identity cut : Nat)
    (hin : (-1 : Int) ≤ input ∧ input ≤ word.length)
    (hx : x < 2^w) (hi : identity < 2^w) (hk : cut < 2^w) :
    ∃ k d, machine.BoundedSegment word (w+1) (start input prior (labels w x identity cut)) d k ∧
      machine.step word d = none ∧ (answer d = true ↔ x = identity ∨ x < cut) ∧
      d.inputHead = input ∧ d.outputReversed = prior ∧ d.workHead = (fun _ => 0) := by
  let l := labels w x identity cut
  let c : C.Config := ⟨0,input,fun _ => 0,fun i => work (l i),prior⟩
  have hlo : c.workCell 1 (c.workHead 1) = none := rfl
  have hr₀ : c.workCell 0 (c.workHead 0 + (encodeLabel w x).length + 1) = none := by
    simp [c,l,labels]
  have hr₁ : c.workCell 1 (c.workHead 1 + (encodeLabel w x).length + 1) = none := by
    simp [c,l,labels]
  have block₀ : TapeArithmetic.block (c.workCell 0) (c.workHead 0 + 1) (encodeLabel w x) := by
    simpa [c,l,labels] using work_block (encodeLabel w x)
  have block₁ : TapeArithmetic.block (c.workCell 1) (c.workHead 1 + 1) (encodeLabel w identity) := by
    simpa [c,l,labels] using work_block (encodeLabel w identity)
  obtain ⟨mid,b,r,hs,hb,hHeads,hCells,hInput,hOut⟩ :=
    TapeRegisters.executeCompare word c (encodeLabel w x) (encodeLabel w identity)
      (by simp) rfl hlo hr₀ hr₁ block₀ block₁
  have cap : C.BoundedSegment word (w+1) c mid (2 * (encodeLabel w x).length + 3) := by
    apply r.boundedSegment hin
    intro t j h₀ h₁
    change 0 ≤ j at h₀
    unfold TapeRegisters.finish at h₁
    split at h₁ <;> simp [c] at h₁ <;> omega
  have halt : C.step word mid = none := TapeRegisters.step_done word mid b hs
  rw [labels_eq hx hi] at hb
  change (routing.component 0).BoundedSegment word _ c mid _ at cap
  change (routing.component 0).step word mid = none at halt
  cases b with
  | true =>
    have stop : routing.next 0 mid.state = none := by rw [hs]; decide
    obtain ⟨hRun,hDone⟩ := routing.routed_stop (.finish cap) halt stop
    refine ⟨_, routing.tag 0 mid, hRun, hDone, ?_, hInput, hOut, hHeads⟩
    simp [answer, Stages.tag, hs, hb.mp rfl]
  | false =>
    have next : routing.next 0 mid.state = some 1 := by rw [hs]; decide
    have ne : x ≠ identity := fun h => by simpa using hb.mpr h
    obtain ⟨tail,hTail⟩ := RankPhysicalSubtract.execute_encoded word prior input w x cut hin hx hk
    let init := RankPhysicalSubtract.cfg 0 0 (encodeLabel w x) (encodeLabel w cut) prior input
    let endCfg := RankPhysicalSubtract.cfg (RankPhysicalSubtract.done (decide (x < cut))) 0
      (Lax51Proofs.RamToTM.subBits (encodeLabel w x) (encodeLabel w cut) false)
      (encodeLabel w cut) prior input
    let entered := P.bankConfig subBanks init mid.workHead mid.workCell
    let last := P.bankConfig subBanks endCfg mid.workHead mid.workCell
    have tailLift := P.relocateBanks_segment subBanks tail (heads := mid.workHead)
      (cells := mid.workCell) (by simp [hHeads,c])
    have join : routing.enter (i := 0) 1 mid = entered := by
      have hc : entered.workCell = mid.workCell := by
        funext i
        fin_cases i
        · change entered.workCell (subBanks 1) = _
          rw [P.bankConfig_cell_image, hCells]
          rfl
        · exact (P.bankConfig_frame _ _ _ _ identityOutside).2
        · change entered.workCell (subBanks 0) = _
          rw [P.bankConfig_cell_image, hCells]
          rfl
      have hh : entered.workHead = mid.workHead := parkedLift _ _ _ rfl hHeads
      change ⟨0,mid.inputHead,mid.workHead,mid.workCell,mid.outputReversed⟩ = entered
      rw [← hc, ← hh, hInput, hOut]
      rfl
    change (routing.component 1).BoundedSegment word (w+1) entered last _ at tailLift
    rw [← join] at tailLift
    have haltLast : (routing.component 1).step word last = none := by
      change (P.relocateBanks subBanks).step word last = none
      unfold last
      rw [relocateBanks_step, hTail]
      rfl
    have stop : routing.next 1 last.state = none := by simp [show (1 : Fin 2) ≠ 0 by decide]
    obtain ⟨hRun,hDone⟩ := routing.routed_stop (.call cap halt next (.finish tailLift)) haltLast stop
    refine ⟨_, routing.tag 1 last, hRun, hDone, ?_, rfl, rfl, ?_⟩
    · by_cases h : x < cut <;> simp [answer, Stages.tag, last, endCfg, bankConfig,
        RankPhysicalSubtract.cfg, RankPhysicalSubtract.done, ne, h, show (1 : Fin 2) ≠ 0 by decide]
    · exact (parkedLift endCfg mid.workHead mid.workCell rfl hHeads).trans hHeads

end Mathproof.MinimumGeneration.PrefixQuotientVerdict
