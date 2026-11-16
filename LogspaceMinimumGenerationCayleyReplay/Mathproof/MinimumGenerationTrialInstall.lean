import Mathproof.MinimumGenerationTapeInstall
import Mathproof.MinimumGenerationPayloadSeek
import Mathproof.MinimumGenerationReingoldLiveInput

namespace Mathproof.MinimumGeneration.TrialInstall

open SearchTransducer
open InputPosition (work)
open ReingoldLiveInput (signedTrialMachine signedTrialStart)

set_option backward.isDefEq.respectTransparency false

/-- The trial's own ten banks lie below six immutable caller templates. -/
def trialBanks : Fin signedTrialMachine.workTapes ↪ Fin 16 :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun q : Fin 16 => q.val) h)⟩

private def templateIndex (i : Fin 10) : Fin 16 :=
  if i = 1 then 11
  else if i = 4 then 12
  else if i = 6 ∨ i = 8 then 13
  else if i = 7 then 14
  else if i = 9 then 15
  else 10

def source (i : Fin 16) : Option (Fin 16) :=
  if hi : i.val < 10 then some (templateIndex ⟨i.val, hi⟩) else none

def template (n x y label : Nat) (i : Fin 16) : Int → Option Bool :=
  let w := TableIO.width n
  if i = 10 then work (encodeLabel (2 * w) 0)
  else if i = 11 then work (encodeLabel (2 * w) x)
  else if i = 12 then work (encodeLabel (2 * w) n)
  else if i = 13 then work (List.replicate w false)
  else if i = 14 then work (encodeLabel w y)
  else if i = 15 then work (encodeLabel w label)
  else fun _ => none

abbrev machine := TapeInstall.machine (10 : Fin 16) source

private theorem registers (w a : Nat) : TapeAddition.register w a = work (encodeLabel w a) := by
  funext p
  by_cases h : p ≤ 0
  · simp [TapeAddition.register, work, h, show p < 1 by omega]
  · simp [TapeAddition.register, work, h, show ¬ p < 1 by omega]

private theorem zeroBits (w : Nat) : encodeLabel w 0 = List.replicate w false := by
  have hz : Nat.testBit 0 = fun _ => false := funext Nat.zero_testBit
  simp [encodeLabel, hz]

private theorem templates_layout (n x y label : Nat) (prior : List Bool) (i : Fin 10) :
    template n x y label (templateIndex i) =
      (signedTrialStart n x y label prior).workCell i := by
  fin_cases i
  · exact (registers _ _).symm
  · exact (registers _ _).symm
  · exact (registers _ _).symm
  · exact (registers _ _).symm
  · exact (registers _ _).symm
  · exact (registers _ _).symm
  · rfl
  · rfl
  · change work (List.replicate (TableIO.width n) false) =
      work (encodeLabel (TableIO.width n) 0)
    rw [zeroBits]
  · rfl

private theorem templateIndex_ge (i : Fin 10) : 10 ≤ (templateIndex i).val := by
  fin_cases i <;> decide

private theorem work_outside (bits : List Bool) (B : Nat) (hb : bits.length ≤ B)
    (p : Int) (hp : p < 1 ∨ (B : Int) < p) : work bits p = none := by
  rcases hp with h | h
  · simp [work, show p ≤ 0 by omega]
  · simp only [work, if_neg (show ¬ p ≤ 0 by omega)]
    exact List.getElem?_eq_none (by omega)

private theorem template_outside (n x y label : Nat) (i : Fin 10) (p : Int)
    (hp : p < 1 ∨ ((2 * TableIO.width n : Nat) : Int) < p) :
    template n x y label (templateIndex i) p = none := by
  fin_cases i <;> exact work_outside _ _ (by simp <;> omega) p hp

/-- The template banks hold the current endpoints, order, signed generator,
and two zero templates. Scratch outside the written interval is blank. -/
def Prepared (n x y label : Nat) (cells : Fin 16 → Int → Option Bool) : Prop :=
  (∀ i, 10 ≤ i.val → cells i = template n x y label i) ∧
  ∀ i, i.val < 10 → ∀ p, p < 1 ∨ ((2 * TableIO.width n : Nat) : Int) < p →
    cells i p = none

/-- Install the literal physical ABI of a signed trial in one bounded sweep.
Prior dirty cells inside the scratch bank window are overwritten. -/
theorem execute {n : Nat} (M : Mul (Fin n)) (x y label : Fin n) (prior : List Bool)
    (cells : Fin 16 → Int → Option Bool) (hc : Prepared n x.val y.val label.val cells) :
    let word := @encodeCayley n M
    let w := TableIO.width n
    let initial := TapeInstall.start (10 : Fin 16) source (↑(n + 1) : Int) cells prior
    let result := TapeInstall.stop (10 : Fin 16) source (↑(n + 1) : Int) cells prior (2 * w)
    machine.BoundedSegment word (2 * w + 1) initial result (2 * w + 2 + 2 * w + 1) ∧
    machine.step word result = none ∧
    result.inputHead = (signedTrialStart n x.val y.val label.val prior).inputHead ∧
    result.workHead = (fun _ => 0) ∧ result.outputReversed = prior ∧
    (∀ i : Fin signedTrialMachine.workTapes,
      result.workCell (trialBanks i) = (signedTrialStart n x.val y.val label.val prior).workCell i) ∧
    ∀ i, 10 ≤ i.val → result.workCell i = cells i := by
  let w := TableIO.width n
  let word := @encodeCayley n M
  have hc₀ : cells (10 : Fin 16) = work (encodeLabel (2 * w) 0) := hc.1 10 (by decide)
  have hin : (-1 : Int) ≤ (↑(n + 1) : Int) ∧ (↑(n + 1) : Int) ≤ word.length := by
    have h : n + 1 ≤ word.length := by
      change n + 1 ≤ (@encodeCayley n M).length
      rw [@length_encodeCayley n M]
      omega
    exact ⟨by omega, by exact_mod_cast h⟩
  obtain ⟨run, halt⟩ := TapeInstall.execute (10 : Fin 16) source (by decide)
    word (encodeLabel (2 * w) 0) prior (↑(n + 1) : Int) cells hc₀ hin
  rw [length_encodeLabel] at run halt
  refine ⟨run, halt, rfl, rfl, rfl, ?_, ?_⟩
  · intro i
    change TapeInstall.installed source cells (2 * w) (trialBanks i) =
      (signedTrialStart n x.val y.val label.val prior).workCell i
    have hi : (trialBanks i).val < 10 := i.isLt
    have hm : source (trialBanks i) = some (templateIndex i) := by
      simp [source, trialBanks]
    rw [TapeInstall.installed_exact source cells (2 * w) _ _ hm]
    · exact (hc.1 (templateIndex i) (templateIndex_ge i)).trans (templates_layout n _ _ _ prior i)
    · intro p hp
      rw [hc.2 _ hi p hp, hc.1 (templateIndex i) (templateIndex_ge i)]
      exact (template_outside n _ _ _ i p hp).symm
  · intro i hi
    exact TapeInstall.installed_source source cells (2 * w) i
      (by simp [source, show ¬ i.val < 10 by omega])


private def identicalBanks : Fin 16 ↪ Fin 16 := Function.Embedding.refl _

private abbrev seek := PayloadSeek.machine 16

private def parked := (fun _ : Fin 16 => (0 : Int))

private theorem configuration_eq {P : SearchTransducer} (a b : P.Config)
    (hs : a.state = b.state) (hi : a.inputHead = b.inputHead)
    (hh : a.workHead = b.workHead) (hc : a.workCell = b.workCell)
    (ho : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

abbrev prepareMachine := thenMachine seek machine identicalBanks identicalBanks

def prepareStart (input : Nat) (cells : Fin 16 → Int → Option Bool) (prior : List Bool) :
    prepareMachine.Config :=
  thenLeft seek machine identicalBanks identicalBanks
    (seek.bankConfig identicalBanks (PayloadSeek.cfg 0 input parked cells prior) parked cells)

/-- From a live signed-generator bank and parked order/endpoints, seek the raw
table payload and install the literal signed trial registers in one physical run. -/
theorem prepare {n : Nat} (M : Mul (Fin n)) (x y label : Fin n) (p : Nat)
    (prior : List Bool) (cells : Fin 16 → Int → Option Bool)
    (hc : Prepared n x.val y.val label.val cells) (hp : p ≤ (@encodeCayley n M).length) :
    let word := @encodeCayley n M
    let w := TableIO.width n
    ∃ d : prepareMachine.Config,
      prepareMachine.BoundedSegment word (2 * w + 1) (prepareStart p cells prior) d
        (p + 2 + n + 1 + 1 + (2 * w + 2 + 2 * w + 1)) ∧
      prepareMachine.step word d = none ∧
      d.inputHead = (signedTrialStart n x.val y.val label.val prior).inputHead ∧
      d.workHead = parked ∧ d.outputReversed = prior ∧
      (∀ i : Fin signedTrialMachine.workTapes,
        d.workCell (trialBanks i) = (signedTrialStart n x.val y.val label.val prior).workCell i) ∧
      ∀ i, 10 ≤ i.val → d.workCell i = cells i := by
  let word := @encodeCayley n M
  let w := TableIO.width n
  let B := 2 * w + 1
  let a := PayloadSeek.cfg 2 (n + 1 : Nat) parked cells prior
  let b := TapeInstall.start (10 : Fin 16) source (↑(n + 1) : Int) cells prior
  let z := TapeInstall.stop (10 : Fin 16) source (↑(n + 1) : Int) cells prior (2 * w)
  obtain ⟨runA, stopA⟩ := PayloadSeek.executeCayley (B := B) n p M parked cells prior hp (by simp [parked])
  obtain ⟨runB, stopB, inputB, headsB, outputB, trialB, frameB⟩ := execute M x y label prior cells hc
  have hBound : ∀ i ∉ Set.range identicalBanks, (parked i).natAbs ≤ B := by simp [parked]
  have aSeg := seek.relocateBanks_segment identicalBanks runA (heads := parked) (cells := cells) hBound
  let aLift := seek.bankConfig identicalBanks a parked cells
  have aStop : (seek.relocateBanks identicalBanks).step word aLift = none := by
    unfold aLift a
    rw [seek.relocateBanks_step, stopA]
    rfl
  have bSeg := machine.relocateBanks_segment identicalBanks runB (heads := parked) (cells := cells) hBound
  let bEntry := machine.bankConfig identicalBanks b parked cells
  let bEnd := machine.bankConfig identicalBanks z parked cells
  have handoff : thenEntry seek machine identicalBanks identicalBanks aLift = bEntry := by
    apply configuration_eq
    · rfl
    · rfl
    · funext i
      change aLift.workHead (identicalBanks i) = bEntry.workHead (identicalBanks i)
      rw [show aLift.workHead (identicalBanks i) = 0 from bankConfig_head_image seek identicalBanks a parked cells i,
        show bEntry.workHead (identicalBanks i) = 0 from bankConfig_head_image machine identicalBanks b parked cells i]
    · funext i
      change aLift.workCell (identicalBanks i) = bEntry.workCell (identicalBanks i)
      rw [show aLift.workCell (identicalBanks i) = cells i from bankConfig_cell_image seek identicalBanks a parked cells i,
        show bEntry.workCell (identicalBanks i) = cells i from bankConfig_cell_image machine identicalBanks b parked cells i]
    · rfl
  change (machine.relocateBanks identicalBanks).BoundedSegment word B bEntry bEnd _ at bSeg
  rw [← handoff] at bSeg
  have bStop : (machine.relocateBanks identicalBanks).step word bEnd = none := by
    unfold bEnd z
    rw [machine.relocateBanks_step, stopB]
    rfl
  let d := thenRight seek machine identicalBanks identicalBanks bEnd
  refine ⟨d, thenSegment seek machine identicalBanks identicalBanks aSeg aStop bSeg,
    ?_, inputB, ?_, outputB, ?_, ?_⟩
  · change prepareMachine.step word (thenRight seek machine identicalBanks identicalBanks bEnd) = none
    rw [thenStep_right, bStop]
    rfl
  · funext i
    change bEnd.workHead (identicalBanks i) = parked i
    exact (bankConfig_head_image machine identicalBanks z parked cells i).trans (congrFun headsB i)
  · intro i
    change bEnd.workCell (identicalBanks (trialBanks i)) = _
    exact (bankConfig_cell_image machine identicalBanks z parked cells (trialBanks i)).trans (trialB i)
  · intro i hi
    change bEnd.workCell (identicalBanks i) = _
    exact (bankConfig_cell_image machine identicalBanks z parked cells i).trans (frameB i hi)
end Mathproof.MinimumGeneration.TrialInstall
