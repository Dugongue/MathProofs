import Mathproof.MinimumGenerationRankPhysicalModulo
import Mathproof.MinimumGenerationTapeMultiply
import Mathlib.Data.ZMod.Basic

/-!
Prepared prime-field multiplication on a single finite SearchTransducer.
The integer product flows directly from the multiplier into the residue
loop, with the original input and output tapes parked.
-/

namespace Mathproof.MinimumGeneration.RankPhysicalPrimeProduct

open SearchTransducer

private def multiplyBanks : Fin 6 ↪ Fin 8 :=
  ⟨fun i => i.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun j : Fin 8 => j.val) h)⟩

private def residueIndex : Fin 3 → Fin 8 :=
  Fin.cases 0 (fun i : Fin 2 => ⟨i.val + 6, by omega⟩)

private def residueBanks : Fin 3 ↪ Fin 8 :=
  ⟨residueIndex, by
    intro i j h
    refine Fin.cases ?_ (fun a => ?_) i j h
    · intro j
      refine Fin.cases (fun _ => rfl) (fun b hb => ?_) j
      have h := congrArg Fin.val hb
      change 0 = b.val + 6 at h
      omega
    · intro j
      refine Fin.cases (fun ha => ?_) (fun b hab => ?_) j
      · have h := congrArg Fin.val ha
        change a.val + 6 = 0 at h
        omega
      · have h := congrArg Fin.val hab
        change a.val + 6 = b.val + 6 at h
        exact congrArg Fin.succ (Fin.ext (by omega))⟩

abbrev machine :=
  thenMachine TapeMultiply.machine RankPhysicalModulo.machine multiplyBanks residueBanks

private def parkedHeads : Fin 8 → Int := fun _ => 0

private def modulusFrame (w p : Nat) (scratch : List Bool) (i : Fin 8) : Int → Option Bool :=
  if i = 6 then InputPosition.work (encodeLabel w p) else InputPosition.work scratch

private def hostedMul (c : TapeMultiply.machine.Config) (w p : Nat) (scratch : List Bool) :=
  TapeMultiply.machine.bankConfig multiplyBanks c parkedHeads (modulusFrame w p scratch)

def startConfig (w x y p : Nat) (scratch out : List Bool) (parked : Int) : machine.Config :=
  thenLeft TapeMultiply.machine RankPhysicalModulo.machine multiplyBanks residueBanks
    (hostedMul (TapeMultiply.startConfig w 0 x y 0 parked out) w p scratch)

private def modStart (w z p : Nat) (scratch out : List Bool) (parked : Int) :
    RankPhysicalModulo.machine.Config :=
  RankPhysicalModulo.stages.tag 0 (RankPhysicalModulo.cfg 0 0
    (RankPhysicalModulo.bankWords (encodeLabel w z) (encodeLabel w p) scratch) out parked)

private def mulEnd (w x y p : Nat) (scratch out : List Bool) (parked : Int) :=
  hostedMul (TapeMultiply.stopConfig w (x*y) x y parked out) w p scratch

private def hostedMod (c : RankPhysicalModulo.machine.Config) (w x y p : Nat)
    (scratch out : List Bool) (parked : Int) :=
  RankPhysicalModulo.machine.bankConfig residueBanks c parkedHeads
    (mulEnd w x y p scratch out parked).workCell

def stopConfig (w x y p : Nat) (scratch out : List Bool) (parked : Int) : machine.Config :=
  thenRight TapeMultiply.machine RankPhysicalModulo.machine multiplyBanks residueBanks
    (hostedMod (RankPhysicalModulo.stages.tag 1 (RankPhysicalModulo.stopConfig w (x*y) p out parked))
      w x y p scratch out parked)

private theorem register_eq_work (w v : Nat) :
    TapeMultiply.register w v = InputPosition.work (encodeLabel w v) := by
  funext pos
  have h : pos < 1 ↔ pos ≤ 0 := by omega
  simp [TapeAddition.register, InputPosition.work, h]

private theorem six_frame : (6 : Fin 8) ∉ Set.range multiplyBanks := by
  rintro ⟨i, h⟩
  have he := congrArg Fin.val h
  change i.val = 6 at he
  have hi := i.isLt
  omega

private theorem seven_frame : (7 : Fin 8) ∉ Set.range multiplyBanks := by
  rintro ⟨i, h⟩
  have he := congrArg Fin.val h
  change i.val = 7 at he
  have hi := i.isLt
  omega

set_option maxHeartbeats 1400000 in
private theorem handoff (w x y p : Nat) (scratch out : List Bool) (parked : Int) :
    thenEntry TapeMultiply.machine RankPhysicalModulo.machine multiplyBanks residueBanks
      (mulEnd w x y p scratch out parked) =
      hostedMod (modStart w (x*y) p scratch out parked) w x y p scratch out parked := by
  let mul := TapeMultiply.stopConfig w (x*y) x y parked out
  let r := modStart w (x*y) p scratch out parked
  let a := hostedMul mul w p scratch
  let b := hostedMod r w x y p scratch out parked
  have hHeads : a.workHead = parkedHeads := by
    funext i
    by_cases hi : i ∈ Set.range multiplyBanks
    · obtain ⟨j, rfl⟩ := hi
      exact bankConfig_head_image TapeMultiply.machine multiplyBanks mul parkedHeads
        (modulusFrame w p scratch) j
    · exact (bankConfig_frame TapeMultiply.machine multiplyBanks mul parkedHeads
        (modulusFrame w p scratch) hi).1
  have bHeads : b.workHead = parkedHeads := by
    funext i
    by_cases hi : i ∈ Set.range residueBanks
    · obtain ⟨j, rfl⟩ := hi
      exact bankConfig_head_image RankPhysicalModulo.machine residueBanks r parkedHeads
        a.workCell j
    · exact (bankConfig_frame RankPhysicalModulo.machine residueBanks r parkedHeads a.workCell hi).1
  have hCells : a.workCell = b.workCell := by
    funext i
    by_cases hi : i ∈ Set.range residueBanks
    · obtain ⟨j, rfl⟩ := hi
      rw [show b.workCell (residueBanks j) = r.workCell j from
        bankConfig_cell_image RankPhysicalModulo.machine residueBanks r parkedHeads a.workCell j]
      fin_cases j
      · change a.workCell (multiplyBanks 0) = InputPosition.work (encodeLabel w (x*y))
        rw [show a.workCell (multiplyBanks 0) = mul.workCell 0 from
          bankConfig_cell_image TapeMultiply.machine multiplyBanks mul parkedHeads
            (modulusFrame w p scratch) 0]
        exact register_eq_work _ _
      · change a.workCell 6 = InputPosition.work (encodeLabel w p)
        exact (bankConfig_frame TapeMultiply.machine multiplyBanks mul parkedHeads
          (modulusFrame w p scratch) six_frame).2
      · change a.workCell 7 = InputPosition.work scratch
        exact (bankConfig_frame TapeMultiply.machine multiplyBanks mul parkedHeads
          (modulusFrame w p scratch) seven_frame).2
    · exact (bankConfig_frame RankPhysicalModulo.machine residueBanks r parkedHeads
        a.workCell hi).2.symm
  change (⟨r.state, parked, a.workHead, a.workCell, out⟩ :
    (RankPhysicalModulo.machine.relocateBanks residueBanks).Config) = b
  rw [hCells, hHeads, ← bHeads]
  rfl

/-- The actual finite machine multiplies and reduces two prepared residues.
The final residue is on physical bank zero. -/
theorem execute (word out : List Bool) (parked : Int) (w x y p : Nat)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (hx : x < 2^w) (hy : y < 2^w) (hp : p < 2^w) (hpPos : 0 < p)
    (hProduct : x*y < 2^w) (scratch : List Bool) (hs : scratch.length = w) :
    machine.BoundedSegment word (w+1) (startConfig w x y p scratch out parked)
      (stopConfig w x y p scratch out parked)
      (TapeMultiply.multiplicationSteps w x y + 1 + RankPhysicalModulo.steps w (x*y) p) ∧
    machine.step word (stopConfig w x y p scratch out parked) = none ∧
    (stopConfig w x y p scratch out parked).workCell 0 =
      InputPosition.work (encodeLabel w ((x*y)%p)) := by
  obtain ⟨hMul, stopMul⟩ := TapeMultiply.executeMultiply word out parked w 0 x y 0 hin hx hy
  simp only [Nat.zero_add] at hMul stopMul
  have hFirst := TapeMultiply.machine.relocateBanks_segment multiplyBanks hMul
    (heads := parkedHeads) (cells := modulusFrame w p scratch) (by simp [parkedHeads])
  have hMulStop := TapeMultiply.machine.relocateBanks_step multiplyBanks word
    (TapeMultiply.stopConfig w (x*y) x y parked out) parkedHeads (modulusFrame w p scratch)
  rw [stopMul] at hMulStop
  obtain ⟨hMod, stopMod⟩ :=
    RankPhysicalModulo.execute word out parked hin w (x*y) p hProduct hp hpPos scratch hs
  have hLast := RankPhysicalModulo.machine.relocateBanks_segment residueBanks hMod
    (heads := parkedHeads) (cells := (mulEnd w x y p scratch out parked).workCell)
    (by simp [parkedHeads])
  have hModStop := RankPhysicalModulo.machine.relocateBanks_step residueBanks word
    (RankPhysicalModulo.stages.tag 1 (RankPhysicalModulo.stopConfig w (x*y) p out parked))
    parkedHeads (mulEnd w x y p scratch out parked).workCell
  rw [stopMod] at hModStop
  change (RankPhysicalModulo.machine.relocateBanks residueBanks).BoundedSegment word (w+1)
    (hostedMod (modStart w (x*y) p scratch out parked) w x y p scratch out parked) _ _ at hLast
  rw [← handoff] at hLast
  have hRun := thenSegment TapeMultiply.machine RankPhysicalModulo.machine multiplyBanks residueBanks
    hFirst hMulStop hLast
  refine ⟨hRun, ?_, ?_⟩
  · rw [stopConfig, thenStep_right, hostedMod, hModStop]
    rfl
  · change (hostedMod (RankPhysicalModulo.stages.tag 1
      (RankPhysicalModulo.stopConfig w (x*y) p out parked)) w x y p scratch out parked).workCell
        (residueBanks 0) = _
    rw [hostedMod, bankConfig_cell_image]
    rfl

/-- The machine emits the representative prescribed by the field product. -/
theorem execute_zmod {p : Nat} [Fact p.Prime] (word out : List Bool) (parked : Int)
    (w : Nat) (x y : ZMod p) (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (hp : p < 2^w) (hProduct : x.val*y.val < 2^w)
    (scratch : List Bool) (hs : scratch.length = w) :
    machine.BoundedSegment word (w+1) (startConfig w x.val y.val p scratch out parked)
      (stopConfig w x.val y.val p scratch out parked)
      (TapeMultiply.multiplicationSteps w x.val y.val + 1 +
        RankPhysicalModulo.steps w (x.val*y.val) p) ∧
    machine.step word (stopConfig w x.val y.val p scratch out parked) = none ∧
    (stopConfig w x.val y.val p scratch out parked).workCell 0 =
      InputPosition.work (encodeLabel w (x*y).val) := by
  rw [ZMod.val_mul]
  exact execute word out parked w x.val y.val p hin (x.val_lt.trans hp) (y.val_lt.trans hp)
    hp (Fact.out : p.Prime).pos hProduct scratch hs

end Mathproof.MinimumGeneration.RankPhysicalPrimeProduct
