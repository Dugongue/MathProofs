import Mathproof.MinimumGenerationRankPhysicalSubtract
import Mathproof.MinimumGenerationTapeRegisters
import Mathproof.MinimumGenerationMacroDispatch

/-!
A three-bank modulo machine for prepared bounded words. The live dividend
survives a failed trial subtraction. Every successful trial removes one modulus.
-/

namespace Mathproof.MinimumGeneration.RankPhysicalModulo

open SearchTransducer
open TapeArithmetic (block)
open Lax51Proofs.RamToTM (subBits)

private def embed : Fin 2 ↪ Fin 3 := ⟨Fin.succ, fun _ _ h => Fin.succ_inj.mp h⟩
private abbrev subtract := RankPhysicalSubtract.machine.relocateBanks embed
private abbrev copyIn := TapeRegisters.machine (0 : Fin 3) 2 .copy
private abbrev copyOut := TapeRegisters.machine (2 : Fin 3) 0 .copy

def stages : Stages 3 7 3 where
  first := 0
  entry _ := 0
  transition i :=
    if i = 0 then copyIn.transition else if i = 1 then subtract.transition else copyOut.transition
  next i q := if i = 0 then some 1 else if i = 1 then
    if q = RankPhysicalSubtract.done true then none else some 2
    else some 0

abbrev machine := stages.machine

def bankWords (value modulus scratch : List Bool) (i : Fin 3) : List Bool :=
  if i = 0 then value else if i = 1 then modulus else scratch

def cfg (i : Fin 3) (q : Fin 7) (words : Fin 3 → List Bool)
    (out : List Bool) (parked : Int) : (stages.component i).Config :=
  ⟨q, parked, fun _ => 0, fun j => InputPosition.work (words j), out⟩

private theorem cfg_ext {M : SearchTransducer} {c d : M.Config}
    (hs : c.state = d.state) (hi : c.inputHead = d.inputHead)
    (hh : c.workHead = d.workHead) (hc : c.workCell = d.workCell)
    (ho : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  congr

private theorem work_right (word : List Bool) :
    InputPosition.work word ((word.length : Int) + 1) = none := by
  simp [InputPosition.work]

private theorem work_block (word : List Bool) : block (InputPosition.work word) 1 word := by
  intro i
  have hi : ¬ (1 + (i.val : Int)) ≤ 0 := by omega
  simp [InputPosition.work, hi]

private def copyCfg {src dst : Fin 3} (q : Fin 7) (words : Fin 3 → List Bool)
    (out : List Bool) (parked : Int) : (TapeRegisters.machine src dst .copy).Config :=
  ⟨q, parked, fun _ => 0, fun j => InputPosition.work (words j), out⟩

private theorem copy_word (src dst : Fin 3) (word out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (w : Nat) (words : Fin 3 → List Bool) (lengths : ∀ j, (words j).length = w) :
    let M := TapeRegisters.machine src dst .copy
    let target := copyCfg (src := src) (dst := dst) (TapeRegisters.done true)
      (Function.update words dst (words src)) out parked
    M.BoundedSegment word (w+1) (copyCfg 0 words out parked) target (2*w+3) ∧
      M.step word target = none := by
  let c := copyCfg (src := src) (dst := dst) 0 words out parked
  obtain ⟨d, run, hs, hh, hb, hf⟩ := TapeRegisters.executeCopy word c (words src) (words dst)
    (by rw [lengths, lengths]) rfl rfl
    (by simpa only [c, copyCfg, Int.zero_add] using work_right (words src))
    (by simpa only [c, copyCfg, Int.zero_add, lengths] using work_right (words dst))
    (by simpa only [c, copyCfg, Int.zero_add] using work_block (words src))
    (by simpa only [c, copyCfg, Int.zero_add] using work_block (words dst))
  have hCell : d.workCell = fun j => InputPosition.work ((Function.update words dst (words src)) j) := by
    funext j pos
    by_cases hj : j = dst
    · subst j
      simp only [Function.update_self]
      by_cases hLo : pos < 1
      · rw [hf.cell dst pos (.inr (.inl (by simpa [c, copyCfg] using hLo)))]
        have hZero : pos ≤ 0 := by omega
        simp [c, copyCfg, InputPosition.work, hZero]
      · by_cases hHi : (w : Int) + 1 ≤ pos
        · rw [hf.cell dst pos (.inr (.inr (by simpa [c, copyCfg, lengths] using hHi)))]
          have hp : (words dst).length ≤ (pos-1).toNat := by
            rw [lengths]
            omega
          have hs' : (words src).length ≤ (pos-1).toNat := by rw [lengths]; omega
          change InputPosition.work (words dst) pos = InputPosition.work (words src) pos
          unfold InputPosition.work
          rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none hp, List.getElem?_eq_none hs']
        · have hi : (pos-1).toNat < (words src).length := by rw [lengths]; omega
          have hBit := hb ⟨(pos-1).toNat, hi⟩
          have hInt : (1 : Int) + ((pos-1).toNat : Int) = pos := by omega
          change d.workCell dst (1 + ((pos-1).toNat : Int)) = some (words src)[(pos-1).toNat] at hBit
          rw [hInt, ← List.getElem?_eq_getElem hi] at hBit
          unfold InputPosition.work
          rw [if_neg (by omega)]
          exact hBit
    · simpa [c, copyCfg, Function.update_of_ne hj] using hf.cell j pos (.inl hj)
  have hd : d = copyCfg (src := src) (dst := dst) (TapeRegisters.done true)
      (Function.update words dst (words src)) out parked :=
    cfg_ext hs hf.input hh hCell hf.output
  have hRun := run.boundedSegment (B := w+1) hin (fun j p hLo hHi => by
    change 0 ≤ p at hLo
    simp only [TapeRegisters.finish, c, copyCfg, Int.zero_add, lengths] at hHi
    split at hHi <;> omega)
  rw [hd, lengths] at hRun
  exact ⟨hRun, TapeRegisters.step_done _ _ true rfl⟩

private theorem copy_in (word out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length) (w : Nat)
    (x p scratch : List Bool) (hx : x.length = w) (hp : p.length = w) (hs : scratch.length = w) :
    (stages.component 0).BoundedSegment word (w+1) (cfg 0 0 (bankWords x p scratch) out parked)
      (cfg 0 (TapeRegisters.done true) (bankWords x p x) out parked) (2*w+3) ∧
      (stages.component 0).step word (cfg 0 (TapeRegisters.done true) (bankWords x p x) out parked) = none := by
  have h := copy_word 0 2 word out parked hin w (bankWords x p scratch)
    (by intro j; fin_cases j <;> simp [bankWords, hx, hp, hs])
  have hu : Function.update (bankWords x p scratch) 2 (bankWords x p scratch 0) =
      bankWords x p x := by funext j; fin_cases j <;> rfl
  rw [hu] at h
  exact h

private theorem copy_out (word out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length) (w : Nat)
    (x p scratch : List Bool) (hx : x.length = w) (hp : p.length = w) (hs : scratch.length = w) :
    (stages.component 2).BoundedSegment word (w+1) (cfg 2 0 (bankWords x p scratch) out parked)
      (cfg 2 (TapeRegisters.done true) (bankWords scratch p scratch) out parked) (2*w+3) ∧
      (stages.component 2).step word (cfg 2 (TapeRegisters.done true) (bankWords scratch p scratch) out parked) = none := by
  have h := copy_word 2 0 word out parked hin w (bankWords x p scratch)
    (by intro j; fin_cases j <;> simp [bankWords, hx, hp, hs])
  have hu : Function.update (bankWords x p scratch) 0 (bankWords x p scratch 2) =
      bankWords scratch p scratch := by funext j; fin_cases j <;> rfl
  rw [hu] at h
  exact h

private theorem zero_frame : (0 : Fin 3) ∉ Set.range embed := by
  rintro ⟨i, hi⟩
  have h := congrArg Fin.val hi
  change i.val + 1 = 0 at h
  omega

set_option maxHeartbeats 1000000 in
private theorem subtract_config (q : Fin 7) (x p trial out : List Bool) (parked : Int) :
    RankPhysicalSubtract.machine.bankConfig embed
      (RankPhysicalSubtract.cfg q 0 trial p out parked) (fun _ => 0) (fun _ => InputPosition.work x) =
      cfg 1 q (bankWords x p trial) out parked := by
  let c := RankPhysicalSubtract.cfg q 0 trial p out parked
  let hs : Fin 3 → Int := fun _ => 0
  let ws : Fin 3 → Int → Option Bool := fun _ => InputPosition.work x
  change RankPhysicalSubtract.machine.bankConfig embed c hs ws = _
  apply cfg_ext (M := subtract)
    (c := RankPhysicalSubtract.machine.bankConfig embed c hs ws)
    (d := cfg 1 q (bankWords x p trial) out parked) rfl rfl ?_ ?_ rfl
  · have h0 := bankConfig_frame RankPhysicalSubtract.machine embed c hs ws zero_frame
    have h1 := bankConfig_head_image RankPhysicalSubtract.machine embed c hs ws (0 : Fin 2)
    have h2 := bankConfig_head_image RankPhysicalSubtract.machine embed c hs ws (1 : Fin 2)
    funext j
    fin_cases j
    · exact h0.1
    · exact h1
    · exact h2
  · have h0 := bankConfig_frame RankPhysicalSubtract.machine embed c hs ws zero_frame
    have h1 := bankConfig_cell_image RankPhysicalSubtract.machine embed c hs ws (0 : Fin 2)
    have h2 := bankConfig_cell_image RankPhysicalSubtract.machine embed c hs ws (1 : Fin 2)
    funext j
    fin_cases j
    · exact h0.2
    · exact h1
    · exact h2

private theorem trial_segment (word out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (w x p : Nat) (hx : x < 2^w) (hp : p < 2^w) :
    let val := encodeLabel w x
    let modulus := encodeLabel w p
    let trial := subBits val modulus false
    let src := cfg 1 0 (bankWords val modulus val) out parked
    let dst := cfg 1 (RankPhysicalSubtract.done (decide (x<p))) (bankWords val modulus trial) out parked
    (stages.component 1).BoundedSegment word (w+1) src dst (2*w+3) ∧
      (stages.component 1).step word dst = none := by
  obtain ⟨h, stop⟩ := RankPhysicalSubtract.execute_encoded word out parked w x p hin hx hp
  dsimp only
  have hRun := RankPhysicalSubtract.machine.relocateBanks_segment embed h
    (heads := fun _ => 0) (cells := fun _ => InputPosition.work (encodeLabel w x)) (by simp)
  have hStop := RankPhysicalSubtract.machine.relocateBanks_step embed word
    (RankPhysicalSubtract.cfg (RankPhysicalSubtract.done (decide (x<p))) 0
      (subBits (encodeLabel w x) (encodeLabel w p) false) (encodeLabel w p) out parked)
    (fun _ => 0) (fun _ => InputPosition.work (encodeLabel w x))
  rw [stop] at hStop
  rw [subtract_config, subtract_config] at hRun
  rw [subtract_config] at hStop
  exact ⟨hRun, hStop⟩

/-- The residue is on bank zero. Bank one retains the modulus; bank two holds
the final failed trial, so the returned configuration is specified exactly. -/
def stopConfig (w x p : Nat) (out : List Bool) (parked : Int) : (stages.component 1).Config :=
  let residue := encodeLabel w (x%p)
  let modulus := encodeLabel w p
  cfg 1 (RankPhysicalSubtract.done true) (bankWords residue modulus (subBits residue modulus false)) out parked

/-- One successful pass uses three physical stages and three dispatches.
The final failed trial uses two stages and one dispatch. -/
def steps (w x p : Nat) : Nat :=
  (x/p) * (3*(2*w+3)+3) + (2*(2*w+3)+1)

private theorem steps_success (w x p : Nat) (hp : 0 < p) (h : p ≤ x) :
    (2*w+3) + 1 + ((2*w+3) + 1 + ((2*w+3) + 1 + steps w (x-p) p)) = steps w x p := by
  have hSplit : (x-p) + 1*p = x := by
    rw [Nat.one_mul, Nat.sub_add_cancel h]
  have hQuot : x/p = (x-p)/p + 1 := by
    calc
      _ = ((x-p) + 1*p)/p := congrArg (fun y => y/p) hSplit.symm
      _ = _ := Nat.add_mul_div_right _ _ hp
  unfold steps
  rw [hQuot, Nat.add_mul, Nat.one_mul]
  omega

private theorem run_loop (word out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (w p : Nat) (hp : p < 2^w) (hpPos : 0 < p) (x : Nat) (hx : x < 2^w)
    (scratch : List Bool) (hs : scratch.length = w) :
    ∃ k, stages.Routed word (w+1) 0
      (cfg 0 0 (bankWords (encodeLabel w x) (encodeLabel w p) scratch) out parked)
      1 (stopConfig w x p out parked) k ∧
      (stages.component 1).step word (stopConfig w x p out parked) = none ∧
      k = steps w x p := by
  obtain ⟨copy, copyStop⟩ := copy_in word out parked hin w (encodeLabel w x) (encodeLabel w p)
    scratch (by simp) (by simp) hs
  have hCopyRoute : stages.next 0 (TapeRegisters.done true) = some 1 := rfl
  by_cases hlt : x < p
  · obtain ⟨trial, trialStop⟩ := trial_segment word out parked hin w x p hx hp
    have label : stopConfig w x p out parked =
        cfg 1 (RankPhysicalSubtract.done true)
          (bankWords (encodeLabel w x) (encodeLabel w p)
            (subBits (encodeLabel w x) (encodeLabel w p) false)) out parked := by
      simp [stopConfig, Nat.mod_eq_of_lt hlt]
    rw [label]
    simp only [hlt, decide_true] at trial trialStop
    refine ⟨_, .call copy copyStop hCopyRoute (.finish trial), trialStop, ?_⟩
    simp only [steps, Nat.div_eq_of_lt hlt, Nat.zero_mul, Nat.zero_add]
    omega
  · have hle : p ≤ x := by omega
    have hWidth : x-p < 2^w := (Nat.sub_le x p).trans_lt hx
    have hDecrease : x-p < x := by omega
    obtain ⟨k, tail, tailStop, hSteps⟩ := run_loop word out parked hin w p hp hpPos (x-p) hWidth
      (encodeLabel w (x-p)) (by simp)
    have hMod : x % p = (x-p) % p := Nat.mod_eq_sub_mod hle
    have hDiff : subBits (encodeLabel w x) (encodeLabel w p) false = encodeLabel w (x-p) := by
      rw [← RankPhysicalSubtract.fixedBits_eq_encodeLabel w x hx,
        ← RankPhysicalSubtract.fixedBits_eq_encodeLabel w p hp, ← Lax51Proofs.RamToTM.fixedBits_sub_of_le w hle,
        RankPhysicalSubtract.fixedBits_eq_encodeLabel w (x-p) hWidth]
    obtain ⟨trial, trialStop⟩ := trial_segment word out parked hin w x p hx hp
    simp only [hlt, decide_false, hDiff] at trial trialStop
    obtain ⟨commit, commitStop⟩ := copy_out word out parked hin w (encodeLabel w x) (encodeLabel w p)
      (encodeLabel w (x-p)) (by simp) (by simp) (by simp)
    have trialRoute : stages.next 1 (RankPhysicalSubtract.done false) = some 2 := rfl
    have commitRoute : stages.next 2 (TapeRegisters.done true) = some 0 := rfl
    rw [show stopConfig w x p out parked = stopConfig w (x-p) p out parked by simp [stopConfig, hMod]]
    refine ⟨_, .call copy copyStop hCopyRoute (.call trial trialStop trialRoute
      (.call commit commitStop commitRoute tail)), tailStop, ?_⟩
    rw [hSteps, steps_success w x p hpPos hle]
termination_by x
decreasing_by exact hDecrease

theorem execute (word out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (w x p : Nat) (hx : x < 2^w) (hp : p < 2^w) (hpPos : 0 < p)
    (scratch : List Bool) (hs : scratch.length = w) :
    machine.BoundedSegment word (w+1)
      (stages.tag 0 (cfg 0 0 (bankWords (encodeLabel w x) (encodeLabel w p) scratch) out parked))
      (stages.tag 1 (stopConfig w x p out parked)) (steps w x p) ∧
      machine.step word (stages.tag 1 (stopConfig w x p out parked)) = none := by
  obtain ⟨k, h, hStop, hSteps⟩ := run_loop word out parked hin w p hp hpPos x hx scratch hs
  rw [← hSteps]
  exact stages.routed_stop h hStop (by rfl)

end Mathproof.MinimumGeneration.RankPhysicalModulo
