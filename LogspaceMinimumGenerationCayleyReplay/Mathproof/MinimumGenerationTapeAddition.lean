import Mathproof.MinimumGenerationMacroDispatch
import Mathproof.MinimumGenerationTapeRegisters
import Mathlib.Data.Nat.Bitwise

/-!
# Physical natural addition from bounded register macros
-/

namespace Mathproof.MinimumGeneration.TapeAddition

open SearchTransducer
open TapeArithmetic (block)

private abbrev native (i : Fin 4) : SearchTransducer :=
  if i = 0 then TapeRegisters.machine (1 : Fin 4) 2 .copy
  else if i = 1 then TapeRegisters.machine (2 : Fin 4) 3 .compare
  else if i = 2 then TapeArithmetic.machine (0 : Fin 4) .increment
  else TapeArithmetic.machine (2 : Fin 4) .decrement

private theorem nativeBanks (i : Fin 4) : (native i).workTapes = 4 := by
  unfold native
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

private theorem padFits (i : Fin 4) : (native i).states ≤ 7 := by
  unfold native
  split
  · decide
  · split
    · decide
    · split <;> decide

private def bankEquiv (i : Fin 4) : Fin (native i).workTapes ≃ Fin 4 :=
  finCongr (nativeBanks i)

private def route (i : Fin 4) (q : Fin (native i).states) : Option (Fin 4) :=
  if i = 0 then some 1
  else if i = 1 then if q.val = 5 then none else some 2
  else if i = 2 then some 3 else some 1

/-- Banks 0, 1, 2 and 3 hold the accumulator, addend, mutable countdown,
and a permanent zero, respectively. -/
def stages : Stages 4 7 4 :=
  Stages.ofMachines 0 native padFits (fun i => (bankEquiv i).toEmbedding) route

abbrev machine := stages.machine

def register (width value : ℕ) (atPos : Int) : Option Bool :=
  if atPos < 1 then none else (encodeLabel width value)[(atPos - 1).toNat]?

private theorem register_left (w v : ℕ) : register w v 0 = none := by
  simp [register]

private theorem register_right (w v : ℕ) : register w v ((w : Int) + 1) = none := by
  have h : ¬(w : Int) + 1 < 1 := by omega
  simp [register, h]

private theorem register_block (w v : ℕ) : block (register w v) 1 (encodeLabel w v) := by
  intro i
  have h : ¬ (1 + (i.val : Int)) < 1 := by omega
  have h' : (1 + (i.val : Int) - 1).toNat = i.val := by omega
  simp only [register, h, if_false, h']
  exact List.getElem?_eq_getElem i.isLt

private def valueAt (x y z : ℕ) (bank : Fin 4) : ℕ :=
  if bank = 0 then x else if bank = 1 then y else if bank = 2 then z else 0

def cells (w x y z : ℕ) (bank : Fin 4) : Int → Option Bool :=
  register w (valueAt x y z bank)

private def nativeCfg (i : Fin 4) (q : Fin (native i).states)
    (w x y z : ℕ) (h : Int) (out : List Bool) : (native i).Config :=
  ⟨q, h, fun _ => 0, fun t => cells w x y z (bankEquiv i t), out⟩

/-- The exact physical configuration at a native macro boundary. -/
def cfg (i : Fin 4) (q : Fin (native i).states)
    (w x y z : ℕ) (h : Int) (out : List Bool) : (stages.component i).Config :=
  ⟨q.castLE (padFits i), h, fun _ => 0, cells w x y z, out⟩

private theorem cfg_ext {M : SearchTransducer} {c d : M.Config}
    (state : c.state = d.state) (ih : c.inputHead = d.inputHead)
    (wh : c.workHead = d.workHead) (wc : c.workCell = d.workCell)
    (out : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  congr

private theorem cfg_lift (i : Fin 4) (q : Fin (native i).states)
    (w x y z : ℕ) (h : Int) (out : List Bool) :
    cfg i q w x y z h out =
      (native i).padConfig (padFits i) (bankEquiv i).toEmbedding
        ((native i).bankConfig (bankEquiv i).toEmbedding (nativeCfg i q w x y z h out)
          (fun _ => 0) (fun _ _ => none)) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext t
    let b := (bankEquiv i).symm t
    have he : (bankEquiv i).toEmbedding b = t := (bankEquiv i).apply_symm_apply t
    change 0 = ((native i).bankConfig (bankEquiv i).toEmbedding
      (nativeCfg i q w x y z h out) (fun _ => 0) (fun _ _ => none)).workHead t
    rw [← he, bankConfig_head_image]
    rfl
  · funext t
    let b := (bankEquiv i).symm t
    have he : (bankEquiv i).toEmbedding b = t := (bankEquiv i).apply_symm_apply t
    change cells w x y z t = ((native i).bankConfig (bankEquiv i).toEmbedding
      (nativeCfg i q w x y z h out) (fun _ => 0) (fun _ _ => none)).workCell t
    rw [← he, bankConfig_cell_image]
    rfl
  · rfl

private theorem cfg_handoff (i j : Fin 4) (q : Fin (native i).states)
    (w x y z : ℕ) (h : Int) (out : List Bool) :
    stages.enter j (cfg i q w x y z h out) =
      cfg j (native j).initialState w x y z h out := rfl

private theorem cfg_route (i : Fin 4) (q : Fin (native i).states)
    (w x y z : ℕ) (h : Int) (out : List Bool) :
    stages.next i (cfg i q w x y z h out).state = route i q :=
  Stages.ofMachines_next_at 0 native padFits (fun i => (bankEquiv i).toEmbedding) route i q

private theorem liftRun (i : Fin 4) {q r : Fin (native i).states} {w x y z x' y' z' k : ℕ}
    {word out : List Bool} {h : Int}
    (run : (native i).BoundedSegment word (w + 1)
      (nativeCfg i q w x y z h out) (nativeCfg i r w x' y' z' h out) k) :
    (stages.component i).BoundedSegment word (w + 1)
      (cfg i q w x y z h out) (cfg i r w x' y' z' h out) k := by
  rw [cfg_lift, cfg_lift]
  apply (native i).padMachine_segment
  exact (native i).relocateBanks_segment (bankEquiv i).toEmbedding run (by simp)

private theorem liftHalt (i : Fin 4) {q : Fin (native i).states} {w x y z : ℕ}
    {word out : List Bool} {h : Int}
    (stop : (native i).step word (nativeCfg i q w x y z h out) = none) :
    (stages.component i).step word (cfg i q w x y z h out) = none := by
  rw [cfg_lift]
  change ((native i).padMachine (padFits i) (bankEquiv i).toEmbedding).step word _ = _
  rw [padMachine_step, relocateBanks_step, stop]
  rfl

private theorem preserveCells {w : ℕ} {old next : Fin 4 → ℕ}
    (t : Fin 4) (same : ∀ b, b ≠ t → old b = next b)
    (after : Fin 4 → Int → Option Bool)
    (blockHere : block (after t) 1 (encodeLabel w (next t)))
    (frame : ∀ b j, b ≠ t ∨ j < 1 ∨ (w : Int) + 1 ≤ j → after b j = register w (old b) j) :
    after = fun b => register w (next b) := by
  funext b j
  by_cases hb : b = t
  · subst b
    by_cases low : j < 1
    · rw [frame t j (.inr (.inl low))]
      simp [register, low]
    · by_cases high : (w : Int) + 1 ≤ j
      · rw [frame t j (.inr (.inr high))]
        have hIdx : w ≤ (j - 1).toNat := by omega
        simp only [register, low, if_false, List.getElem?_eq_none (by simpa using hIdx :
          (encodeLabel w (old t)).length ≤ (j - 1).toNat),
          List.getElem?_eq_none (by simpa using hIdx :
            (encodeLabel w (next t)).length ≤ (j - 1).toNat)]
      · let idx : Fin (encodeLabel w (next t)).length := ⟨(j - 1).toNat, by
            rw [length_encodeLabel]
            omega⟩
        have hi : (1 : Int) + idx.val = j := by dsimp [idx]; omega
        rw [← hi]
        exact (blockHere idx).trans (register_block w (next t) idx).symm
  · rw [frame b j (.inl hb), same b hb]

private theorem windows {w : ℕ} {a : Int} (hl : 0 ≤ a) (hh : a ≤ (w : Int) + 1) :
    a.natAbs ≤ w + 1 := by omega

private theorem label_zero (w : ℕ) : encodeLabel w 0 = List.replicate w false := by
  apply List.ext_getElem?
  intro i
  by_cases h : i < w
  · simp [encodeLabel, h]
  · have h' : w ≤ i := by omega
    rw [List.getElem?_eq_none (by simpa using h' : (encodeLabel w 0).length ≤ i)]
    exact (List.getElem?_eq_none (by simpa using h' : (List.replicate w false).length ≤ i)).symm

private theorem label_zero_iff {w z : ℕ} (cap : z < 2 ^ w) :
    encodeLabel w z = List.replicate w false ↔ z = 0 := by
  constructor
  · intro h
    rw [← label_zero] at h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · have h' := congrArg (fun l : List Bool => l[i]?) h
      simpa [encodeLabel, List.getElem?_eq_getElem (by simpa using hi :
        i < (List.range w).length)] using h'
    · have hle : w ≤ i := by omega
      simp [Nat.testBit_eq_false_of_lt (cap.trans_le (Nat.pow_le_pow_right (by decide) hle))]
  · rintro rfl
    exact label_zero w


private theorem copySegment {word out : List Bool} {h : Int} {w x y z : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) :
    (stages.component 0).BoundedSegment word (w + 1)
      (cfg 0 (native 0).initialState w x y z h out) (cfg 0 (TapeRegisters.done true) w x y y h out) (2 * w + 3) ∧
    (stages.component 0).step word (cfg 0 (TapeRegisters.done true) w x y y h out) = none := by
  let c := nativeCfg 0 (native 0).initialState w x y z h out
  have hy : (encodeLabel w y).length = w := length_encodeLabel w y
  obtain ⟨d, run, hstate, heads, bits, frame⟩ :=
    TapeRegisters.executeCopy (source := (1 : Fin 4)) (target := (2 : Fin 4)) word c
      (encodeLabel w y) (encodeLabel w z) (by simp) rfl (register_left w z)
      (by simp only [hy, Int.zero_add, c, nativeCfg, cells]; exact register_right w _)
      (by simp only [hy, Int.zero_add, c, nativeCfg, cells]; exact register_right w _)
      (register_block w y) (register_block w z)
  have hc : d = nativeCfg 0 (TapeRegisters.done true) w x y y h out := by
    apply cfg_ext (d := nativeCfg 0 (TapeRegisters.done true) w x y y h out) hstate frame.input heads ?_ frame.output
    have he (t : Fin 4) : bankEquiv 0 t = t := Fin.ext rfl
    have hCells := preserveCells (old := valueAt x y z) (next := valueAt x y y) 2
      (fun t ht => by simp [valueAt, ht]) d.workCell
      (by simpa [c, nativeCfg, valueAt] using bits)
      (fun t p hp => by
        simpa only [c, nativeCfg, cells, he] using
          frame.cell t p (by simpa only [hy, c, nativeCfg, Int.zero_add] using hp))
    funext t p
    change d.workCell t p = cells w x y y (bankEquiv 0 t) p
    rw [he t]
    exact congrFun (congrFun hCells t) p
  have hb := run.boundedSegment (B := w + 1) hin (fun t j hlo hhi => by
    apply windows hlo
    simp only [TapeRegisters.finish, c, nativeCfg, hy, Int.zero_add] at hhi
    split at hhi <;> omega)
  rw [hc, hy] at hb
  exact ⟨liftRun 0 hb, liftHalt 0 (TapeRegisters.step_done _ _ true rfl)⟩

private theorem compareSegment {word out : List Bool} {h : Int} {w x y z : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (hz : z < 2 ^ w) :
    (stages.component 1).BoundedSegment word (w + 1)
      (cfg 1 (native 1).initialState w x y z h out) (cfg 1 (TapeRegisters.done (decide (z = 0))) w x y z h out) (2 * w + 3) ∧
    (stages.component 1).step word (cfg 1 (TapeRegisters.done (decide (z = 0))) w x y z h out) = none := by
  let c := nativeCfg 1 (native 1).initialState w x y z h out
  have hzLen : (encodeLabel w z).length = w := length_encodeLabel _ _
  obtain ⟨d, zero, run, hstate, result, heads, frame, input, output⟩ :=
    TapeRegisters.executeIsZero (source := (2 : Fin 4)) (target := (3 : Fin 4)) word c
      (encodeLabel w z) rfl (register_left w 0)
      (by simp only [hzLen, Int.zero_add, c, nativeCfg, cells]; exact register_right w _)
      (by simp only [hzLen, Int.zero_add, c, nativeCfg, cells]; exact register_right w _)
      (register_block w z) (by rw [hzLen, ← label_zero]; exact register_block w 0)
  have hzEq : zero = decide (z = 0) := by
    rw [hzLen, label_zero_iff hz] at result
    cases zero <;> simp_all
  have hc : d = nativeCfg 1 (TapeRegisters.done (decide (z = 0))) w x y z h out := by
    apply cfg_ext (d := nativeCfg 1 (TapeRegisters.done (decide (z = 0))) w x y z h out) _ input heads frame output
    exact hstate.trans (congrArg TapeRegisters.done hzEq)
  have hb := run.boundedSegment (B := w + 1) hin (fun t j hlo hhi => by
    apply windows hlo
    simp only [TapeRegisters.finish, c, nativeCfg, hzLen, Int.zero_add] at hhi
    split at hhi <;> omega)
  rw [hc, hzLen] at hb
  exact ⟨liftRun 1 hb, liftHalt 1 (TapeRegisters.step_done _ _ (decide (z = 0)) rfl)⟩

private abbrev genericArithmeticCfg (t : Fin 4) (op : TapeArithmetic.Operation)
    (w : ℕ) (values : Fin 4 → ℕ) (h : Int) (out : List Bool) (q : Fin 5) :
    TapeArithmetic.Config t op :=
  ⟨q, h, fun _ => 0, fun b => register w (values b), out⟩

private theorem arithmeticSegment {word out : List Bool} {h : Int} {w : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length)
    (t : Fin 4) (op : TapeArithmetic.Operation) (old next : Fin 4 → ℕ)
    (same : ∀ j, j ≠ t → old j = next j)
    (value : TapeArithmetic.ripple op true (encodeLabel w (old t)) = encodeLabel w (next t)) :
    let c := genericArithmeticCfg t op w old h out 0
    let d := genericArithmeticCfg t op w next h out 4
    (TapeArithmetic.machine t op).BoundedSegment word (w + 1) c d (2 * w + 3) ∧
      (TapeArithmetic.machine t op).step word d = none := by
  let c := genericArithmeticCfg t op w old h out 0
  let final := genericArithmeticCfg t op w next h out 4
  have hw : (encodeLabel w (old t)).length = w := length_encodeLabel _ _
  obtain ⟨d, run, hstate, head, bits, frame⟩ :=
    TapeArithmetic.execute word c (encodeLabel w (old t)) rfl (register_left w (old t))
      (by simpa only [genericArithmeticCfg, c, Int.zero_add, hw] using register_right w (old t))
      (register_block w (old t))
  have hc : d = final := by
    apply cfg_ext (d := final) hstate frame.input ?_ ?_ frame.output
    · funext j
      by_cases hj : j = t
      · subst j
        exact head
      · exact frame.heads j hj
    · apply preserveCells t same d.workCell
      · simpa only [value, c, Int.zero_add] using bits
      · intro j p hp
        exact frame.cells j p (by simpa only [hw, genericArithmeticCfg, c, Int.zero_add] using hp)
  have hb := TapeRegisters.arithmeticBoundedSegment (B := w + 1) run hin
    (fun j hlo hhi => windows hlo (by simpa only [hw, genericArithmeticCfg, c, Int.zero_add] using hhi))
    (fun _ _ => by simp [c])
  rw [hc, hw] at hb
  exact ⟨hb, TapeArithmetic.step_done _ _ rfl⟩

private theorem incrementSegment {word out : List Bool} {h : Int} {w x y z : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) :
    (stages.component 2).BoundedSegment word (w + 1)
      (cfg 2 (native 2).initialState w x y z h out) (cfg 2 (4 : Fin 5) w (x + 1) y z h out) (2 * w + 3) ∧
    (stages.component 2).step word (cfg 2 (4 : Fin 5) w (x + 1) y z h out) = none := by
  obtain ⟨run, stop⟩ := arithmeticSegment hin (0 : Fin 4) .increment
    (valueAt x y z) (valueAt (x + 1) y z) (fun j hj => by simp [valueAt, hj])
    (by simpa [valueAt] using TapeArithmetic.ripple_increment_encodeLabel w x)
  exact ⟨liftRun 2 run, liftHalt 2 stop⟩

private theorem decrementSegment {word out : List Bool} {h : Int} {w x y z : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (positive : 0 < z) :
    (stages.component 3).BoundedSegment word (w + 1)
      (cfg 3 (native 3).initialState w x y z h out) (cfg 3 (4 : Fin 5) w x y (z - 1) h out) (2 * w + 3) ∧
    (stages.component 3).step word (cfg 3 (4 : Fin 5) w x y (z - 1) h out) = none := by
  obtain ⟨run, stop⟩ := arithmeticSegment hin (2 : Fin 4) .decrement
    (valueAt x y z) (valueAt x y (z - 1)) (fun j hj => by simp [valueAt, hj])
    (by simpa [valueAt] using TapeArithmetic.ripple_decrement_encodeLabel w z positive)
  exact ⟨liftRun 3 run, liftHalt 3 stop⟩

private def stride (w : ℕ) : ℕ := 2 * w + 3

private def loopLength (w z : ℕ) : ℕ := ((stride w + 1) * z) * 3 + stride w

private theorem loopRoute {word out : List Bool} {h : Int} {w : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (x y z : ℕ) (hz : z < 2 ^ w) :
    stages.Routed word (w + 1)
      1 (cfg 1 (native 1).initialState w x y z h out)
      1 (cfg 1 (TapeRegisters.done true) w (x + z) y 0 h out)
      (loopLength w z) := by
  induction z generalizing x with
  | zero =>
    have hbase := (compareSegment (out := out) (x := x) (y := y) hin hz).1
    simpa [loopLength, stride] using Stages.Routed.finish hbase
  | succ z ih =>
    obtain ⟨compare, compareStop⟩ := compareSegment (out := out) (x := x) (y := y) hin hz
    have hcmp : stages.next 1 (cfg 1 (TapeRegisters.done (decide (z + 1 = 0)))
        w x y (z + 1) h out).state = some 2 := by
      rw [cfg_route]
      simp [route, TapeRegisters.done, native]
    obtain ⟨inc, incStop⟩ := incrementSegment (out := out) (x := x) (y := y) (z := z + 1) (w := w) hin
    obtain ⟨dec, decStop⟩ := decrementSegment (out := out) (x := x + 1) (y := y) (z := z + 1)
      (w := w) hin (by omega)
    have hincr : stages.next 2 (cfg 2 (4 : Fin 5) w (x + 1) y (z + 1) h out).state = some 3 := by
      rw [cfg_route]
      rfl
    have hdecr : stages.next 3 (cfg 3 (4 : Fin 5) w (x + 1) y ((z + 1) - 1) h out).state = some 1 := by
      rw [cfg_route]
      rfl
    have hl : loopLength w (z + 1) =
        stride w + 1 + (stride w + 1 + (stride w + 1 + loopLength w z)) := by
      simp only [loopLength, Nat.mul_succ, Nat.add_mul]
      omega
    rw [hl]
    refine Stages.Routed.call (j := 2) compare compareStop hcmp ?_
    rw [cfg_handoff]
    refine Stages.Routed.call (j := 3) inc incStop hincr ?_
    rw [cfg_handoff]
    refine Stages.Routed.call (j := 1) dec decStop hdecr ?_
    rw [cfg_handoff]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (x + 1) (by omega)

def additionSteps (width addend : ℕ) : ℕ := stride width + 1 + loopLength width addend

/-- Entry with the accumulator, addend, countdown scratch and zero bank. -/
def startConfig (w x y z : ℕ) (h : Int) (out : List Bool) : machine.Config :=
  stages.tag 0 (cfg 0 (native 0).initialState w x y z h out)

/-- Exit with both operands represented in the prescribed output banks.
The preserved addend and cleared countdown have the original width. -/
def stopConfig (w sum y : ℕ) (h : Int) (out : List Bool) : machine.Config :=
  stages.tag 1 (cfg 1 (TapeRegisters.done true) w sum y 0 h out)

/-- Starting from four prepared registers, the actual transducer adds the
second register into the first, clears the countdown, preserves the addend
and zero banks, and halts without moving the input head or emitting output. -/
theorem executeAddition (word out : List Bool) (h : Int) (w x y z : ℕ)
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (hy : y < 2 ^ w) :
    machine.BoundedSegment word (w + 1)
      (startConfig w x y z h out)
      (stopConfig w (x + y) y h out)
      (additionSteps w y) ∧
    machine.step word (stopConfig w (x + y) y h out) = none := by
  obtain ⟨copy, copyStop⟩ := copySegment (x := x) (y := y) (z := z) (w := w) hin
  obtain ⟨_, stop⟩ := compareSegment (out := out) (x := x + y) (y := y) (z := 0) (w := w) hin
    (Nat.two_pow_pos w)
  have haltRoute : stages.next 1 (cfg 1 (TapeRegisters.done true) w (x+y) y 0 h out).state = none := by
    rw [cfg_route]
    rfl
  refine stages.routed_stop (Stages.Routed.call (j := 1) copy copyStop ?_ ?_) ?_ haltRoute
  · rw [cfg_route]
    rfl
  · rw [cfg_handoff]
    exact loopRoute hin x y y hy
  · simpa using stop
end Mathproof.MinimumGeneration.TapeAddition
