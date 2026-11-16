import Mathproof.MinimumGenerationTapeAddition
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Multiply-and-accumulate on prepared binary tape registers
-/

namespace Mathproof.MinimumGeneration.TapeMultiply

open SearchTransducer
open TapeArithmetic (block)

private abbrev native (i : Fin 4) : SearchTransducer :=
  if i = 0 then TapeRegisters.machine (4 : Fin 6) 5 .copy
  else if i = 1 then TapeRegisters.machine (5 : Fin 6) 3 .compare
  else if i = 2 then TapeAddition.machine
  else TapeArithmetic.machine (5 : Fin 6) .decrement

private theorem fitsBanks (i : Fin 4) : (native i).workTapes ≤ 6 := by
  unfold native
  split
  · decide
  · split
    · decide
    · split <;> decide

private theorem fitsStates (i : Fin 4) : (native i).states ≤ 28 := by
  unfold native
  split
  · decide
  · split
    · decide
    · split <;> decide

private def banks (i : Fin 4) : Fin (native i).workTapes ↪ Fin 6 :=
  ⟨fun a => a.castLE (fitsBanks i), fun _ _ h => Fin.ext (congrArg (fun t : Fin 6 => t.val) h)⟩

private def route (i : Fin 4) (q : Fin (native i).states) : Option (Fin 4) :=
  if i = 0 then some 1
  else if i = 1 then if q.val = 5 then none else some 2
  else if i = 2 then some 3 else some 1

/-- Banks 0, 1, 2, 3, 4 and 5 contain the accumulator, first factor,
addition scratch, permanent zero, second factor and outer countdown. -/
def stages : Stages 4 28 6 :=
  Stages.ofMachines 0 native fitsStates banks route

abbrev machine := stages.machine

abbrev register := TapeAddition.register

private theorem register_left (w v : ℕ) : register w v 0 = none := by
  simp [register, TapeAddition.register]

private theorem register_right (w v : ℕ) : register w v ((w : Int) + 1) = none := by
  have h : ¬(w : Int) + 1 < 1 := by omega
  simp [register, TapeAddition.register, h]

private theorem register_block (w v : ℕ) : block (register w v) 1 (encodeLabel w v) := by
  intro i
  have h : ¬ (1 + (i.val : Int)) < 1 := by omega
  have h' : (1 + (i.val : Int) - 1).toNat = i.val := by omega
  simp only [register, TapeAddition.register, h, if_false, h']
  exact List.getElem?_eq_getElem i.isLt


private def valueAt (a x y z : ℕ) (bank : Fin 6) : ℕ :=
  if bank = 0 then a else if bank = 1 then x else if bank = 4 then y
  else if bank = 5 then z else 0

def cells (w a x y z : ℕ) (bank : Fin 6) : Int → Option Bool :=
  register w (valueAt a x y z bank)

private def nativeCfg (i : Fin 4) (q : Fin (native i).states)
    (w a x y z : ℕ) (h : Int) (out : List Bool) : (native i).Config :=
  ⟨q, h, fun _ => 0, fun t => cells w a x y z (banks i t), out⟩

private def cfg (i : Fin 4) (q : Fin (native i).states)
    (w a x y z : ℕ) (h : Int) (out : List Bool) : (stages.component i).Config :=
  ⟨q.castLE (fitsStates i), h, fun _ => 0, cells w a x y z, out⟩

private theorem cfg_ext {M : SearchTransducer} {c d : M.Config}
    (state : c.state = d.state) (ih : c.inputHead = d.inputHead)
    (wh : c.workHead = d.workHead) (wc : c.workCell = d.workCell)
    (out : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  congr


private theorem cfg_lift (i : Fin 4) (q : Fin (native i).states)
    (w a x y z : ℕ) (h : Int) (out : List Bool) (frame : Fin 6 → Int → Option Bool)
    (hf : ∀ t ∉ Set.range (banks i), frame t = cells w a x y z t) :
    cfg i q w a x y z h out =
      (native i).padConfig (fitsStates i) (banks i)
        ((native i).bankConfig (banks i) (nativeCfg i q w a x y z h out) (fun _ => 0) frame) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext t
    change 0 = ((native i).bankConfig (banks i)
      (nativeCfg i q w a x y z h out) (fun _ => 0) frame).workHead t
    by_cases ht : t ∈ Set.range (banks i)
    · obtain ⟨b, rfl⟩ := ht
      rw [bankConfig_head_image]
      rfl
    · rw [((native i).bankConfig_frame (banks i) _ _ _ ht).1]
  · funext t
    change cells w a x y z t = ((native i).bankConfig (banks i)
      (nativeCfg i q w a x y z h out) (fun _ => 0) frame).workCell t
    by_cases ht : t ∈ Set.range (banks i)
    · obtain ⟨b, rfl⟩ := ht
      rw [bankConfig_cell_image]
      rfl
    · rw [((native i).bankConfig_frame (banks i) _ _ _ ht).2, hf t ht]
  · rfl

private theorem cfg_handoff (i j : Fin 4) (q : Fin (native i).states)
    (w a x y z : ℕ) (h : Int) (out : List Bool) :
    stages.enter j (cfg i q w a x y z h out) =
      cfg j (native j).initialState w a x y z h out := rfl

private theorem cfg_route (i : Fin 4) (q : Fin (native i).states)
    (w a x y z : ℕ) (h : Int) (out : List Bool) :
    stages.next i (cfg i q w a x y z h out).state = route i q :=
  Stages.ofMachines_next_at 0 native fitsStates banks route i q

private theorem liftRun (i : Fin 4) {q r : Fin (native i).states} {w a a' x y z z' k : ℕ}
    {word out : List Bool} {h : Int}
    (run : (native i).BoundedSegment word (w + 1)
      (nativeCfg i q w a x y z h out) (nativeCfg i r w a' x y z' h out) k)
    (frame : ∀ t ∉ Set.range (banks i), cells w a x y z t = cells w a' x y z' t) :
    (stages.component i).BoundedSegment word (w + 1)
      (cfg i q w a x y z h out) (cfg i r w a' x y z' h out) k := by
  rw [cfg_lift i q w a x y z h out (cells w a x y z) (fun _ _ => rfl),
    cfg_lift i r w a' x y z' h out (cells w a x y z) frame]
  apply (native i).padMachine_segment
  exact (native i).relocateBanks_segment (banks i) run (by simp)

private theorem liftHalt (i : Fin 4) {q : Fin (native i).states} {w a x y z : ℕ}
    {word out : List Bool} {h : Int}
    (stop : (native i).step word (nativeCfg i q w a x y z h out) = none) :
    (stages.component i).step word (cfg i q w a x y z h out) = none := by
  rw [cfg_lift i q w a x y z h out (cells w a x y z) (fun _ _ => rfl)]
  change ((native i).padMachine (fitsStates i) (banks i)).step word _ = _
  rw [padMachine_step, relocateBanks_step, stop]
  rfl

private theorem fullLayout (i : Fin 4) (hw : (native i).workTapes = 6) (t : Fin 6) :
    t ∈ Set.range (banks i) := by
  refine ⟨t.cast hw.symm, Fin.ext ?_⟩
  rfl

private theorem fullLayout_id (i : Fin 4) (hw : (native i).workTapes = 6)
    (j : Fin (native i).workTapes) : banks i j = j.cast hw := Fin.ext rfl

private theorem preserveCells {w : ℕ} {old next : Fin 6 → ℕ}
    (t : Fin 6) (same : ∀ b, b ≠ t → old b = next b)
    (after : Fin 6 → Int → Option Bool)
    (blockHere : block (after t) 1 (encodeLabel w (next t)))
    (frame : ∀ b j, b ≠ t ∨ j < 1 ∨ (w : Int) + 1 ≤ j → after b j = register w (old b) j) :
    after = fun b => register w (next b) := by
  funext b j
  by_cases hb : b = t
  · subst b
    by_cases low : j < 1
    · rw [frame t j (.inr (.inl low))]
      simp [register, TapeAddition.register, low]
    · by_cases high : (w : Int) + 1 ≤ j
      · rw [frame t j (.inr (.inr high))]
        have hIdx : w ≤ (j - 1).toNat := by omega
        simp only [register, TapeAddition.register, low, if_false, List.getElem?_eq_none (by simpa using hIdx :
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



private theorem copySegment {word out : List Bool} {h : Int} {w a x y z : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) :
    (stages.component 0).BoundedSegment word (w + 1)
      (cfg 0 (native 0).initialState w a x y z h out)
      (cfg 0 (TapeRegisters.done true) w a x y y h out) (2 * w + 3) ∧
    (stages.component 0).step word (cfg 0 (TapeRegisters.done true) w a x y y h out) = none := by
  let c := nativeCfg 0 (native 0).initialState w a x y z h out
  have hy : (encodeLabel w y).length = w := length_encodeLabel _ _
  obtain ⟨d, run, state, heads, bits, frame⟩ :=
    TapeRegisters.executeCopy (source := (4 : Fin 6)) (target := (5 : Fin 6)) word c
      (encodeLabel w y) (encodeLabel w z) (by simp) rfl (register_left w z)
      (by simp only [hy, Int.zero_add, c, nativeCfg, cells]; exact register_right w _)
      (by simp only [hy, Int.zero_add, c, nativeCfg, cells]; exact register_right w _)
      (register_block w y) (register_block w z)
  have hc : d = nativeCfg 0 (TapeRegisters.done true) w a x y y h out := by
    apply cfg_ext (d := nativeCfg 0 (TapeRegisters.done true) w a x y y h out)
      state frame.input heads ?_ frame.output
    have he (t : Fin 6) : banks 0 t = t := Fin.ext rfl
    have hCells := preserveCells (old := valueAt a x y z) (next := valueAt a x y y) 5
      (fun t ht => by simp [valueAt, ht]) d.workCell
      (by simpa [c, nativeCfg, valueAt] using bits)
      (fun t p hp => by
        simpa only [c, nativeCfg, cells, he] using
          frame.cell t p (by simpa only [hy, c, nativeCfg, Int.zero_add] using hp))
    funext t p
    change d.workCell t p = cells w a x y y (banks 0 t) p
    rw [he t]
    exact congrFun (congrFun hCells t) p
  have hb := run.boundedSegment (B := w + 1) hin (fun t j hlo hhi => by
    apply windows hlo
    simp only [TapeRegisters.finish, c, nativeCfg, hy, Int.zero_add] at hhi
    split at hhi <;> omega)
  rw [hc, hy] at hb
  exact ⟨liftRun 0 hb (fun t ht => (ht (fullLayout 0 rfl t)).elim),
    liftHalt 0 (TapeRegisters.step_done _ _ true rfl)⟩

private theorem compareSegment {word out : List Bool} {h : Int} {w a x y z : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (hz : z < 2 ^ w) :
    (stages.component 1).BoundedSegment word (w + 1)
      (cfg 1 (native 1).initialState w a x y z h out)
      (cfg 1 (TapeRegisters.done (decide (z = 0))) w a x y z h out) (2 * w + 3) ∧
    (stages.component 1).step word
      (cfg 1 (TapeRegisters.done (decide (z = 0))) w a x y z h out) = none := by
  let c := nativeCfg 1 (native 1).initialState w a x y z h out
  have hzLen : (encodeLabel w z).length = w := length_encodeLabel _ _
  obtain ⟨d, zero, run, state, result, heads, frame, input, output⟩ :=
    TapeRegisters.executeIsZero (source := (5 : Fin 6)) (target := (3 : Fin 6)) word c
      (encodeLabel w z) rfl (register_left w 0)
      (by simp only [hzLen, Int.zero_add, c, nativeCfg, cells]; exact register_right w _)
      (by simp only [hzLen, Int.zero_add, c, nativeCfg, cells]; exact register_right w _)
      (register_block w z) (by rw [hzLen, ← label_zero]; exact register_block w 0)
  have hzEq : zero = decide (z = 0) := by
    rw [hzLen, label_zero_iff hz] at result
    cases zero <;> simp_all
  have hc : d = nativeCfg 1 (TapeRegisters.done (decide (z = 0))) w a x y z h out := by
    apply cfg_ext (d := nativeCfg 1 (TapeRegisters.done (decide (z = 0))) w a x y z h out)
      _ input heads frame output
    exact state.trans (congrArg TapeRegisters.done hzEq)
  have hb := run.boundedSegment (B := w + 1) hin (fun t j hlo hhi => by
    apply windows hlo
    simp only [TapeRegisters.finish, c, nativeCfg, hzLen, Int.zero_add] at hhi
    split at hhi <;> omega)
  rw [hc, hzLen] at hb
  exact ⟨liftRun 1 hb (fun _ _ => rfl),
    liftHalt 1 (TapeRegisters.step_done _ _ (decide (z = 0)) rfl)⟩

private def addedState : Fin (native 2).states :=
  (TapeAddition.stopConfig 0 0 0 0 []).state

private theorem addSegment {word out : List Bool} {h : Int} {w a x y z : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (hx : x < 2 ^ w) :
    (stages.component 2).BoundedSegment word (w + 1)
      (cfg 2 (native 2).initialState w a x y z h out)
      (cfg 2 addedState w (a + x) x y z h out) (TapeAddition.additionSteps w x) ∧
    (stages.component 2).step word (cfg 2 addedState w (a + x) x y z h out) = none := by
  have enter : TapeAddition.startConfig w a x 0 h out =
      nativeCfg 2 (native 2).initialState w a x y z h out := by
    apply cfg_ext <;> try rfl
    funext b
    have he : banks 2 b = b.castLE (by decide) := Fin.ext rfl
    change TapeAddition.cells w a x 0 b = cells w a x y z (banks 2 b)
    rw [he]
    fin_cases b <;> rfl
  have finish : TapeAddition.stopConfig w (a + x) x h out =
      nativeCfg 2 addedState w (a+x) x y z h out := by
    apply cfg_ext <;> try rfl
    funext b
    have he : banks 2 b = b.castLE (by decide) := Fin.ext rfl
    change TapeAddition.cells w (a+x) x 0 b = cells w (a+x) x y z (banks 2 b)
    rw [he]
    fin_cases b <;> rfl
  obtain ⟨hr, hs⟩ := TapeAddition.executeAddition word out h w a x 0 hin hx
  rw [enter, finish] at hr
  rw [finish] at hs
  refine ⟨liftRun 2 hr ?_, liftHalt 2 hs⟩
  intro t ht
  have ht0 : t ≠ 0 := by
    intro hzero
    subst t
    exact ht ⟨(0 : Fin 4), Fin.ext rfl⟩
  simp [cells, valueAt, ht0]

private theorem decrementSegment {word out : List Bool} {h : Int} {w a x y z : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (pos : 0 < z) :
    (stages.component 3).BoundedSegment word (w + 1)
      (cfg 3 (native 3).initialState w a x y z h out)
      (cfg 3 (4 : Fin 5) w a x y (z - 1) h out) (2 * w + 3) ∧
    (stages.component 3).step word (cfg 3 (4 : Fin 5) w a x y (z - 1) h out) = none := by
  let c := nativeCfg 3 (native 3).initialState w a x y z h out
  let d' := nativeCfg 3 (4 : Fin 5) w a x y (z - 1) h out
  obtain ⟨d, run, state, heads, bits, frame⟩ :=
    TapeArithmetic.executeDecrement (bank := (5 : Fin 6)) word c w z pos rfl (register_left w z)
      (by simp only [c, nativeCfg, cells, Int.zero_add]; exact register_right w _)
      (register_block w z)
  have hc : d = d' := by
    apply cfg_ext (d := d') state frame.input ?_ ?_ frame.output
    · funext t
      by_cases ht : t = (5 : Fin 6)
      · subst t
        exact heads
      · exact frame.heads t ht
    · have he (t : Fin 6) : banks 3 t = t := Fin.ext rfl
      have hCells := preserveCells (old := valueAt a x y z) (next := valueAt a x y (z-1)) 5
        (fun t ht => by simp [valueAt, ht]) d.workCell
        (by simpa [c, nativeCfg, valueAt] using bits)
        (fun t p hp => by
          simpa only [c, nativeCfg, cells, he] using
            frame.cells t p (by simpa only [c, nativeCfg, Int.zero_add] using hp))
      funext t p
      change d.workCell t p = cells w a x y (z-1) (banks 3 t) p
      rw [he t]
      exact congrFun (congrFun hCells t) p
  have hb := TapeRegisters.arithmeticBoundedSegment (B := w + 1) run hin
    (fun j hlo hhi => windows hlo (by simpa only [c, nativeCfg, Int.zero_add] using hhi))
    (fun _ _ => by simp [c, nativeCfg])
  rw [hc] at hb
  exact ⟨liftRun 3 hb (fun t ht => (ht (fullLayout 3 rfl t)).elim),
    liftHalt 3 (TapeArithmetic.step_done _ _ rfl)⟩

private def stride (w : ℕ) : ℕ := 2 * w + 3

private def cycleSteps (w x : ℕ) : ℕ := stride w + 1 + (TapeAddition.additionSteps w x + 1) + (stride w + 1)

private def loopLength (w x z : ℕ) : ℕ := cycleSteps w x * z + stride w

private theorem loopRoute {word out : List Bool} {h : Int} {w : ℕ}
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (a x y z : ℕ)
    (hx : x < 2 ^ w) (hz : z < 2 ^ w) :
    stages.Routed word (w + 1)
      1 (cfg 1 (native 1).initialState w a x y z h out)
      1 (cfg 1 (TapeRegisters.done true) w (a + x * z) x y 0 h out)
      (loopLength w x z) := by
  induction z generalizing a with
  | zero =>
    have hbase := (compareSegment (out := out) (a := a) (x := x) (y := y) hin hz).1
    simpa [loopLength, stride] using Stages.Routed.finish hbase
  | succ z ih =>
    obtain ⟨compare, compareStop⟩ :=
      compareSegment (out := out) (a := a) (x := x) (y := y) hin hz
    have hcmp : stages.next 1 (cfg 1 (TapeRegisters.done (decide (z + 1 = 0)))
        w a x y (z + 1) h out).state = some 2 := by
      rw [cfg_route]
      simp [route, TapeRegisters.done, native]
    obtain ⟨add, addStop⟩ := addSegment (out := out) (a := a) (y := y) (z := z + 1) hin hx
    obtain ⟨dec, decStop⟩ := decrementSegment (out := out) (a := a + x) (x := x) (y := y)
      (z := z + 1) (w := w) hin (by omega)
    have hadd : stages.next 2 (cfg 2 addedState w (a + x) x y (z + 1) h out).state = some 3 := by
      rw [cfg_route]
      rfl
    have hdec : stages.next 3 (cfg 3 (4 : Fin 5) w (a + x) x y ((z + 1) - 1) h out).state = some 1 := by
      rw [cfg_route]
      rfl
    have hl : loopLength w x (z + 1) =
        stride w + 1 + (TapeAddition.additionSteps w x + 1 + (stride w + 1 + loopLength w x z)) := by
      simp only [loopLength, Nat.mul_succ, cycleSteps]
      omega
    rw [hl]
    refine Stages.Routed.call (j := 2) compare compareStop hcmp ?_
    rw [cfg_handoff]
    refine Stages.Routed.call (j := 3) add addStop hadd ?_
    rw [cfg_handoff]
    refine Stages.Routed.call (j := 1) dec decStop hdec ?_
    rw [cfg_handoff]
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a + x) (by omega)

def multiplicationSteps (w x y : ℕ) : ℕ := stride w + 1 + loopLength w x y

/-- Prepared entry with the accumulator and two preserved factors. -/
def startConfig (w a x y z : ℕ) (h : Int) (out : List Bool) : machine.Config :=
  stages.tag 0 (cfg 0 (native 0).initialState w a x y z h out)

/-- Exit with accumulated product and both countdown registers cleared. -/
def stopConfig (w sum x y : ℕ) (h : Int) (out : List Bool) : machine.Config :=
  stages.tag 1 (cfg 1 (TapeRegisters.done true) w sum x y 0 h out)

/-- The literal machine computes the fixed-width encoding of the accumulated
product, preserves both factors and both external tape positions, and halts. -/
theorem executeMultiply (word out : List Bool) (h : Int) (w a x y z : ℕ)
    (hin : (-1 : Int) ≤ h ∧ h ≤ word.length) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    machine.BoundedSegment word (w + 1) (startConfig w a x y z h out)
      (stopConfig w (a + x * y) x y h out) (multiplicationSteps w x y) ∧
    machine.step word (stopConfig w (a + x * y) x y h out) = none := by
  obtain ⟨copy, copyStop⟩ := copySegment (out := out) (a := a) (x := x) (y := y) (z := z) (w := w) hin
  obtain ⟨_, stop⟩ := compareSegment (out := out) (a := a + x * y) (x := x) (y := y)
    (z := 0) (w := w) hin (Nat.two_pow_pos w)
  have haltRoute : stages.next 1 (cfg 1 (TapeRegisters.done true) w (a + x * y) x y 0 h out).state =
      none := by
    rw [cfg_route]
    rfl
  refine stages.routed_stop (Stages.Routed.call (j := 1) copy copyStop ?_ ?_) ?_ haltRoute
  · rw [cfg_route]
    rfl
  · rw [cfg_handoff]
    exact loopRoute hin a x y y hx hy
  · simpa using stop

/-- Exact transition count as a polynomial in the width and represented
operands. In the address application both operands are bounded by input size. -/
theorem multiplicationSteps_succ (w x y : ℕ) :
    multiplicationSteps w x y + 1 = (2 * w + 4) * ((3 * x + 4) * y + 2) := by
  let s := 2 * w + 3
  change s + 1 + ((s + 1 + (s + 1 + ((s + 1) * x * 3 + s) + 1) + (s + 1)) * y + s) + 1 = _
  dsimp [s]
  ring
end Mathproof.MinimumGeneration.TapeMultiply
