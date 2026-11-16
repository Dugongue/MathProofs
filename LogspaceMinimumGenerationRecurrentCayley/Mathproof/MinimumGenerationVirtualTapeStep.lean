import Mathproof.MinimumGenerationReingoldLiveInput
import Mathproof.MinimumGenerationTapeRegisters

namespace Mathproof.MinimumGeneration.VirtualTapeStep

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open SearchTransducer
open ReingoldLiveInput (callbackStep)
open TapeArithmetic (block)

private def cellCode : InputCell → Fin 7
  | .leftEnd => 0
  | .data false => 1
  | .data true => 2
  | .rightEnd => 3

private def decodeCell (p : Fin 7) : Option InputCell :=
  match p.val with
  | 0 => some .leftEnd
  | 1 => some (.data false)
  | 2 => some (.data true)
  | 3 => some .rightEnd
  | _ => none

@[simp] private theorem decodeCell_code (c : InputCell) : decodeCell (cellCode c) = some c := by
  cases c with
  | leftEnd => rfl
  | rightEnd => rfl
  | data b => cases b <;> rfl

private def motionCode : Move → Fin 7
  | .stay => 4
  | .left => 5
  | .right => 6

@[simp] private theorem decodeCell_motion (m : Move) : decodeCell (motionCode m) = none := by
  cases m <;> rfl

/-- The extra work bank stores the shifted virtual input position. -/
def pointerBank (M : SearchTransducer) : Fin (M.workTapes + 1) := Fin.last M.workTapes

/-- A single physical playback action, on the native work banks. The virtual
symbol is delivered in finite control. The real input head does not move.
The terminal state retains the native successor and the virtual move. -/
abbrev playback (M : SearchTransducer) : SearchTransducer where
  states := M.states * 7
  workTapes := M.workTapes + 1
  initialState := finProdFinEquiv (M.initialState, cellCode .leftEnd)
  transition state _ stored :=
    let (q, p) := finProdFinEquiv.symm state
    (decodeCell p).bind fun cell =>
      (M.transition q cell (fun t => stored t.castSucc)).map
        fun (q', movement, actions, bit) =>
          (finProdFinEquiv (q', motionCode movement), .stay,
            Fin.lastCases ⟨none, .stay⟩ actions, bit)

private def project (M : SearchTransducer) (c : M.Config) (phase : Fin 7)
    (realHead pointerHead : Int) (pointer : Int → Option Bool) : (playback M).Config :=
  ⟨finProdFinEquiv (c.state, phase), realHead,
    Fin.lastCases pointerHead c.workHead, Fin.lastCases pointer c.workCell, c.outputReversed⟩

/-- Callable playback entry, after a physical virtual-input query returns. -/
def ready (M : SearchTransducer) (c : M.Config) (cell : InputCell)
    (realHead pointerHead : Int) (pointer : Int → Option Bool) : (playback M).Config :=
  project M c (cellCode cell) realHead pointerHead pointer

/-- Physical playback exit, before committing the pending virtual move. -/
def played (M : SearchTransducer) (c : M.Config) (pending : Move)
    (realHead pointerHead : Int) (pointer : Int → Option Bool) : (playback M).Config :=
  project M c (motionCode pending) realHead pointerHead pointer

private theorem after_prj (M : SearchTransducer) (c : M.Config) (phase : Fin 7)
    (realHead pointerHead : Int) (pointer : Int → Option Bool) :
    (project M c phase realHead pointerHead pointer).workHead (pointerBank M) = pointerHead ∧
      (project M c phase realHead pointerHead pointer).workCell (pointerBank M) = pointer := by
  simp [project, pointerBank]

/-- The playback really performs the corresponding finite-table
instruction. The old physical pointer tape is preserved byte for byte. -/
theorem playback_exact (M : SearchTransducer) (raw : List Bool)
    (cell : InputCell) (c d : M.Config) (realHead pointerHead : Int) (pointer : Int → Option Bool)
    (nativeStep : callbackStep M (fun _ => cell) c = some d) :
    ∃ pending : Move,
      (playback M).step raw (ready M c cell realHead pointerHead pointer) =
        some (played M d pending realHead pointerHead pointer) ∧
      d.inputHead = c.inputHead + moveOffset pending := by
  unfold callbackStep at nativeStep
  cases h : M.transition c.state cell (fun i => c.workCell i (c.workHead i)) with
  | none => simp [h] at nativeStep
  | some a =>
    obtain ⟨q, pending, writes, bit⟩ := a
    simp only [h, Option.map_some, Option.some.injEq] at nativeStep
    subst d
    refine ⟨pending, ?_, rfl⟩
    simp only [SearchTransducer.step, playback, ready, played, project, Equiv.symm_apply_apply,
      decodeCell_code, Option.bind_some, Fin.lastCases_castSucc, h, Option.map_some,
      moveOffset, Int.add_zero, Option.some.injEq]
    congr 1
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.lastCases_castSucc]
    · funext i j
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp
      · simp

/-- A terminal playback state can be handed to the register-move router. -/
theorem played_halts (M : SearchTransducer) (raw : List Bool) (c : M.Config) (move : Move)
    (realHead pointerHead : Int) (pointer : Int → Option Bool) :
    (playback M).step raw (played M c move realHead pointerHead pointer) = none := by
  simp [SearchTransducer.step, playback, project, played, Option.bind_none]

/-- The finite controller correctly sees the native no-transition response. -/
theorem playback_halt (M : SearchTransducer) (raw : List Bool)
    (cell : InputCell) (c : M.Config) (realHead pointerHead : Int) (pointer : Int → Option Bool)
    (nativeStop : callbackStep M (fun _ => cell) c = none) :
    (playback M).step raw (ready M c cell realHead pointerHead pointer) = none := by
  unfold callbackStep at nativeStop
  have h := Option.map_eq_none_iff.mp nativeStop
  simp [SearchTransducer.step, playback, ready, project, h]

/-- State entry for the physical register update. This projection is the
one used at a handoff from the playback. -/
def arithmeticEntry (M : SearchTransducer) (op : TapeArithmetic.Operation)
    (c : (playback M).Config) : (TapeArithmetic.machine (pointerBank M) op).Config :=
  ⟨0, c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

/-- The actual pointer adder executes a right move, restores its work head,
and preserves every native bank, physical input position and emitted bit. -/
theorem executeRight (M : SearchTransducer) (raw : List Bool) (c : (playback M).Config)
    (w p : ℕ) (hLeft : c.workCell (pointerBank M) (c.workHead (pointerBank M)) = none)
    (hRight : c.workCell (pointerBank M) (c.workHead (pointerBank M) + w + 1) = none)
    (hBits : block (c.workCell (pointerBank M)) (c.workHead (pointerBank M) + 1) (encodeLabel w p)) :
    let bank := pointerBank M
    let start := arithmeticEntry M .increment c
    ∃ result, TapeArithmetic.Runs raw (c.workHead bank) (c.workHead bank + w + 1)
      (2 * w + 3) start result ∧ result.state = 4 ∧ result.workHead bank = c.workHead bank ∧
      block (result.workCell bank) (c.workHead bank + 1) (encodeLabel w (p + 1)) ∧
      TapeArithmetic.Framed start result (c.workHead bank + 1) (c.workHead bank + w + 1) :=
  TapeArithmetic.executeIncrement raw (arithmeticEntry M .increment c) w p rfl hLeft hRight hBits

/-- The actual pointer subtractor executes a left move from a nonboundary
position, restoring its work head and preserving all native banks. -/
theorem executeLeft (M : SearchTransducer) (raw : List Bool) (c : (playback M).Config)
    (w p : ℕ) (inside : 0 < p)
    (hLeft : c.workCell (pointerBank M) (c.workHead (pointerBank M)) = none)
    (hRight : c.workCell (pointerBank M) (c.workHead (pointerBank M) + w + 1) = none)
    (hBits : block (c.workCell (pointerBank M)) (c.workHead (pointerBank M) + 1) (encodeLabel w p)) :
    let bank := pointerBank M
    let start := arithmeticEntry M .decrement c
    ∃ result, TapeArithmetic.Runs raw (c.workHead bank) (c.workHead bank + w + 1)
      (2 * w + 3) start result ∧ result.state = 4 ∧ result.workHead bank = c.workHead bank ∧
      block (result.workCell bank) (c.workHead bank + 1) (encodeLabel w (p - 1)) ∧
      TapeArithmetic.Framed start result (c.workHead bank + 1) (c.workHead bank + w + 1) :=
  TapeArithmetic.executeDecrement raw (arithmeticEntry M .decrement c) w p inside
    rfl hLeft hRight hBits

section Routed

variable {M : SearchTransducer}

private abbrev Phase := Fin 3 × Fin 5

private def inputPhase (cell : InputCell) : Phase :=
  (0, ⟨(cellCode cell).val, by cases cell with | data b => cases b <;> decide | _ => decide⟩)

private def terminalPhase : Phase := (0, 4)

private def arithmeticPhase (op : TapeArithmetic.Operation) (q : Fin 5) : Phase :=
  (match op with | .increment => 1 | .decrement => 2, q)

private def movePhase : Move → Phase
  | .stay => terminalPhase
  | .left => arithmeticPhase .decrement 0
  | .right => arithmeticPhase .increment 0

private def encodePhase (q : Fin M.states) (p : Phase) : Fin (M.states * (3 * 5)) :=
  finProdFinEquiv (q, finProdFinEquiv p)

private def decodePhase (state : Fin (M.states * (3 * 5))) : Fin M.states × Phase :=
  let (q, p) := finProdFinEquiv.symm state
  (q, finProdFinEquiv.symm p)

@[simp] private theorem decodePhase_encode (q : Fin M.states) (p : Phase) :
    decodePhase (encodePhase q p) = (q, p) := by
  simp [encodePhase, decodePhase]

private def sourceCell (p : Fin 5) : Option InputCell :=
  decodeCell (Fin.castLE (by decide : 5 ≤ 7) p)

@[simp] private theorem sourceCell_inputPhase (cell : InputCell) :
    sourceCell (inputPhase cell).2 = some cell := by
  cases cell with
  | data b => cases b <;> rfl
  | _ => rfl

private def arithmeticTransition (M : SearchTransducer) (q : Fin M.states)
    (op : TapeArithmetic.Operation) (phase : Fin 5) (sym : InputCell)
    (scanned : Fin (M.workTapes + 1) → Option Bool) :=
  ((TapeArithmetic.machine (pointerBank M) op).transition phase sym scanned).map
    fun (next, movement, actions, bit) => (encodePhase q (arithmeticPhase op next), movement, actions, bit)

/-- Play back the native action, automatically route its virtual motion
through the appropriate physical arithmetic routine, and retain its successor. -/
abbrev routed (M : SearchTransducer) : SearchTransducer where
  states := M.states * (3 * 5)
  workTapes := M.workTapes + 1
  initialState := encodePhase M.initialState (inputPhase .leftEnd)
  transition state sym scanned :=
    let (q, mode, phase) := decodePhase state
    if mode = 0 then
      (sourceCell phase).bind fun cell =>
        (M.transition q cell (fun t => scanned t.castSucc)).map
          fun (q', movement, actions, bit) =>
            (encodePhase q' (movePhase movement), .stay, Fin.lastCases ⟨none, .stay⟩ actions, bit)
    else if mode = 1 then arithmeticTransition M q .increment phase sym scanned
    else arithmeticTransition M q .decrement phase sym scanned

private def routedProject (M : SearchTransducer) (c : M.Config) (phase : Phase)
    (realHead pointerHead : Int) (pointer : Int → Option Bool) : (routed M).Config :=
  ⟨encodePhase c.state phase, realHead,
    Fin.lastCases pointerHead c.workHead, Fin.lastCases pointer c.workCell, c.outputReversed⟩

/-- Entry to the physical routed action after the virtual symbol is returned. -/
def routedReady (M : SearchTransducer) (c : M.Config) (cell : InputCell)
    (realHead pointerHead : Int) (pointer : Int → Option Bool) : (routed M).Config :=
  routedProject M c (inputPhase cell) realHead pointerHead pointer

/-- Exit after the native action, before executing the selected pointer edit. -/
@[simp] theorem routedReady_pointerHead (M : SearchTransducer) (c : M.Config)
    (cell : InputCell) (real base : Int) (pointer : Int → Option Bool) :
    (routedReady M c cell real base pointer).workHead (pointerBank M) = base := by
  simp [routedReady, routedProject, project, pointerBank]

@[simp] theorem routedReady_nativeHead (M : SearchTransducer) (c : M.Config)
    (cell : InputCell) (real base : Int) (pointer : Int → Option Bool) (i : Fin M.workTapes) :
    (routedReady M c cell real base pointer).workHead i.castSucc = c.workHead i := by
  simp [routedReady, routedProject, project]

@[simp] theorem routedReady_pointerCell (M : SearchTransducer) (c : M.Config)
    (cell : InputCell) (real base : Int) (pointer : Int → Option Bool) :
    (routedReady M c cell real base pointer).workCell (pointerBank M) = pointer := by
  simp [routedReady, routedProject, project, pointerBank]

@[simp] theorem routedReady_nativeCell (M : SearchTransducer) (c : M.Config)
    (cell : InputCell) (real base : Int) (pointer : Int → Option Bool) (i : Fin M.workTapes) :
    (routedReady M c cell real base pointer).workCell i.castSucc = c.workCell i := by
  simp [routedReady, routedProject, project]

def routedPlayed (M : SearchTransducer) (c : M.Config) (motion : Move)
    (realHead pointerHead : Int) (pointer : Int → Option Bool) : (routed M).Config :=
  routedProject M c (movePhase motion) realHead pointerHead pointer

theorem routedPlayback (M : SearchTransducer) (raw : List Bool)
    (cell : InputCell) (c d : M.Config) (realHead pointerHead : Int) (pointer : Int → Option Bool)
    (nativeStep : callbackStep M (fun _ => cell) c = some d) :
    ∃ pending : Move,
      (routed M).step raw (routedReady M c cell realHead pointerHead pointer) =
        some (routedPlayed M d pending realHead pointerHead pointer) ∧
      d.inputHead = c.inputHead + moveOffset pending := by
  unfold callbackStep at nativeStep
  cases h : M.transition c.state cell (fun i => c.workCell i (c.workHead i)) with
  | none => simp [h] at nativeStep
  | some a =>
    obtain ⟨q, pending, writes, bit⟩ := a
    simp only [h, Option.map_some, Option.some.injEq] at nativeStep
    subst d
    refine ⟨pending, ?_, rfl⟩
    have hmode : (inputPhase cell).1 = 0 := rfl
    simp only [SearchTransducer.step, routed, routedReady, routedPlayed, routedProject,
      decodePhase_encode, hmode, if_pos, sourceCell_inputPhase, Option.bind_some,
      Fin.lastCases_castSucc, h, Option.map_some, moveOffset, Int.add_zero, Option.some.injEq]
    congr 1
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.lastCases_castSucc]
    · funext i j
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp
      · simp

theorem routedStops (M : SearchTransducer) (raw : List Bool)
    (cell : InputCell) (c : M.Config) (realHead pointerHead : Int) (pointer : Int → Option Bool)
    (nativeStop : callbackStep M (fun _ => cell) c = none) :
    (routed M).step raw (routedReady M c cell realHead pointerHead pointer) = none := by
  unfold callbackStep at nativeStop
  have h := Option.map_eq_none_iff.mp nativeStop
  have hmode : (inputPhase cell).1 = 0 := rfl
  simp only [SearchTransducer.step, routed, routedReady, routedProject, decodePhase_encode,
    hmode, if_pos, sourceCell_inputPhase, Option.bind_some, Fin.lastCases_castSucc, h,
    Option.map_none]

/-- Retain the native successor in finite control during every pointer edit. -/
def liftArithmetic (M : SearchTransducer) (q : Fin M.states) (op : TapeArithmetic.Operation)
    (c : (TapeArithmetic.machine (pointerBank M) op).Config) : (routed M).Config :=
  ⟨encodePhase q (arithmeticPhase op c.state), c.inputHead, c.workHead, c.workCell, c.outputReversed⟩

theorem routed_arithmeticStep (M : SearchTransducer) (raw : List Bool) (q : Fin M.states)
    (op : TapeArithmetic.Operation) (c : (TapeArithmetic.machine (pointerBank M) op).Config) :
    (routed M).step raw (liftArithmetic M q op c) =
      ((TapeArithmetic.machine (pointerBank M) op).step raw c).map (liftArithmetic M q op) := by
  cases op with
  | increment =>
    unfold SearchTransducer.step
    simp only [routed, liftArithmetic, decodePhase_encode, arithmeticPhase, show (1 : Fin 3) ≠ 0 by decide,
      if_false, if_pos, arithmeticTransition, Option.map_map, Function.comp_def]
    with_unfolding_all erw [Option.map_map]
    rfl
  | decrement =>
    unfold SearchTransducer.step
    simp only [routed, liftArithmetic, decodePhase_encode, arithmeticPhase, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, if_false, arithmeticTransition, Option.map_map, Function.comp_def]
    with_unfolding_all erw [Option.map_map]
    rfl

theorem routed_arithmeticRun (M : SearchTransducer) (raw : List Bool) (q : Fin M.states)
    (op : TapeArithmetic.Operation) (c : (TapeArithmetic.machine (pointerBank M) op).Config)
    (len : ℕ) :
    (routed M).runFrom raw (liftArithmetic M q op c) len =
      ((TapeArithmetic.machine (pointerBank M) op).runFrom raw c len).map (liftArithmetic M q op) := by
  induction len with
  | zero => rfl
  | succ k ih =>
    simp only [SearchTransducer.runFrom, ih]
    cases h : (TapeArithmetic.machine (pointerBank M) op).runFrom raw c k with
    | none => rfl
    | some d => exact routed_arithmeticStep M raw q op d

theorem routed_arithmeticSegment (M : SearchTransducer) {raw : List Bool} (q : Fin M.states)
    (op : TapeArithmetic.Operation) {c d : (TapeArithmetic.machine (pointerBank M) op).Config}
    {B length : ℕ} (h : (TapeArithmetic.machine (pointerBank M) op).BoundedSegment raw B c d length) :
    (routed M).BoundedSegment raw B (liftArithmetic M q op c) (liftArithmetic M q op d) length := by
  refine ⟨by rw [routed_arithmeticRun, h.1]; rfl, ?_⟩
  intro k hk x hx
  rw [routed_arithmeticRun] at hx
  cases hd : (TapeArithmetic.machine (pointerBank M) op).runFrom raw c k with
  | none => simp [hd] at hx
  | some y =>
    simp only [hd, Option.map_some, Option.some.injEq] at hx
    subst x
    exact h.2 k hk y hd

/-- The selected arithmetic arm yields a physical halt at the callback boundary. -/
theorem routed_arithmeticHalt (M : SearchTransducer) (raw : List Bool) (q : Fin M.states)
    (op : TapeArithmetic.Operation) (c : (TapeArithmetic.machine (pointerBank M) op).Config)
    (done : c.state = 4) : (routed M).step raw (liftArithmetic M q op c) = none := by
  rw [routed_arithmeticStep]
  simp [SearchTransducer.step, TapeArithmetic.machine, done]

private theorem routed_stayHalt (M : SearchTransducer) (raw : List Bool) (c : M.Config)
    (realHead base : Int) (pointer : Int → Option Bool) :
    (routed M).step raw (routedPlayed M c .stay realHead base pointer) = none := by
  simp [SearchTransducer.step, routed, routedPlayed, routedProject, movePhase, terminalPhase,
    sourceCell, decodeCell]

/-- The entry/exit agreement needed by the next virtual-input callback. -/
structure AtAddress (M : SearchTransducer) (native : M.Config) (realHead base : Int) (w : ℕ)
    (physical : (routed M).Config) : Prop where
  state : (decodePhase physical.state).1 = native.state
  realPosition : physical.inputHead = realHead
  nativeHead : ∀ i, physical.workHead i.castSucc = native.workHead i
  nativeTape : ∀ i, physical.workCell i.castSucc = native.workCell i
  output : physical.outputReversed = native.outputReversed
  restored : physical.workHead (pointerBank M) = base
  leftMarker : physical.workCell (pointerBank M) base = none
  rightMarker : physical.workCell (pointerBank M) (base + w + 1) = none
  address : block (physical.workCell (pointerBank M)) (base + 1)
    (encodeLabel w (native.inputHead + 1).toNat)

/-- The pointer changes only in the marked address block. -/
def PointerExterior (M : SearchTransducer) (base : Int) (w : ℕ)
    (original : Int → Option Bool) (physical : (routed M).Config) : Prop :=
  ∀ j, j < base + 1 ∨ base + w + 1 ≤ j →
    physical.workCell (pointerBank M) j = original j

/-- At base zero, a blank exterior transported by the physical instruction
determines the whole pointer bank from the marked binary block. -/
theorem AtAddress.pointer_eq_work {M : SearchTransducer} {native : M.Config}
    {real : Int} {w : ℕ} {old : Int → Option Bool} {out : (routed M).Config}
    (address : AtAddress M native real 0 w out)
    (frame : PointerExterior M 0 w old out)
    (blank : ∀ j, j ≤ 0 ∨ (w : Int) < j → old j = none) :
    out.workCell (pointerBank M) =
      InputPosition.work (encodeLabel w (native.inputHead + 1).toNat) := by
  funext j
  let bits := encodeLabel w (native.inputHead + 1).toNat
  have len : bits.length = w := length_encodeLabel _ _
  by_cases h₀ : j ≤ 0
  · rw [frame j (.inl (by omega)), blank j (.inl h₀)]
    simp [InputPosition.work, h₀]
  · by_cases hw : (w : Int) < j
    · rw [frame j (.inr (by omega)), blank j (.inr hw)]
      simp only [InputPosition.work, if_neg h₀]
      exact (List.getElem?_eq_none (by change bits.length ≤ (j-1).toNat; omega)).symm
    · let i : Fin bits.length := ⟨(j - 1).toNat, by omega⟩
      have e : (0 : Int) + 1 + i.val = j := by dsimp [i]; omega
      have exactBit := address.address i
      rw [e] at exactBit
      change out.workCell (pointerBank M) j = InputPosition.work bits j
      rw [exactBit, InputPosition.work, if_neg h₀]
      exact (List.getElem?_eq_getElem i.isLt).symm

private theorem projectedBounded (M : SearchTransducer) (raw : List Bool) (B : ℕ)
    (c : M.Config) (phase : Phase) (realHead base : Int) (pointer : Int → Option Bool)
    (hin : (-1 : Int) ≤ realHead ∧ realHead ≤ (raw.length : Int))
    (hnative : ∀ i, (c.workHead i).natAbs ≤ B) (hp : base.natAbs ≤ B) :
    (routed M).Bounded raw B (routedProject M c phase realHead base pointer) := by
  refine ⟨hin.1, hin.2, fun i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [routedProject] using hp
  · simpa [routedProject] using hnative j

private theorem singleSegment (M : SearchTransducer) {raw : List Bool} {B : ℕ}
    {c d : M.Config} (h : M.step raw c = some d)
    (hc : M.Bounded raw B c) (hd : M.Bounded raw B d) :
    M.BoundedSegment raw B c d 1 := by
  refine ⟨h, ?_⟩
  intro k hk x hx
  interval_cases k
  · cases hx
    exact hc
  · change M.step raw c = some x at hx
    rw [h] at hx
    cases hx
    exact hd

private def operationMove : TapeArithmetic.Operation → Move
  | .increment => .right
  | .decrement => .left

private def moveAddress : TapeArithmetic.Operation → ℕ → ℕ
  | .increment, p => p + 1
  | .decrement, p => p - 1

private theorem routedCommit (M : SearchTransducer) (raw : List Bool) (B w p : ℕ)
    (d : M.Config) (op : TapeArithmetic.Operation) (realHead base : Int)
    (pointer : Int → Option Bool)
    (hin : (-1 : Int) ≤ realHead ∧ realHead ≤ (raw.length : Int))
    (hnative : ∀ i, (d.workHead i).natAbs ≤ B)
    (window : ∀ j, base ≤ j → j ≤ base + w + 1 → j.natAbs ≤ B)
    (hLeft : pointer base = none) (hRight : pointer (base + w + 1) = none)
    (hBits : block pointer (base + 1) (encodeLabel w p))
    (inside : op = .decrement → 0 < p)
    (index : (d.inputHead + 1).toNat = moveAddress op p) :
    ∃ y, (routed M).BoundedSegment raw B
      (routedPlayed M d (operationMove op) realHead base pointer) y (2 * w + 3) ∧
      (routed M).step raw y = none ∧ AtAddress M d realHead base w y ∧
        PointerExterior M base w pointer y := by
  let c := played M d (operationMove op) realHead base pointer
  have hb : c.workHead (pointerBank M) = base := by simp [c, played, project, pointerBank]
  have hc : c.workCell (pointerBank M) = pointer := by simp [c, played, project, pointerBank]
  have hl : c.workCell (pointerBank M) (c.workHead (pointerBank M)) = none := by
    simpa only [hb, hc] using hLeft
  have hr : c.workCell (pointerBank M) (c.workHead (pointerBank M) + w + 1) = none := by
    simpa only [hb, hc] using hRight
  have hword : block (c.workCell (pointerBank M)) (c.workHead (pointerBank M) + 1)
      (encodeLabel w p) := by simpa only [hb, hc] using hBits
  let start := arithmeticEntry M op c
  have runExists : ∃ result, TapeArithmetic.Runs raw base (base + w + 1) (2 * w + 3)
        start result ∧ result.state = 4 ∧ result.workHead (pointerBank M) = base ∧
      block (result.workCell (pointerBank M)) (base + 1) (encodeLabel w (moveAddress op p)) ∧
      TapeArithmetic.Framed start result (base + 1) (base + w + 1) := by
    cases op
    · simpa only [hb, moveAddress] using executeRight M raw c w p hl hr hword
    · simpa only [hb, moveAddress] using executeLeft M raw c w p (inside rfl) hl hr hword
  obtain ⟨result, run, done, restored, word, frame⟩ := runExists
  have neBank (i : Fin M.workTapes) : i.castSucc ≠ pointerBank M := Fin.castSucc_ne_last i
  have hframe : ∀ t, t ≠ pointerBank M → (start.workHead t).natAbs ≤ B := by
    intro t ht
    refine Fin.lastCases ?_ (fun i => ?_) t ht
    · intro contra
      exact (contra rfl).elim
    · intro _
      simpa [start, c, arithmeticEntry, played, project] using hnative i
  have segment := TapeRegisters.arithmeticBoundedSegment run hin window hframe
  have routedSegment := routed_arithmeticSegment M d.state op segment
  have entry : liftArithmetic M d.state op start =
      routedPlayed M d (operationMove op) realHead base pointer := by cases op <;> rfl
  refine ⟨liftArithmetic M d.state op result, entry ▸ routedSegment,
    routed_arithmeticHalt M raw d.state op result done, ?_, ?_⟩
  refine ⟨by simp [liftArithmetic], frame.input, ?_, ?_, frame.output, restored, ?_, ?_, ?_⟩
  · intro i
    simpa [start, c, arithmeticEntry, played, project, liftArithmetic] using frame.heads _ (neBank i)
  · intro i
    funext j
    simpa [start, c, arithmeticEntry, played, project, liftArithmetic] using
      frame.cells (i.castSucc) j (.inl (neBank i))
  · change result.workCell (pointerBank M) base = none
    rw [frame.cells _ _ (.inr (.inl (by omega)))]
    simpa [start, arithmeticEntry, hc] using hLeft
  · change result.workCell (pointerBank M) (base + w + 1) = none
    rw [frame.cells _ _ (.inr (.inr le_rfl))]
    simpa [start, arithmeticEntry, hc] using hRight
  · simpa only [liftArithmetic, index] using word
  · intro j hj
    change result.workCell (pointerBank M) j = pointer j
    rw [frame.cells _ _ (.inr hj)]
    simp [start, arithmeticEntry, hc]

/-- One physical machine completes a native action and restores its live virtual
address bank for the next read. The input symbol comes from the caller. -/
theorem routedExecuteFramed (M : SearchTransducer) (raw : List Bool) (B w p : ℕ)
    (cell : InputCell) (c d : M.Config) (realHead base : Int) (pointer : Int → Option Bool)
    (nativeStep : callbackStep M (fun _ => cell) c = some d)
    (position : c.inputHead + 1 = (p : Int)) (valid : (-1 : Int) ≤ d.inputHead)
    (hin : (-1 : Int) ≤ realHead ∧ realHead ≤ (raw.length : Int))
    (before : ∀ i, (c.workHead i).natAbs ≤ B) (after : ∀ i, (d.workHead i).natAbs ≤ B)
    (window : ∀ j, base ≤ j → j ≤ base + w + 1 → j.natAbs ≤ B)
    (hLeft : pointer base = none) (hRight : pointer (base + w + 1) = none)
    (hBits : block pointer (base + 1) (encodeLabel w p)) :
    ∃ length y, length ≤ 2 * w + 4 ∧
      (routed M).BoundedSegment raw B (routedReady M c cell realHead base pointer) y length ∧
      (routed M).step raw y = none ∧ AtAddress M d realHead base w y ∧
        PointerExterior M base w pointer y := by
  obtain ⟨move, step, offset⟩ := routedPlayback M raw cell c d realHead base pointer nativeStep
  have hp : base.natAbs ≤ B := window base le_rfl (by omega)
  have first := singleSegment (routed M) step
    (projectedBounded M raw B c (inputPhase cell) realHead base pointer hin before hp)
    (projectedBounded M raw B d (movePhase move) realHead base pointer hin after hp)
  cases move with
  | stay =>
    have index : (d.inputHead + 1).toNat = p := by simp [moveOffset] at offset; omega
    refine ⟨1, _, by omega, first, routed_stayHalt M raw d realHead base pointer, ?_⟩
    simp only [routedPlayed, routedProject, movePhase]
    exact ⟨⟨by simp, rfl, by simp, by simp, rfl, by simp [pointerBank],
      by simp [pointerBank, hLeft], by simp [pointerBank, hRight], by simp [pointerBank, index, hBits]⟩,
      fun j _ => by simp [pointerBank]⟩
  | left =>
    simp only [moveOffset] at offset
    have index : (d.inputHead + 1).toNat = moveAddress .decrement p := by
      simp only [moveAddress]; omega
    obtain ⟨y, seg, stop, aligned⟩ := routedCommit M raw B w p d .decrement realHead base pointer
      hin after window hLeft hRight hBits (fun _ => by omega) index
    exact ⟨1 + (2 * w + 3), y, by omega, BoundedSegment.append (routed M) first seg, stop, aligned⟩
  | right =>
    simp only [moveOffset] at offset
    have index : (d.inputHead + 1).toNat = moveAddress .increment p := by
      simp only [moveAddress]; omega
    obtain ⟨y, seg, stop, aligned⟩ := routedCommit M raw B w p d .increment realHead base pointer
      hin after window hLeft hRight hBits (fun h => by cases h) index
    exact ⟨1 + (2 * w + 3), y, by omega, BoundedSegment.append (routed M) first seg, stop, aligned⟩


/-- The routed instruction preserves the prior interface when only the address
value and delimiters are needed. -/
theorem routedExecute (M : SearchTransducer) (raw : List Bool) (B w p : ℕ)
    (cell : InputCell) (c d : M.Config) (realHead base : Int) (pointer : Int → Option Bool)
    (nativeStep : callbackStep M (fun _ => cell) c = some d)
    (position : c.inputHead + 1 = (p : Int)) (valid : (-1 : Int) ≤ d.inputHead)
    (hin : (-1 : Int) ≤ realHead ∧ realHead ≤ (raw.length : Int))
    (before : ∀ i, (c.workHead i).natAbs ≤ B) (after : ∀ i, (d.workHead i).natAbs ≤ B)
    (window : ∀ j, base ≤ j → j ≤ base + w + 1 → j.natAbs ≤ B)
    (hLeft : pointer base = none) (hRight : pointer (base + w + 1) = none)
    (hBits : block pointer (base + 1) (encodeLabel w p)) :
    ∃ length y, length ≤ 2 * w + 4 ∧
      (routed M).BoundedSegment raw B (routedReady M c cell realHead base pointer) y length ∧
      (routed M).step raw y = none ∧ AtAddress M d realHead base w y := by
  obtain ⟨len,y,time,run,halt,address,_⟩ :=
    routedExecuteFramed M raw B w p cell c d realHead base pointer nativeStep position valid hin
      before after window hLeft hRight hBits
  exact ⟨len,y,time,run,halt,address⟩

end Routed


end Mathproof.MinimumGeneration.VirtualTapeStep
