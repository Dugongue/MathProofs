import Mathproof.MinimumGenerationProblem

namespace Mathproof.MinimumGeneration.TapeArithmetic

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)

inductive Operation
  | increment
  | decrement
  deriving DecidableEq

/-- The one-bit carry (or borrow) held in finite control. -/
def propagate (op : Operation) (carry bit : Bool) : Bool :=
  carry && (match op with | .increment => bit | .decrement => !bit)

def changed (carry bit : Bool) : Bool := if carry then !bit else bit

/-- Fixed-width ripple arithmetic on little-endian labels. -/
def ripple (op : Operation) (carry : Bool) : List Bool → List Bool
  | [] => []
  | b :: bits => changed carry b :: ripple op (propagate op carry b) bits

def finalCarry (op : Operation) (carry : Bool) : List Bool → Bool
  | [] => carry
  | b :: bits => finalCarry op (propagate op carry b) bits

@[simp] theorem ripple_length (op : Operation) (carry : Bool) (bits : List Bool) :
    (ripple op carry bits).length = bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons b bits ih => simp [ripple, ih]

private def scanState (carry : Bool) : Fin 5 := if carry then 1 else 2

private def actions (bank : Fin tapes) (move : Move) (write : Option (Option Bool))
    (t : Fin tapes) : Action (Option Bool) :=
  if t = bank then ⟨write, move⟩ else ⟨none, .stay⟩

/-- Edit a single prepared register. The carry/borrow fits in the finite
control. Both boundary markers are blank. The input and output heads are idle. -/
abbrev machine {tapes : ℕ} (bank : Fin tapes) (op : Operation) : SearchTransducer where
  states := 5
  workTapes := tapes
  initialState := 0
  transition q _ read :=
    let next := fun (state : Fin 5) (move : Move) (write : Option (Option Bool)) =>
      some (state, .stay, actions bank move write, none)
    if q = 0 then next (scanState true) .right none
    else if q = 1 ∨ q = 2 then
      match read bank with
      | none => next 3 .left none
      | some b =>
        let carry := decide (q = 1)
        next (scanState (propagate op carry b)) .right (some (some (changed carry b)))
    else if q = 3 then
      match read bank with
      | none => next 4 .stay none
      | some _ => next 3 .left none
    else none

variable {tapes : ℕ} {bank : Fin tapes} {op : Operation}

abbrev Config (bank : Fin tapes) (op : Operation) := (machine bank op).Config

/-- The part of a local transition shared by the five control phases. -/
private def advance (c : Config bank op) (q : Fin 5) (move : Move)
    (write : Option (Option Bool)) : Config bank op :=
  { state := q
    inputHead := c.inputHead
    outputReversed := c.outputReversed
    workHead := fun t => if t = bank then c.workHead t + moveOffset move else c.workHead t
    workCell := fun t j =>
      if t = bank ∧ j = c.workHead bank then write.getD (c.workCell t j) else c.workCell t j }

private theorem step_of_transition (word : List Bool) (c : Config bank op) (q : Fin 5)
    (move : Move) (write : Option (Option Bool))
    (h : (machine bank op).transition c.state (SearchTransducer.readInput word c.inputHead)
        (fun t => c.workCell t (c.workHead t)) =
      some (q, .stay, actions bank move write, none)) :
    (machine bank op).step word c = some (advance c q move write) := by
  unfold SearchTransducer.step
  rw [h]
  simp [advance, actions, moveOffset]
  constructor
  · funext t
    by_cases ht : t = bank <;> simp [ht, moveOffset]
  · funext t j
    by_cases ht : t = bank <;> simp [ht]

private theorem step_enter (word : List Bool) (c : Config bank op) (hq : c.state = 0) :
    (machine bank op).step word c = some (advance c (scanState true) .right none) := by
  apply step_of_transition
  simp [machine, hq]

private theorem step_scan_bit (word : List Bool) (c : Config bank op) (carry b : Bool)
    (hq : c.state = scanState carry) (hb : c.workCell bank (c.workHead bank) = some b) :
    (machine bank op).step word c =
      some (advance c (scanState (propagate op carry b)) .right
        (some (some (changed carry b)))) := by
  apply step_of_transition
  cases carry <;> simp [machine, hq, hb, scanState, propagate, changed]

private theorem step_scan_marker (word : List Bool) (c : Config bank op) (carry : Bool)
    (hq : c.state = scanState carry) (hb : c.workCell bank (c.workHead bank) = none) :
    (machine bank op).step word c = some (advance c 3 .left none) := by
  apply step_of_transition
  cases carry <;> simp [machine, hq, hb, scanState]

private theorem step_rewind_bit (word : List Bool) (c : Config bank op) (b : Bool)
    (hq : c.state = 3) (hb : c.workCell bank (c.workHead bank) = some b) :
    (machine bank op).step word c = some (advance c 3 .left none) := by
  apply step_of_transition
  simp [machine, hq, hb]

private theorem step_rewind_marker (word : List Bool) (c : Config bank op)
    (hq : c.state = 3) (hb : c.workCell bank (c.workHead bank) = none) :
    (machine bank op).step word c = some (advance c 4 .stay none) := by
  apply step_of_transition
  simp [machine, hq, hb]

theorem step_done (word : List Bool) (c : Config bank op) (hq : c.state = 4) :
    (machine bank op).step word c = none := by
  simp [SearchTransducer.step, machine, hq]

/-- A contiguous little-endian work-tape register and its starting coordinate. -/
def block (cell : Int → Option Bool) (start : Int) (bits : List Bool) : Prop :=
  ∀ i : Fin bits.length, cell (start + i.val) = some bits[i]

private theorem block_cons {cell : Int → Option Bool} {start : Int} {b : Bool}
    {bits : List Bool} :
    block cell start (b :: bits) ↔ cell start = some b ∧ block cell (start + 1) bits := by
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0, by simp⟩, ?_⟩
    intro i
    simpa [Int.add_assoc, Int.add_comm (1 : Int)] using
      h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  · rintro ⟨hFirst, hTail⟩ i
    cases i with
    | mk val lt =>
      cases val with
      | zero => simpa using hFirst
      | succ val =>
        simpa [Int.add_assoc, Int.add_comm (1 : Int)] using
          hTail ⟨val, Nat.lt_of_succ_lt_succ lt⟩

/-- Frame property of a register edit. All metadata and other tapes are kept,
and the selected tape is written only in the stated half-open interval. -/
structure Framed (c c' : Config bank op) (lo hi : Int) : Prop where
  input : c'.inputHead = c.inputHead
  output : c'.outputReversed = c.outputReversed
  heads : ∀ t, t ≠ bank → c'.workHead t = c.workHead t
  cells : ∀ t j, t ≠ bank ∨ j < lo ∨ hi ≤ j → c'.workCell t j = c.workCell t j

private theorem frame_trans {c₀ c₁ c₂ : Config bank op} {l₀ h₀ l₁ h₁ lo hi : Int}
    (h₀₁ : Framed c₀ c₁ l₀ h₀) (h₁₂ : Framed c₁ c₂ l₁ h₁)
    (hl₀ : lo ≤ l₀) (hh₀ : h₀ ≤ hi) (hl₁ : lo ≤ l₁) (hh₁ : h₁ ≤ hi) :
    Framed c₀ c₂ lo hi := by
  refine ⟨h₁₂.input.trans h₀₁.input, h₁₂.output.trans h₀₁.output,
    fun t ht => (h₁₂.heads t ht).trans (h₀₁.heads t ht), ?_⟩
  intro t j h
  rcases h with ht | hl | hh
  · exact (h₁₂.cells t j (.inl ht)).trans (h₀₁.cells t j (.inl ht))
  · exact (h₁₂.cells t j (.inr (.inl (lt_of_lt_of_le hl hl₁)))).trans
      (h₀₁.cells t j (.inr (.inl (lt_of_lt_of_le hl hl₀))))
  · exact (h₁₂.cells t j (.inr (.inr (le_trans hh₁ hh)))).trans
      (h₀₁.cells t j (.inr (.inr (le_trans hh₀ hh))))

private theorem frame_idle (c : Config bank op) (q : Fin 5) (move : Move) (lo hi : Int) :
    Framed c (advance c q move none) lo hi := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro t ht
    simp [advance, ht]
  · intro t j _
    simp [advance]

private theorem frame_write (c : Config bank op) (q : Fin 5) (move : Move) (b : Bool) :
    Framed c (advance c q move (some (some b))) (c.workHead bank) (c.workHead bank + 1) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro t ht
    simp [advance, ht]
  · intro t j h
    rcases h with ht | hl | hh
    · simp [advance, ht]
    · simp [advance, ne_of_lt hl]
    · have hn : j ≠ c.workHead bank := by omega
      simp [advance, hn]

/-- A run of consecutive physical transitions with every selected work-head
position inside a fixed interval, including the two endpoints. -/
inductive Runs (word : List Bool) (lo hi : Int) : ℕ → Config bank op → Config bank op → Prop
  | nil (c) (hlo : lo ≤ c.workHead bank) (hhi : c.workHead bank ≤ hi) :
      Runs word lo hi 0 c c
  | cons {n c d e} (hlo : lo ≤ c.workHead bank) (hhi : c.workHead bank ≤ hi)
      (h : (machine bank op).step word c = some d) (rest : Runs word lo hi n d e) :
      Runs word lo hi (n + 1) c e

theorem Runs.append {word : List Bool} {lo hi : Int}
    {m n : ℕ} {a b c : Config bank op}
    (aToB : Runs word lo hi m a b) (bToC : Runs word lo hi n b c) :
    Runs word lo hi (n + m) a c := by
  induction aToB with
  | nil => simpa using bToC
  | cons hlo hhi h _ ih => exact .cons hlo hhi h (ih bToC)

private theorem Runs.widen {word : List Bool} {lo hi lo' hi' : Int}
    {n : ℕ} {a b : Config bank op} (run : Runs word lo hi n a b)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    Runs word lo' hi' n a b := by
  induction run with
  | nil _ hl hh => exact .nil _ (hlo.trans hl) (hh.trans hhi)
  | cons hl hh step _ ih => exact .cons (hlo.trans hl) (hh.trans hhi) step ih

private theorem scan (word : List Bool) (c : Config bank op) (carry : Bool) (bits : List Bool)
    (hq : c.state = scanState carry) (hb : block (c.workCell bank) (c.workHead bank) bits) :
    ∃ d, Runs word (c.workHead bank) (c.workHead bank + bits.length) bits.length c d ∧
      d.state = scanState (finalCarry op carry bits) ∧
      d.workHead bank = c.workHead bank + bits.length ∧
      block (d.workCell bank) (c.workHead bank) (ripple op carry bits) ∧
      Framed c d (c.workHead bank) (c.workHead bank + bits.length) := by
  induction bits generalizing c carry with
  | nil =>
    exact ⟨c, by simpa using Runs.nil c le_rfl le_rfl, hq, by simp,
      fun i => Fin.elim0 i, ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩⟩
  | cons b bits ih =>
    obtain ⟨hFirst, hTail⟩ := block_cons.mp hb
    let nextCarry := propagate op carry b
    let d := advance c (scanState nextCarry) .right (some (some (changed carry b)))
    have hStep := step_scan_bit word c carry b hq hFirst
    have hdHead : d.workHead bank = c.workHead bank + 1 := by simp [d, advance, moveOffset]
    have hdCell : ∀ j, j ≠ c.workHead bank → d.workCell bank j = c.workCell bank j := by
      intro j hj
      simp [d, advance, hj]
    have hdBits : block (d.workCell bank) (d.workHead bank) bits := by
      rw [hdHead]
      intro i
      rw [hdCell _ (by omega)]
      exact hTail i
    obtain ⟨e, run, hState, hHead, hBits, hFrame⟩ := ih d nextCarry rfl hdBits
    have hEnd : d.workHead bank + (bits.length : Int) =
        c.workHead bank + ((b :: bits).length : Int) := by
      rw [hdHead, List.length_cons]
      omega
    refine ⟨e, ?_, hState, hHead.trans hEnd, block_cons.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa only [List.length_cons] using Runs.cons le_rfl (by omega) hStep
        (run.widen (by omega) (le_of_eq hEnd))
    · rw [hFrame.cells bank _ (.inr (.inl (by omega)))]
      simp [d, advance]
    · rw [← hdHead]
      exact hBits
    · have hf : Framed c d (c.workHead bank) (c.workHead bank + 1) := frame_write ..
      exact frame_trans hf hFrame le_rfl (by simp [List.length_cons])
        (by omega) (le_of_eq hEnd)

/-- Reset the selected cursor to the left blank marker without modifying any work cell. -/
theorem executeRewind (word : List Bool) (c : Config bank op) (base : Int) (k : ℕ)
    (hq : c.state = 3) (hh : c.workHead bank = base + k)
    (hLeft : c.workCell bank base = none)
    (hBits : ∀ i : ℕ, i < k → ∃ b, c.workCell bank (base + (i : Int) + 1) = some b) :
    ∃ d, Runs word base (base + k) (k + 1) c d ∧
      d.state = 4 ∧ d.workHead bank = base ∧ Framed c d base base := by
  induction k generalizing c with
  | zero =>
    have hHead : c.workHead bank = base := by simpa using hh
    let d := advance c 4 .stay none
    have hStep := step_rewind_marker word c hq (hHead ▸ hLeft)
    have hdHead : d.workHead bank = base := by simp [d, advance, moveOffset, hHead]
    refine ⟨d, ?_, rfl, hdHead, frame_idle ..⟩
    simpa [d] using
      Runs.cons (le_of_eq hHead.symm) (le_of_eq hHead) hStep
        (Runs.nil _ (le_of_eq hdHead.symm) (le_of_eq hdHead))
  | succ k ih =>
    obtain ⟨b, hb⟩ := hBits k (by omega)
    have hRead : c.workCell bank (c.workHead bank) = some b := by
      rw [hh]
      convert hb using 2
      omega
    let d := advance c 3 .left none
    have hStep := step_rewind_bit word c b hq hRead
    have hdHead : d.workHead bank = base + k := by
      simp [d, advance, hh, moveOffset]
      omega
    have hdCell : d.workCell bank = c.workCell bank := by
      funext j
      simp [d, advance]
    obtain ⟨e, run, hState, hHead, hFrame⟩ :=
      ih d rfl hdHead (by simpa only [hdCell] using hLeft)
        (fun i hi => by simpa only [hdCell] using hBits i (by omega))
    refine ⟨e, Runs.cons (by omega) (le_of_eq hh) hStep
      (run.widen le_rfl (by omega)), hState, hHead, ?_⟩
    exact frame_trans (frame_idle c 3 .left base base) hFrame le_rfl le_rfl le_rfl le_rfl

/-- Carry or borrow from a prepared register in exactly two traversals.
The selected work head starts and returns on the left marker. The run
physically stays between the two markers, and every other tape is preserved. -/
theorem execute (word : List Bool) (c : Config bank op) (bits : List Bool)
    (hq : c.state = 0) (hLeft : c.workCell bank (c.workHead bank) = none)
    (hRight : c.workCell bank (c.workHead bank + bits.length + 1) = none)
    (hBits : block (c.workCell bank) (c.workHead bank + 1) bits) :
    ∃ d, Runs word (c.workHead bank) (c.workHead bank + bits.length + 1)
        (2 * bits.length + 3) c d ∧
      d.state = 4 ∧ d.workHead bank = c.workHead bank ∧
      block (d.workCell bank) (c.workHead bank + 1) (ripple op true bits) ∧
      Framed c d (c.workHead bank + 1) (c.workHead bank + bits.length + 1) := by
  let a := advance c (scanState true) .right none
  have haHead : a.workHead bank = c.workHead bank + 1 := by simp [a, advance, moveOffset]
  have haCell : a.workCell bank = c.workCell bank := by
    funext j
    simp [a, advance]
  obtain ⟨b, runScan, hbState, hbHead, hbBits, hbFrame⟩ :=
    scan word a true bits rfl (by simpa only [haHead, haCell] using hBits)
  have hbHead' : b.workHead bank = c.workHead bank + bits.length + 1 := by omega
  have hbLeft : b.workCell bank (c.workHead bank) = none := by
    rw [hbFrame.cells bank _ (.inr (.inl (by omega))), haCell]
    exact hLeft
  have hbRight : b.workCell bank (b.workHead bank) = none := by
    rw [hbFrame.cells bank _ (.inr (.inr (by omega))), haCell, hbHead']
    exact hRight
  let t := advance b 3 .left none
  have htHead : t.workHead bank = c.workHead bank + bits.length := by
    simp [t, advance, moveOffset, hbHead']
  have htCell : t.workCell bank = b.workCell bank := by
    funext j
    simp [t, advance]
  have htBits : ∀ i : ℕ, i < bits.length → ∃ bit,
      t.workCell bank (c.workHead bank + (i : Int) + 1) = some bit := by
    intro i hi
    have h := hbBits ⟨i, by simpa using hi⟩
    rw [htCell]
    rw [haHead] at h
    exact ⟨_, by simpa [Int.add_assoc, Int.add_comm (1 : Int)] using h⟩
  obtain ⟨d, runRewind, hdState, hdHead, hdFrame⟩ := executeRewind word t (c.workHead bank)
    bits.length rfl htHead (by simpa only [htCell] using hbLeft) htBits
  have run₁ : Runs word (c.workHead bank) (c.workHead bank + bits.length + 1)
      (bits.length + 1) c b :=
    .cons le_rfl (by omega) (step_enter word c hq)
      (runScan.widen (by omega) (by omega))
  have run₂ : Runs word (c.workHead bank) (c.workHead bank + bits.length + 1)
      (bits.length + 1 + 1) b d :=
    .cons (by omega) (le_of_eq hbHead') (step_scan_marker word b _ hbState hbRight)
      (runRewind.widen le_rfl (by omega))
  have hLen : (bits.length + 1 + 1) + (bits.length + 1) = 2 * bits.length + 3 := by omega
  refine ⟨d, hLen ▸ run₁.append run₂, hdState, hdHead, ?_, ?_⟩
  · intro i
    rw [hdFrame.cells bank _ (.inr (.inr (by omega))), htCell]
    simpa only [haHead] using hbBits i
  · have h₁ : Framed c a (c.workHead bank + 1) (c.workHead bank + bits.length + 1) :=
      frame_idle ..
    have h₂ : Framed c b (c.workHead bank + 1) (c.workHead bank + bits.length + 1) :=
      frame_trans h₁ hbFrame le_rfl le_rfl (by omega) (by omega)
    have h₃ : Framed c t (c.workHead bank + 1) (c.workHead bank + bits.length + 1) :=
      frame_trans h₂ (frame_idle b 3 .left _ _) le_rfl le_rfl le_rfl le_rfl
    have h₄ : Framed t d (c.workHead bank + 1) (c.workHead bank + bits.length + 1) :=
      ⟨hdFrame.input, hdFrame.output, hdFrame.heads, fun i j _ =>
        hdFrame.cells i j (.inr (lt_or_ge j (c.workHead bank)))⟩
    exact frame_trans h₃ h₄ le_rfl le_rfl le_rfl le_rfl

private theorem encodeLabel_cons (w value : ℕ) :
    encodeLabel (w + 1) value = value.testBit 0 :: encodeLabel w (value / 2) := by
  simp [encodeLabel, List.range_succ_eq_map, Function.comp_def, Nat.testBit_succ]

@[simp] theorem ripple_noCarry (op : Operation) (bits : List Bool) :
    ripple op false bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [ripple, changed, propagate, ih]

/-- Exact natural-number increment with the fixed-width encoding's usual truncation. -/
theorem ripple_increment_encodeLabel (w value : ℕ) :
    ripple .increment true (encodeLabel w value) = encodeLabel w (value + 1) := by
  induction w generalizing value with
  | zero => rfl
  | succ w ih =>
    rw [encodeLabel_cons, encodeLabel_cons]
    by_cases h : value % 2 = 0
    · have hParity : (value + 1) % 2 = 1 := by omega
      have hHalf : (value + 1) / 2 = value / 2 := by omega
      simp [ripple, changed, propagate, Nat.testBit_zero, h, hParity, hHalf]
    · have hOdd : value % 2 = 1 := by omega
      have hParity : (value + 1) % 2 = 0 := by omega
      have hHalf : (value + 1) / 2 = value / 2 + 1 := by omega
      simp [ripple, changed, propagate, Nat.testBit_zero, hOdd, hParity, hHalf, ih]

/-- Exact natural-number decrement for a positive count. -/
theorem ripple_decrement_encodeLabel (w value : ℕ) (positive : 0 < value) :
    ripple .decrement true (encodeLabel w value) = encodeLabel w (value - 1) := by
  induction w generalizing value with
  | zero => rfl
  | succ w ih =>
    rw [encodeLabel_cons, encodeLabel_cons]
    by_cases h : value % 2 = 0
    · have hParity : (value - 1) % 2 = 1 := by omega
      have hHalf : (value - 1) / 2 = value / 2 - 1 := by omega
      have hHalfPos : 0 < value / 2 := by omega
      simp [ripple, changed, propagate, Nat.testBit_zero, h, hParity, hHalf, ih _ hHalfPos]
    · have hOdd : value % 2 = 1 := by omega
      have hParity : (value - 1) % 2 = 0 := by omega
      have hHalf : (value - 1) / 2 = value / 2 := by omega
      simp [ripple, changed, propagate, Nat.testBit_zero, hOdd, hParity, hHalf]

/-- The physical register macro executes fixed-width natural-number increment. -/
theorem executeIncrement {bank : Fin tapes} (word : List Bool)
    (c : Config bank .increment) (w value : ℕ)
    (hq : c.state = 0) (hLeft : c.workCell bank (c.workHead bank) = none)
    (hRight : c.workCell bank (c.workHead bank + w + 1) = none)
    (hBits : block (c.workCell bank) (c.workHead bank + 1) (encodeLabel w value)) :
    ∃ d, Runs word (c.workHead bank) (c.workHead bank + w + 1) (2 * w + 3) c d ∧
      d.state = 4 ∧ d.workHead bank = c.workHead bank ∧
      block (d.workCell bank) (c.workHead bank + 1) (encodeLabel w (value + 1)) ∧
      Framed c d (c.workHead bank + 1) (c.workHead bank + w + 1) := by
  have hWidth : (encodeLabel w value).length = w := by simp [encodeLabel]
  simpa only [hWidth, ripple_increment_encodeLabel] using
    execute word c (encodeLabel w value) hq hLeft (by simpa only [hWidth] using hRight) hBits

/-- The physical register macro executes fixed-width decrement of a positive count. -/
theorem executeDecrement {bank : Fin tapes} (word : List Bool)
    (c : Config bank .decrement) (w value : ℕ) (positive : 0 < value)
    (hq : c.state = 0) (hLeft : c.workCell bank (c.workHead bank) = none)
    (hRight : c.workCell bank (c.workHead bank + w + 1) = none)
    (hBits : block (c.workCell bank) (c.workHead bank + 1) (encodeLabel w value)) :
    ∃ d, Runs word (c.workHead bank) (c.workHead bank + w + 1) (2 * w + 3) c d ∧
      d.state = 4 ∧ d.workHead bank = c.workHead bank ∧
      block (d.workCell bank) (c.workHead bank + 1) (encodeLabel w (value - 1)) ∧
      Framed c d (c.workHead bank + 1) (c.workHead bank + w + 1) := by
  have hWidth : (encodeLabel w value).length = w := by simp [encodeLabel]
  simpa only [hWidth, ripple_decrement_encodeLabel w value positive] using
    execute word c (encodeLabel w value) hq hLeft (by simpa only [hWidth] using hRight) hBits

/-- A checked macro run can be appended directly to the physical machine's
canonical execution relation at any reachable entry. -/
theorem Runs.after_add {word : List Bool} {lo hi : Int} {k : ℕ}
    {c d : Config bank op} (run : Runs word lo hi k c d) (start : ℕ)
    (hStart : (machine bank op).after word start = some c) :
    (machine bank op).after word (start + k) = some d := by
  induction run generalizing start with
  | nil => simpa using hStart
  | @cons n c e d hlo hhi hStep hRun ih =>
    have hNext : (machine bank op).after word (start + 1) = some e := by
      simpa [SearchTransducer.after, hStart] using hStep
    have hLen : start + (n + 1) = (start + 1) + n := by omega
    rw [hLen]
    exact ih (start + 1) hNext

end Mathproof.MinimumGeneration.TapeArithmetic
