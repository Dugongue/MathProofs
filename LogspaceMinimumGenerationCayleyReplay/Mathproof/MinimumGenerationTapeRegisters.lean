import Mathproof.MinimumGenerationTapeArithmetic
import Mathproof.MinimumGenerationTapeCompose

namespace Mathproof.MinimumGeneration.TapeRegisters

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open TapeArithmetic (block)

inductive Operation
  | copy
  | compare
  | zero

private def writeBit (op : Operation) (source target : Bool) : Bool :=
  match op with
  | .copy => source
  | .compare => target
  | .zero => false

private def compareBit (op : Operation) (equal source target : Bool) : Bool :=
  match op with
  | .compare => equal && (source == target)
  | _ => equal

private def scanPhase (equal : Bool) : Fin 7 := if equal then 1 else 2
private def returnPhase (equal : Bool) : Fin 7 := if equal then 3 else 4

/-- The returned bit is stored in finite control. -/
def done (equal : Bool) : Fin 7 := if equal then 5 else 6

private def driven (source target t : Fin tapes) : Prop := t = source ∨ t = target

private instance (source target t : Fin tapes) : Decidable (driven source target t) :=
  inferInstanceAs (Decidable (t = source ∨ t = target))

private def actions (source target : Fin tapes) (move : Move) (write : Option (Option Bool))
    (t : Fin tapes) : Action (Option Bool) :=
  ⟨if t = target then write else none, if driven source target t then move else .stay⟩

/-- Two banks are traversed synchronously. For zeroing, the two bank names
may identify the same bank, so a single work tape suffices. -/
abbrev machine {tapes : ℕ} (source target : Fin tapes) (op : Operation) : SearchTransducer where
  states := 7
  workTapes := tapes
  initialState := 0
  transition phase _ read :=
    let next := fun (q : Fin 7) (move : Move) (write : Option (Option Bool)) =>
      some (q, .stay, actions source target move write, none)
    if phase = 0 then next (scanPhase true) .right none
    else if phase = 1 ∨ phase = 2 then
      let equal := decide (phase = 1)
      match read source, read target with
      | some a, some b => next (scanPhase (compareBit op equal a b)) .right
          (some (some (writeBit op a b)))
      | none, none => next (returnPhase equal) .left none
      | _, _ => none
    else if phase = 3 ∨ phase = 4 then
      let equal := decide (phase = 3)
      match read target with
      | some _ => next (returnPhase equal) .left none
      | none => next (done equal) .stay none
    else none

variable {tapes : ℕ} {source target : Fin tapes} {op : Operation}

abbrev Config (source target : Fin tapes) (op : Operation) := (machine source target op).Config

private def advance (c : Config source target op) (q : Fin 7) (move : Move)
    (write : Option (Option Bool)) : Config source target op :=
  ⟨q, c.inputHead,
    fun t => if driven source target t then c.workHead t + moveOffset move else c.workHead t,
    fun t j => if t = target ∧ j = c.workHead target then write.getD (c.workCell t j)
      else c.workCell t j,
    c.outputReversed⟩

private theorem step_of_transition (word : List Bool) (c : Config source target op) (q : Fin 7)
    (move : Move) (write : Option (Option Bool))
    (h : (machine source target op).transition c.state (SearchTransducer.readInput word c.inputHead)
        (fun t => c.workCell t (c.workHead t)) =
      some (q, .stay, actions source target move write, none)) :
    (machine source target op).step word c = some (advance c q move write) := by
  unfold SearchTransducer.step
  rw [h]
  simp [advance, actions, moveOffset]
  constructor
  · funext t
    by_cases ht : driven source target t <;> simp [ht]
  · funext t j
    by_cases ht : t = target <;> simp [ht]

private theorem enter (word : List Bool) (c : Config source target op) (hq : c.state = 0) :
    (machine source target op).step word c = some (advance c (scanPhase true) .right none) := by
  apply step_of_transition
  simp [machine, hq]

private theorem scanBit (word : List Bool) (c : Config source target op) (eq a b : Bool)
    (hq : c.state = scanPhase eq)
    (ha : c.workCell source (c.workHead source) = some a)
    (hb : c.workCell target (c.workHead target) = some b) :
    (machine source target op).step word c = some
      (advance c (scanPhase (compareBit op eq a b)) .right (some (some (writeBit op a b)))) := by
  apply step_of_transition
  cases eq <;> simp [machine, hq, ha, hb, scanPhase]

private theorem scanMarker (word : List Bool) (c : Config source target op) (eq : Bool)
    (hq : c.state = scanPhase eq)
    (ha : c.workCell source (c.workHead source) = none)
    (hb : c.workCell target (c.workHead target) = none) :
    (machine source target op).step word c = some (advance c (returnPhase eq) .left none) := by
  apply step_of_transition
  cases eq <;> simp [machine, hq, ha, hb, scanPhase]

private theorem returnBit (word : List Bool) (c : Config source target op) (eq b : Bool)
    (hq : c.state = returnPhase eq)
    (hb : c.workCell target (c.workHead target) = some b) :
    (machine source target op).step word c = some (advance c (returnPhase eq) .left none) := by
  apply step_of_transition
  cases eq <;> simp [machine, hq, hb, returnPhase]

private theorem returnMarker (word : List Bool) (c : Config source target op) (eq : Bool)
    (hq : c.state = returnPhase eq)
    (hb : c.workCell target (c.workHead target) = none) :
    (machine source target op).step word c = some (advance c (done eq) .stay none) := by
  apply step_of_transition
  cases eq <;> simp [machine, hq, hb, returnPhase]

theorem step_done (word : List Bool) (c : Config source target op) (equal : Bool)
    (hq : c.state = done equal) : (machine source target op).step word c = none := by
  cases equal <;> simp [SearchTransducer.step, machine, done, hq]

private theorem block_cons {cell : Int → Option Bool} {p : Int} {a : Bool} {xs : List Bool} :
    block cell p (a :: xs) ↔ cell p = some a ∧ block cell (p + 1) xs := by
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0, by simp⟩, ?_⟩
    intro i
    simpa [Int.add_assoc, Int.add_comm (1 : Int)] using h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  · rintro ⟨hFirst, hTail⟩ ⟨val, lt⟩
    cases val with
    | zero => simpa using hFirst
    | succ val =>
      simpa [Int.add_assoc, Int.add_comm (1 : Int)] using
        hTail ⟨val, Nat.lt_of_succ_lt_succ lt⟩

/-- The output payload of one paired pass. Nominally the inputs have the same width. -/
def payload (op : Operation) (xs ys : List Bool) : List Bool :=
  List.zipWith (writeBit op) xs ys

def verdict (op : Operation) (eq : Bool) : List Bool → List Bool → Bool
  | a :: xs, b :: ys => verdict op (compareBit op eq a b) xs ys
  | _, _ => eq

/-- Every configuration of this run has all work heads within the indicated
coordinate bounds. Idle banks have intervals of size one. -/
def Within (c : Config source target op) (lo hi : Fin tapes → Int) : Prop :=
  ∀ t, lo t ≤ c.workHead t ∧ c.workHead t ≤ hi t

def finish (base : Fin tapes → Int) (source target : Fin tapes) (offset : Int)
    (t : Fin tapes) : Int :=
  if driven source target t then base t + offset else base t

inductive Runs (word : List Bool) (lo hi : Fin tapes → Int) :
    ℕ → Config source target op → Config source target op → Prop
  | nil (c) (hc : Within c lo hi) : Runs word lo hi 0 c c
  | cons {n c d e} (hc : Within c lo hi) (step : (machine source target op).step word c = some d)
      (rest : Runs word lo hi n d e) : Runs word lo hi (n + 1) c e

private theorem Runs.widen {word : List Bool} {lo hi lo' hi' : Fin tapes → Int}
    {n : ℕ} {a b : Config source target op} (run : Runs word lo hi n a b)
    (hlo : ∀ t, lo' t ≤ lo t) (hhi : ∀ t, hi t ≤ hi' t) :
    Runs word lo' hi' n a b := by
  induction run with
  | nil c hc => exact .nil c (fun t => ⟨(hlo t).trans (hc t).1, (hc t).2.trans (hhi t)⟩)
  | cons hc step _ ih => exact .cons (fun t => ⟨(hlo t).trans (hc t).1, (hc t).2.trans (hhi t)⟩) step ih

private theorem Runs.append {word : List Bool} {lo hi : Fin tapes → Int}
    {m n : ℕ} {a b c : Config source target op}
    (first : Runs word lo hi m a b) (last : Runs word lo hi n b c) :
    Runs word lo hi (n + m) a c := by
  induction first with
  | nil => simpa using last
  | cons hc step _ ih => exact .cons hc step (ih last)

/-- The paired register caller leaves all work cells outside its target block alone. -/
structure Framed (c d : Config source target op) (lo hi : Int) : Prop where
  input : d.inputHead = c.inputHead
  output : d.outputReversed = c.outputReversed
  cell : ∀ t j, t ≠ target ∨ j < lo ∨ hi ≤ j → d.workCell t j = c.workCell t j

private theorem frame_trans {c d e : Config source target op} {l₁ h₁ l₂ h₂ lo hi : Int}
    (before : Framed c d l₁ h₁) (after : Framed d e l₂ h₂)
    (hl₁ : lo ≤ l₁) (hh₁ : h₁ ≤ hi) (hl₂ : lo ≤ l₂) (hh₂ : h₂ ≤ hi) :
    Framed c e lo hi := by
  refine ⟨after.input.trans before.input, after.output.trans before.output, ?_⟩
  intro t j h
  rcases h with ht | hl | hh
  · exact (after.cell t j (.inl ht)).trans (before.cell t j (.inl ht))
  · exact (after.cell t j (.inr (.inl (lt_of_lt_of_le hl hl₂)))).trans
      (before.cell t j (.inr (.inl (lt_of_lt_of_le hl hl₁))))
  · exact (after.cell t j (.inr (.inr (hh₂.trans hh)))).trans
      (before.cell t j (.inr (.inr (hh₁.trans hh))))

private theorem frame_idle (c : Config source target op) (q : Fin 7) (m : Move) (lo hi : Int) :
    Framed c (advance c q m none) lo hi :=
  ⟨rfl, rfl, fun t j _ => by simp [advance]⟩

private theorem frame_write (c : Config source target op) (q : Fin 7) (m : Move) (b : Bool) :
    Framed c (advance c q m (some (some b))) (c.workHead target) (c.workHead target + 1) := by
  refine ⟨rfl, rfl, ?_⟩
  intro t j h
  rcases h with ht | hl | hh
  · simp [advance, ht]
  · simp [advance, ne_of_lt hl]
  · have hn : j ≠ c.workHead target := by omega
    simp [advance, hn]

private theorem advance_cell_future (c : Config source target op) (q : Fin 7) (m : Move)
    (write : Option (Option Bool)) (t : Fin tapes) (j : Int) (h : c.workHead t < j) :
    (advance c q m write).workCell t j = c.workCell t j := by
  by_cases ht : t = target
  · subst t
    simp [advance, ne_of_gt h]
  · simp [advance, ht]

private theorem finish_mono {base : Fin tapes → Int} {a b : Int} (h : a ≤ b) (t : Fin tapes) :
    finish base source target a t ≤ finish base source target b t := by
  by_cases ht : driven source target t <;> simp [finish, ht, h]

private theorem finish_ge (base : Fin tapes → Int) {o : Int} (h : 0 ≤ o) (t : Fin tapes) :
    base t ≤ finish base source target o t := by
  by_cases ht : driven source target t <;> simp [finish, ht, h]

private theorem finish_finish (base : Fin tapes → Int) (a b : Int) :
    finish (finish base source target a) source target b = finish base source target (a + b) := by
  funext t
  by_cases ht : driven source target t <;> simp [finish, ht, Int.add_assoc]

private theorem right_head (c : Config source target op) (q : Fin 7)
    (write : Option (Option Bool)) :
    (advance c q .right write).workHead = finish c.workHead source target 1 := rfl

private theorem left_head (c : Config source target op) (q : Fin 7)
    (write : Option (Option Bool)) :
    (advance c q .left write).workHead = finish c.workHead source target (-1) := rfl

private theorem scan (word : List Bool) (c : Config source target op) (eq : Bool)
    (xs ys : List Bool) (lengths : xs.length = ys.length)
    (hq : c.state = scanPhase eq)
    (hSource : block (c.workCell source) (c.workHead source) xs)
    (hTarget : block (c.workCell target) (c.workHead target) ys) :
    ∃ d, Runs word c.workHead (finish c.workHead source target xs.length) xs.length c d ∧
      d.state = scanPhase (verdict op eq xs ys) ∧
      d.workHead = finish c.workHead source target xs.length ∧
      block (d.workCell target) (c.workHead target) (payload op xs ys) ∧
      Framed c d (c.workHead target) (c.workHead target + xs.length) := by
  induction xs generalizing c eq ys with
  | nil =>
    refine ⟨c, .nil c ?_, hq, ?_, fun i => Fin.elim0 i, ⟨rfl, rfl, fun _ _ _ => rfl⟩⟩
    · intro t
      exact ⟨le_rfl, finish_ge _ (by simp) _⟩
    · funext t
      simp [finish]
  | cons a xs ih =>
    cases ys with
    | nil => simp at lengths
    | cons b ys =>
      have len : xs.length = ys.length := by simpa using lengths
      obtain ⟨hFirstA, hTailA⟩ := block_cons.mp hSource
      obtain ⟨hFirstB, hTailB⟩ := block_cons.mp hTarget
      let d := advance c (scanPhase (compareBit op eq a b)) .right (some (some (writeBit op a b)))
      have hh : d.workHead = finish c.workHead source target 1 := right_head ..
      have hA : d.workHead source = c.workHead source + 1 := by simp [hh, finish, driven]
      have hB : d.workHead target = c.workHead target + 1 := by simp [hh, finish, driven]
      have hS : block (d.workCell source) (d.workHead source) xs := by
        intro i
        rw [hA, advance_cell_future _ _ _ _ _ _ (by omega)]
        exact hTailA i
      have hT : block (d.workCell target) (d.workHead target) ys := by
        intro i
        rw [hB, advance_cell_future _ _ _ _ _ _ (by omega)]
        exact hTailB i
      obtain ⟨e, run, hfState, hfHead, hfBlock, hfFrame⟩ :=
        ih d (compareBit op eq a b) ys len rfl hS hT
      have hEnd : finish d.workHead source target xs.length =
          finish c.workHead source target (a :: xs).length := by
        rw [hh, finish_finish]
        congr 1
        simp [Int.add_comm]
      refine ⟨e, ?_, hfState, hfHead.trans hEnd, block_cons.mpr ⟨?_, ?_⟩, ?_⟩
      · exact .cons (fun t => ⟨le_rfl, finish_ge _ (by omega) t⟩)
          (scanBit word c eq a b hq hFirstA hFirstB)
          (run.widen (by rw [hh]; exact finish_ge _ (by omega))
            (fun t => le_of_eq (congrFun hEnd t)))
      · rw [hfFrame.cell target _ (.inr (.inl (by omega)))]
        simp [d, advance]
      · rw [← hB]
        exact hfBlock
      · exact frame_trans (frame_write c _ .right _) hfFrame le_rfl (by simp)
          (by omega) (by simp only [List.length_cons, hB]; omega)

private theorem rewind (word : List Bool) (c : Config source target op) (eq : Bool)
    (base : Fin tapes → Int) (k : ℕ) (hq : c.state = returnPhase eq)
    (hh : c.workHead = finish base source target k)
    (hLeft : c.workCell target (base target) = none)
    (hBits : ∀ i : ℕ, i < k → ∃ b, c.workCell target (base target + (i : Int) + 1) = some b) :
    ∃ d, Runs word base (finish base source target k) (k + 1) c d ∧
      d.state = done eq ∧ d.workHead = base ∧ d.workCell = c.workCell ∧
      d.inputHead = c.inputHead ∧ d.outputReversed = c.outputReversed := by
  have hHead : c.workHead target = base target + k := by
    simp [hh, finish, driven]
  induction k generalizing c with
  | zero =>
    have hc : c.workHead = base := by
      funext t
      simp [hh, finish]
    let d := advance c (done eq) .stay none
    have hd : d.workHead = base := by
      funext t
      simp [d, advance, hc, moveOffset]
    have hStep := returnMarker word c eq hq (congrFun hc target ▸ hLeft)
    refine ⟨d, .cons ?_ hStep (.nil d ?_), rfl, hd, ?_, rfl, rfl⟩
    · intro t
      simp [hc, finish]
    · intro t
      simp [hd, finish]
    · funext t j
      simp [d, advance]
  | succ k ih =>
    obtain ⟨b, hBit⟩ := hBits k (by omega)
    have hRead : c.workCell target (c.workHead target) = some b := by
      rw [hHead]
      convert hBit using 2
      omega
    let d := advance c (returnPhase eq) .left none
    have hdHead : d.workHead = finish base source target k := by
      rw [left_head, hh, finish_finish]
      congr 1
      omega
    have hdCell : d.workCell = c.workCell := by
      funext t j
      simp [d, advance]
    obtain ⟨e, run, heState, heHead, heCell, heInput, heOutput⟩ :=
      ih d rfl hdHead (by simpa only [hdCell] using hLeft)
        (fun i hi => by simpa only [hdCell] using hBits i (by omega))
        (by simp [hdHead, finish, driven])
    exact ⟨e, .cons (fun t => ⟨by rw [hh]; exact finish_ge _ (by omega) _, by rw [hh]⟩)
      (returnBit word c eq b hq hRead) (run.widen (fun _ => le_rfl) (finish_mono (by omega))),
      heState, heHead, heCell.trans hdCell, heInput, heOutput⟩

/-- One exact physical copy, compare, or zero pass. The destination has the
computed payload, the returned verdict is in finite control, and both cursors
are restored. Every work head is bounded on every prefix of the execution. -/
theorem execute (word : List Bool) (c : Config source target op) (xs ys : List Bool)
    (lengths : xs.length = ys.length) (hq : c.state = 0)
    (hLeft : c.workCell target (c.workHead target) = none)
    (hRightS : c.workCell source (c.workHead source + xs.length + 1) = none)
    (hRightT : c.workCell target (c.workHead target + xs.length + 1) = none)
    (hSource : block (c.workCell source) (c.workHead source + 1) xs)
    (hTarget : block (c.workCell target) (c.workHead target + 1) ys) :
    ∃ d, Runs word c.workHead (finish c.workHead source target (xs.length + 1))
        (2 * xs.length + 3) c d ∧
      d.state = done (verdict op true xs ys) ∧ d.workHead = c.workHead ∧
      block (d.workCell target) (c.workHead target + 1) (payload op xs ys) ∧
      Framed c d (c.workHead target + 1) (c.workHead target + xs.length + 1) := by
  let a := advance c (scanPhase true) .right none
  have haHead : a.workHead = finish c.workHead source target 1 := right_head ..
  have haS : a.workHead source = c.workHead source + 1 := by simp [haHead, finish, driven]
  have haT : a.workHead target = c.workHead target + 1 := by simp [haHead, finish, driven]
  have haCell : a.workCell = c.workCell := by
    funext t j
    simp [a, advance]
  obtain ⟨b, runScan, hbState, hbHead, hbBlock, hbFrame⟩ := scan word a true xs ys lengths rfl
    (by simpa only [haS, haCell] using hSource) (by simpa only [haT, haCell] using hTarget)
  have hbHead' : b.workHead = finish c.workHead source target (xs.length + 1) := by
    rw [hbHead, haHead, finish_finish, Int.add_comm]
  have hbS : b.workHead source = c.workHead source + xs.length + 1 := by
    simp [hbHead', finish, driven, Int.add_assoc]
  have hbT : b.workHead target = c.workHead target + xs.length + 1 := by
    simp [hbHead', finish, driven, Int.add_assoc]
  have hbLeft : b.workCell target (c.workHead target) = none := by
    rw [hbFrame.cell target _ (.inr (.inl (by omega))), haCell]
    exact hLeft
  have hbRightS : b.workCell source (b.workHead source) = none := by
    rw [hbS]
    suffices hf : source ≠ target ∨
        c.workHead source + (xs.length : Int) + 1 < a.workHead target ∨
        a.workHead target + (xs.length : Int) ≤ c.workHead source + (xs.length : Int) + 1 by
      rw [hbFrame.cell source _ hf, haCell]
      exact hRightS
    by_cases equal : source = target
    · right
      right
      have he : c.workHead source = c.workHead target := congrArg c.workHead equal
      omega
    · exact .inl equal
  have hbRightT : b.workCell target (b.workHead target) = none := by
    rw [hbFrame.cell target _ (.inr (.inr (by omega))), haCell, hbT]
    exact hRightT
  let t := advance b (returnPhase (verdict op true xs ys)) .left none
  have htHead : t.workHead = finish c.workHead source target xs.length := by
    rw [left_head, hbHead', finish_finish]
    congr 1
    omega
  have htCell : t.workCell = b.workCell := by
    funext k j
    simp [t, advance]
  have hpLen : (payload op xs ys).length = xs.length := by
    simp [payload, ← lengths]
  have htBits : ∀ i : ℕ, i < xs.length →
      ∃ bit, t.workCell target (c.workHead target + (i : Int) + 1) = some bit := by
    intro i hi
    have h := hbBlock ⟨i, by simpa only [hpLen] using hi⟩
    rw [haT] at h
    exact ⟨_, by simpa [htCell, Int.add_assoc, Int.add_comm (1 : Int)] using h⟩
  obtain ⟨d, runRewind, hdState, hdHead, hdCell, hdInput, hdOutput⟩ :=
    rewind word t (verdict op true xs ys) c.workHead xs.length rfl htHead
      (by simpa only [htCell] using hbLeft) htBits
  have run₁ : Runs word c.workHead (finish c.workHead source target (xs.length + 1))
      (xs.length + 1) c b :=
    .cons (fun i => ⟨le_rfl, finish_ge _ (by omega) i⟩) (enter word c hq)
      (runScan.widen (by rw [haHead]; exact finish_ge _ (by omega))
        (fun i => (congrFun (hbHead.symm.trans hbHead') i).le))
  have run₂ : Runs word c.workHead (finish c.workHead source target (xs.length + 1))
      (xs.length + 1 + 1) b d :=
    .cons (fun i => ⟨by rw [hbHead']; exact finish_ge _ (by omega) i, (congrFun hbHead' i).le⟩)
      (scanMarker word b _ hbState hbRightS hbRightT)
      (runRewind.widen (fun _ => le_rfl) (finish_mono (by omega)))
  have hLen : (xs.length + 1 + 1) + (xs.length + 1) = 2 * xs.length + 3 := by omega
  refine ⟨d, hLen ▸ run₁.append run₂, hdState, hdHead, ?_, ?_⟩
  · simpa only [hdCell, htCell, haT] using hbBlock
  · refine ⟨hdInput.trans (hbFrame.input.trans rfl), hdOutput.trans (hbFrame.output.trans rfl), ?_⟩
    intro bank j hj
    rw [hdCell, htCell, hbFrame.cell bank j (by simpa [haT, Int.add_assoc, Int.add_comm (1 : Int)] using hj),
      haCell]

theorem payload_copy (xs ys : List Bool) (lengths : xs.length = ys.length) :
    payload .copy xs ys = xs := by
  induction xs generalizing ys with
  | nil => simp [payload]
  | cons a xs ih =>
    cases ys with
    | nil => simp at lengths
    | cons b ys =>
      change _ :: payload _ xs ys = _
      rw [ih ys (by simpa using lengths)]
      rfl

theorem payload_compare (xs ys : List Bool) (lengths : xs.length = ys.length) :
    payload .compare xs ys = ys := by
  induction xs generalizing ys with
  | nil =>
    have h : ys = [] := by simpa using lengths.symm
    simp [payload, h]
  | cons a xs ih =>
    cases ys with
    | nil => simp at lengths
    | cons b ys =>
      change _ :: payload _ xs ys = _
      rw [ih ys (by simpa using lengths)]
      rfl

theorem payload_zero (xs : List Bool) :
    payload .zero xs xs = List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change false :: payload .zero xs xs = _
    rw [ih]
    rfl

theorem compare_verdict (xs ys : List Bool) (lengths : xs.length = ys.length) (eq : Bool) :
    verdict .compare eq xs ys = true ↔ eq = true ∧ xs = ys := by
  induction xs generalizing ys eq with
  | nil =>
    have h : ys = [] := by simpa using lengths.symm
    simp [verdict, h]
  | cons a xs ih =>
    cases ys with
    | nil => simp at lengths
    | cons b ys =>
      rw [verdict, ih ys (by simpa using lengths)]
      simp [compareBit, and_assoc]

private theorem verdict_copy (xs ys : List Bool) :
    verdict .copy true xs ys = true := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a xs ih => cases ys with
    | nil => rfl
    | cons b ys => exact ih ys

private theorem verdict_zero (xs : List Bool) : verdict .zero true xs xs = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact ih

/-- Exact copy between two prepared registers. When the banks are distinct,
the source is preserved by the returned frame. -/
theorem executeCopy (word : List Bool) (c : Config source target .copy) (xs ys : List Bool)
    (lengths : xs.length = ys.length) (hq : c.state = 0)
    (hLeft : c.workCell target (c.workHead target) = none)
    (hRightS : c.workCell source (c.workHead source + xs.length + 1) = none)
    (hRightT : c.workCell target (c.workHead target + xs.length + 1) = none)
    (hSource : block (c.workCell source) (c.workHead source + 1) xs)
    (hTarget : block (c.workCell target) (c.workHead target + 1) ys) :
    ∃ d, Runs word c.workHead (finish c.workHead source target (xs.length + 1))
        (2 * xs.length + 3) c d ∧ d.state = done true ∧ d.workHead = c.workHead ∧
      block (d.workCell target) (c.workHead target + 1) xs ∧
      Framed c d (c.workHead target + 1) (c.workHead target + xs.length + 1) := by
  simpa only [payload_copy xs ys lengths, verdict_copy] using
    execute word c xs ys lengths hq hLeft hRightS hRightT hSource hTarget

/-- The terminal control bit is true exactly when the two registers agree.
Their contents are available unchanged on return. -/
theorem executeCompare (word : List Bool) (c : Config source target .compare) (xs ys : List Bool)
    (lengths : xs.length = ys.length) (hq : c.state = 0)
    (hLeft : c.workCell target (c.workHead target) = none)
    (hRightS : c.workCell source (c.workHead source + xs.length + 1) = none)
    (hRightT : c.workCell target (c.workHead target + xs.length + 1) = none)
    (hSource : block (c.workCell source) (c.workHead source + 1) xs)
    (hTarget : block (c.workCell target) (c.workHead target + 1) ys) :
    ∃ (d : Config source target .compare) (equal : Bool),
      Runs word c.workHead (finish c.workHead source target (xs.length + 1)) (2 * xs.length + 3) c d ∧
      d.state = done equal ∧ (equal = true ↔ xs = ys) ∧ d.workHead = c.workHead ∧
      d.workCell = c.workCell ∧ d.inputHead = c.inputHead ∧ d.outputReversed = c.outputReversed := by
  obtain ⟨d, run, state, heads, bits, frame⟩ :=
    execute word c xs ys lengths hq hLeft hRightS hRightT hSource hTarget
  refine ⟨d, verdict .compare true xs ys, run, state, by simpa using compare_verdict xs ys lengths true,
    heads, ?_, frame.input, frame.output⟩
  rw [payload_compare xs ys lengths] at bits
  funext t j
  by_cases ht : t = target
  · by_cases hLow : j < c.workHead target + 1
    · exact frame.cell t j (.inr (.inl hLow))
    · by_cases hHigh : c.workHead target + xs.length + 1 ≤ j
      · exact frame.cell t j (.inr (.inr hHigh))
      · let i := (j - (c.workHead target + 1)).toNat
        have hi : (i : Int) = j - (c.workHead target + 1) := by
          exact Int.toNat_of_nonneg (by omega)
        have hLen : i < ys.length := by omega
        have hj : c.workHead target + 1 + (i : Int) = j := by omega
        rw [ht, ← hj]
        exact (bits ⟨i, hLen⟩).trans (hTarget ⟨i, hLen⟩).symm
  · exact frame.cell t j (.inl ht)

/-- Zero one prepared register of any width, using only its bank. -/
theorem executeZero (word : List Bool) (c : Config target target .zero) (xs : List Bool)
    (hq : c.state = 0) (hLeft : c.workCell target (c.workHead target) = none)
    (hRight : c.workCell target (c.workHead target + xs.length + 1) = none)
    (hBits : block (c.workCell target) (c.workHead target + 1) xs) :
    ∃ d, Runs word c.workHead (finish c.workHead target target (xs.length + 1))
        (2 * xs.length + 3) c d ∧ d.state = done true ∧ d.workHead = c.workHead ∧
      block (d.workCell target) (c.workHead target + 1) (List.replicate xs.length false) ∧
      Framed c d (c.workHead target + 1) (c.workHead target + xs.length + 1) := by
  simpa only [payload_zero, verdict_zero] using
    execute word c xs xs rfl hq hLeft hRight hRight hBits hBits

/-- A paired register edit is composable with the canonical machine execution relation. -/
theorem Runs.after_add {word : List Bool} {lo hi : Fin tapes → Int} {k : ℕ}
    {c d : Config source target op} (run : Runs word lo hi k c d) (start : ℕ)
    (hStart : (machine source target op).after word start = some c) :
    (machine source target op).after word (start + k) = some d := by
  induction run generalizing start with
  | nil => simpa using hStart
  | @cons n c e d hc hStep hRun ih =>
    have hNext : (machine source target op).after word (start + 1) = some e := by
      simpa [SearchTransducer.after, hStart] using hStep
    have hLen : start + (n + 1) = (start + 1) + n := by omega
    rw [hLen]
    exact ih (start + 1) hNext


/-- Compare a prepared bank with the same-width zero bank. The saved zero
bank and the tested word remain intact. -/
theorem executeIsZero (word : List Bool) (c : Config source target .compare) (xs : List Bool)
    (hq : c.state = 0) (hLeft : c.workCell target (c.workHead target) = none)
    (hRightS : c.workCell source (c.workHead source + xs.length + 1) = none)
    (hRightT : c.workCell target (c.workHead target + xs.length + 1) = none)
    (hSource : block (c.workCell source) (c.workHead source + 1) xs)
    (hZero : block (c.workCell target) (c.workHead target + 1) (List.replicate xs.length false)) :
    ∃ (d : Config source target .compare) (zero : Bool),
      Runs word c.workHead (finish c.workHead source target (xs.length + 1)) (2 * xs.length + 3) c d ∧
      d.state = done zero ∧ (zero = true ↔ xs = List.replicate xs.length false) ∧
      d.workHead = c.workHead ∧ d.workCell = c.workCell ∧
      d.inputHead = c.inputHead ∧ d.outputReversed = c.outputReversed :=
  executeCompare word c xs (List.replicate xs.length false) (by simp) hq hLeft
    hRightS hRightT hSource hZero

private theorem step_fixed {M : SearchTransducer} {word : List Bool} {c d : M.Config}
    {fixedBank : Fin M.workTapes → Prop}
    (stationary : ∀ q inp reads r, M.transition q inp reads = some r →
      r.2.1 = .stay ∧ ∀ t, fixedBank t → (r.2.2.1 t).move = .stay)
    (step : M.step word c = some d) :
    d.inputHead = c.inputHead ∧ ∀ t, fixedBank t → d.workHead t = c.workHead t := by
  unfold SearchTransducer.step at step
  cases h : M.transition c.state (SearchTransducer.readInput word c.inputHead)
      (fun t => c.workCell t (c.workHead t)) with
  | none => simp [h] at step
  | some r =>
    obtain ⟨state, inp, acts, out⟩ := r
    obtain ⟨fixedInput, fixedWork⟩ := stationary _ _ _ _ h
    simp only [h, Option.map_some, Option.some.injEq] at step
    subst d
    change inp = .stay at fixedInput
    refine ⟨by simp [fixedInput, moveOffset], fun t ht => ?_⟩
    specialize fixedWork t ht
    change (acts t).move = .stay at fixedWork
    simp [fixedWork, moveOffset]

private theorem registerStepInput {word : List Bool} {c d : Config source target op}
    (step : (machine source target op).step word c = some d) : d.inputHead = c.inputHead := by
  refine (step_fixed (fixedBank := fun _ => False) ?_ step).1
  intro q inp reads r trans
  have hMove : r.2.1 = .stay := by
    simp only [machine] at trans
    split at trans
    · cases trans; rfl
    · split at trans
      · split at trans <;> cases trans <;> rfl
      · split at trans
        · split at trans <;> cases trans <;> rfl
        · cases trans
  exact ⟨hMove, fun _ impossible => impossible.elim⟩

private theorem singleStepSegment {M : SearchTransducer} {word : List Bool} {B : ℕ}
    {c d : M.Config} (step : M.step word c = some d)
    (before : M.Bounded word B c) (after : M.Bounded word B d) :
    M.BoundedSegment word B c d 1 := by
  have run : M.runFrom word c 1 = some d := by simpa [SearchTransducer.runFrom] using step
  refine ⟨run, ?_⟩
  intro k hk x hx
  have casesK : k = 0 ∨ k = 1 := by omega
  rcases casesK with rfl | rfl
  · change some c = some x at hx
    cases hx
    exact before
  · rw [run] at hx
    cases hx
    exact after

/-- Convert the exact paired-register run to the existing framed composition
model once a common absolute bound for its head intervals has been fixed. -/
theorem Runs.boundedSegment {word : List Bool} {lo hi : Fin tapes → Int} {B k : ℕ}
    {c d : Config source target op} (run : Runs word lo hi k c d)
    (input : (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (word.length : Int))
    (windows : ∀ t j, lo t ≤ j → j ≤ hi t → j.natAbs ≤ B) :
    (machine source target op).BoundedSegment word B c d k := by
  induction run with
  | nil c hc =>
    refine ⟨rfl, ?_⟩
    intro i hi x hx
    have : i = 0 := by omega
    subst i
    change some c = some x at hx
    cases hx
    exact ⟨input.1, input.2, fun t => windows t _ (hc t).1 (hc t).2⟩
  | @cons n c d e hc step tail ih =>
    have hd := registerStepInput step
    have rest := ih (by simpa only [hd] using input)
    have start : (machine source target op).Bounded word B c :=
      ⟨input.1, input.2, fun t => windows t _ (hc t).1 (hc t).2⟩
    have boundNext := rest.2 0 (Nat.zero_le _) d rfl
    have first := singleStepSegment step start boundNext
    simpa only [Nat.add_comm 1 n] using
      SearchTransducer.BoundedSegment.append (machine source target op) first rest

private theorem arithmeticStepFixed {tapes : ℕ} {bank : Fin tapes} {op : TapeArithmetic.Operation}
    {word : List Bool} {c d : TapeArithmetic.Config bank op}
    (step : (TapeArithmetic.machine bank op).step word c = some d) :
    d.inputHead = c.inputHead ∧ ∀ t, t ≠ bank → d.workHead t = c.workHead t := by
  refine step_fixed (fixedBank := fun t => t ≠ bank) ?_ step
  intro q inp reads r trans
  simp only [TapeArithmetic.machine] at trans
  split at trans
  · cases trans
    exact ⟨rfl, fun t ht => by change ((if t = bank then _ else _) : Action (Option Bool)).move = _; simp [ht]⟩
  · split at trans
    · split at trans <;> cases trans <;>
        exact ⟨rfl, fun t ht => by change ((if t = bank then _ else _) : Action (Option Bool)).move = _; simp [ht]⟩
    · split at trans
      · split at trans <;> cases trans <;>
          exact ⟨rfl, fun t ht => by change ((if t = bank then _ else _) : Action (Option Bool)).move = _; simp [ht]⟩
      · cases trans

/-- Convert the single-bank arithmetic run to the generic bounded segment.
The caller bounds its idle banks at the entry configuration. -/
theorem arithmeticBoundedSegment {tapes : ℕ} {bank : Fin tapes} {op : TapeArithmetic.Operation}
    {word : List Bool} {lo hi : Int} {B k : ℕ}
    {c d : TapeArithmetic.Config bank op} (run : TapeArithmetic.Runs word lo hi k c d)
    (input : (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (word.length : Int))
    (window : ∀ j, lo ≤ j → j ≤ hi → j.natAbs ≤ B)
    (idle : ∀ t, t ≠ bank → (c.workHead t).natAbs ≤ B) :
    (TapeArithmetic.machine bank op).BoundedSegment word B c d k := by
  induction run with
  | nil c hlo hhi =>
    refine ⟨rfl, ?_⟩
    intro i hi x hx
    have : i = 0 := by omega
    subst i
    change some c = some x at hx
    cases hx
    refine ⟨input.1, input.2, fun t => ?_⟩
    by_cases ht : t = bank
    · subst t
      exact window _ hlo hhi
    · exact idle t ht
  | @cons n c d e hlo hhi step tail ih =>
    obtain ⟨hInput, hFixed⟩ := arithmeticStepFixed step
    have rest := ih (by simpa only [hInput] using input) (fun t ht => by
      rw [hFixed t ht]
      exact idle t ht)
    have start : (TapeArithmetic.machine bank op).Bounded word B c := by
      refine ⟨input.1, input.2, fun t => ?_⟩
      by_cases ht : t = bank
      · subst t
        exact window _ hlo hhi
      · exact idle t ht
    have boundNext := rest.2 0 (Nat.zero_le _) d rfl
    have first := singleStepSegment step start boundNext
    simpa only [Nat.add_comm 1 n] using
      SearchTransducer.BoundedSegment.append (TapeArithmetic.machine bank op) first rest


private theorem abs_window {x : Int} {B : ℕ} (h : x.natAbs ≤ B) :
    -(B : Int) ≤ x ∧ x ≤ (B : Int) := by
  have upper := Int.le_natAbs (a := x)
  have lower := Int.le_natAbs (a := -x)
  rw [Int.natAbs_neg] at lower
  omega

private theorem peel {M : SearchTransducer} {word : List Bool} {B n : ℕ}
    {c d : M.Config} (run : M.BoundedSegment word B c d (n + 1)) :
    ∃ e, M.step word c = some e ∧ M.BoundedSegment word B e d n := by
  have full := run.1
  rw [show n + 1 = 1 + n by omega, SearchTransducer.runFrom_add] at full
  have one : M.runFrom word c 1 = M.step word c := rfl
  cases step : M.step word c with
  | none => simp [one, step] at full
  | some e =>
    have hOne : M.runFrom word c 1 = some e := one.trans step
    simp only [hOne, Option.bind_some] at full
    refine ⟨e, rfl, full, ?_⟩
    intro k hk x hx
    apply run.2 (1 + k) (by omega) x
    simpa only [SearchTransducer.runFrom_add, hOne, Option.bind_some] using hx

/-- Recover a physical paired-bank trace from the router's absolute bound. -/
theorem Runs.ofBoundedSegment {word : List Bool} {B k : ℕ}
    {c d : Config source target op}
    (run : (machine source target op).BoundedSegment word B c d k) :
    Runs word (fun _ => -(B : Int)) (fun _ => (B : Int)) k c d := by
  induction k generalizing c with
  | zero =>
    have hc : c = d := Option.some.inj run.1
    subst d
    exact .nil c (fun t => abs_window ((run.2 0 (by simp) c rfl).2.2 t))
  | succ n ih =>
    obtain ⟨e, step, tail⟩ := peel run
    exact .cons (fun t => abs_window ((run.2 0 (by simp) c rfl).2.2 t)) step (ih tail)

/-- Recover a physical arithmetic trace from the router's absolute bound. -/
theorem arithmeticRuns {tapes : ℕ} {bank : Fin tapes} {op : TapeArithmetic.Operation}
    {word : List Bool} {B k : ℕ} {c d : TapeArithmetic.Config bank op}
    (run : (TapeArithmetic.machine bank op).BoundedSegment word B c d k) :
    TapeArithmetic.Runs word (-(B : Int)) (B : Int) k c d := by
  induction k generalizing c with
  | zero =>
    have hc : c = d := Option.some.inj run.1
    subst d
    obtain ⟨lo, hi⟩ := abs_window ((run.2 0 (by simp) c rfl).2.2 bank)
    exact .nil c lo hi
  | succ n ih =>
    obtain ⟨e, step, tail⟩ := peel run
    obtain ⟨lo, hi⟩ := abs_window ((run.2 0 (by simp) c rfl).2.2 bank)
    exact .cons lo hi step (ih tail)

end Mathproof.MinimumGeneration.TapeRegisters
