import Mathproof.MinimumGenerationTableIO
import Mathlib.Data.Nat.Bits

namespace Mathproof.MinimumGeneration.InputScan

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open SearchTransducer

private def scan : Fin 3 := 0
private def carry : Fin 3 := 1
private def rewind : Fin 3 := 2

/-- Advance through the unary header, incrementing a growing binary counter.
Work cell zero is the permanent blank left marker. A blank to the right grows the counter. -/
def headerMachine : SearchTransducer where
  states := 3
  workTapes := 1
  initialState := scan
  transition q input read :=
    if q = scan then
      match input with
      | .data true => some (carry, .right, fun _ => ⟨none, .right⟩, none)
      | _ => none
    else if q = carry then
      match read 0 with
      | some true => some (carry, .stay, fun _ => ⟨some (some false), .right⟩, none)
      | _ => some (rewind, .stay, fun _ => ⟨some (some true), .left⟩, none)
    else
      match read 0 with
      | none => some (scan, .stay, fun _ => ⟨none, .stay⟩, none)
      | some _ => some (rewind, .stay, fun _ => ⟨none, .left⟩, none)

/-- Increment a little-endian representation, allocating one cell on overflow. -/
def increment : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: increment rest

def value : List Bool → Nat
  | [] => 0
  | b :: rest => Nat.bit b (value rest)

theorem value_increment (xs : List Bool) : value (increment xs) = value xs + 1 := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    cases b
    · simp [increment, value, Nat.bit]
    · simp [increment, value, Nat.bit, ih]
      omega

theorem increment_nonempty (xs : List Bool) : (increment xs).length > 0 := by
  cases xs with
  | nil => decide
  | cons b xs => cases b <;> simp [increment]

/-- The code invariant allows the empty counter for zero. -/
def Canonical : List Bool → Prop
  | [] => True
  | b :: [] => b = true
  | _ :: b :: rest => Canonical (b :: rest)

theorem canonical_increment {xs : List Bool} (h : Canonical xs) : Canonical (increment xs) := by
  induction xs with
  | nil => simp [increment, Canonical]
  | cons b xs ih =>
    cases xs with
    | nil => cases b <;> simp [increment, Canonical]
    | cons d rest =>
      cases b with
      | false => exact h
      | true =>
        cases d with
        | false => simpa [increment, Canonical] using ih (by simpa [Canonical] using h)
        | true => simpa [increment, Canonical] using ih (by simpa [Canonical] using h)

def counterBits : Nat → List Bool
  | 0 => []
  | k + 1 => increment (counterBits k)

theorem canonical_counterBits (k : Nat) : Canonical (counterBits k) := by
  induction k with
  | zero => trivial
  | succ k ih => exact canonical_increment ih

@[simp] theorem value_counterBits (k : Nat) : value (counterBits k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [counterBits, value_increment, ih]

theorem value_lt_pow (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    cases b <;> simp [value, Nat.bit, Nat.pow_succ] <;> omega

theorem pow_le_value {xs : List Bool} (h : Canonical xs) (hne : xs ≠ []) :
    2 ^ (xs.length - 1) ≤ value xs := by
  induction xs with
  | nil => contradiction
  | cons b xs ih =>
    cases xs with
    | nil =>
      have hb : b = true := h
      subst b
      decide
    | cons d rest =>
      have hh : Canonical (d :: rest) := h
      have hi := ih hh (by simp)
      have he : (b :: d :: rest).length - 1 = ((d :: rest).length - 1) + 1 := by simp
      rw [he, Nat.pow_succ]
      cases b <;> simp [value, Nat.bit] at * <;> omega

theorem counterBits_length (k : Nat) (hk : k ≠ 0) : (counterBits k).length = Nat.log2 k + 1 := by
  have hne : counterBits k ≠ [] := by
    intro h
    apply hk
    rw [← value_counterBits k, h]
    rfl
  have hpos : 0 < (counterBits k).length := List.length_pos_of_ne_nil hne
  have hlo := pow_le_value (canonical_counterBits k) hne
  have hhi := value_lt_pow (counterBits k)
  rw [value_counterBits] at hlo hhi
  have he : Nat.log2 k = (counterBits k).length - 1 := by
    apply (Nat.log2_eq_iff hk).2
    exact ⟨hlo, by rwa [Nat.sub_add_cancel (by omega)]⟩
  omega

theorem bit_at_value (xs : List Bool) (j : Nat) (hj : j < xs.length) :
    xs[j]? = some (Nat.testBit (value xs) j) := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons b ys ih =>
    cases j with
    | zero =>
      change some b = some (Nat.bodd (Nat.bit b (value ys)))
      rw [Nat.bodd_bit]
    | succ j =>
      simpa only [value, List.getElem?_cons_succ, Nat.testBit_bit_succ] using ih j (by simpa using hj)

theorem counterBits_eq_encodeLabel (n : Nat) (hn : n ≠ 0) :
    counterBits n = encodeLabel (Nat.log2 n + 1) n := by
  have hlen := counterBits_length n hn
  apply List.ext_getElem?
  intro j
  by_cases hj : j < Nat.log2 n + 1
  · have hbit := bit_at_value (counterBits n) j (by rwa [hlen])
    rw [value_counterBits] at hbit
    rw [hbit]
    simp [encodeLabel, List.getElem?_eq_getElem (by simpa using hj : j < (List.range (Nat.log2 n + 1)).length)]
  · have h₁ : (counterBits n).length ≤ j := by rw [hlen]; omega
    have h₂ : (encodeLabel (Nat.log2 n + 1) n).length ≤ j := by simp [encodeLabel]; omega
    rw [List.getElem?_eq_none h₁, List.getElem?_eq_none h₂]
theorem counterBits_length_le (k n : Nat) (hk : k ≤ n) :
    (counterBits k).length ≤ Nat.log2 n + 1 := by
  by_cases h : k = 0
  · subst k; simp [counterBits]
  · rw [counterBits_length k h]
    have hh := (Nat.log2_self_le h).trans hk
    have hn : n ≠ 0 := by omega
    exact Nat.add_le_add_right ((Nat.le_log2 hn).2 hh) 1

/-- A verified small-step segment, with bounds checked at every configuration. -/
def Safe (word : List Bool) (cap : Nat) (c : headerMachine.Config) : Prop :=
  0 ≤ c.inputHead ∧ c.inputHead ≤ word.length ∧
    0 ≤ c.workHead (0 : Fin 1) ∧ c.workHead (0 : Fin 1) ≤ cap

inductive SafeRun (word : List Bool) (cap : Nat) :
    Nat → headerMachine.Config → headerMachine.Config → Prop
  | refl {c} : Safe word cap c → SafeRun word cap 0 c c
  | cons {k c d e} : Safe word cap c → headerMachine.step word c = some d →
      SafeRun word cap k d e → SafeRun word cap (k + 1) c e

namespace SafeRun

theorem trans {word cap k m c d e} (h₁ : SafeRun word cap k c d)
    (h₂ : SafeRun word cap m d e) : SafeRun word cap (k + m) c e := by
  induction h₁ with
  | refl => simpa using h₂
  | @cons k c a d hsafe hstep hpath ih =>
    have hh := SafeRun.cons hsafe hstep (ih h₂)
    simpa only [Nat.add_right_comm] using hh

theorem singleton {word cap c d} (hc : Safe word cap c)
    (hs : headerMachine.step word c = some d) (hd : Safe word cap d) :
    SafeRun word cap 1 c d :=
  .cons hc hs (.refl hd)

end SafeRun


/-- Preserve a left blank marker, followed by the zeros already written by a carry
and then the unprocessed suffix. -/
def counterTape (written : Nat) (suffix : List Bool) (i : Int) : Option Bool :=
  if i ≤ 0 then none else if i ≤ (written : Int) then some false
  else suffix[(i - (written : Int) - 1).toNat]?

def putBit (f : Int → Option Bool) (i : Int) (b : Bool) : Int → Option Bool :=
  fun j => if j = i then some b else f j

@[simp] theorem counterTape_zero (k : Nat) (xs : List Bool) :
    counterTape k xs 0 = none := by simp [counterTape]

@[simp] theorem counterTape_first (k : Nat) (xs : List Bool) :
    counterTape k xs (((k + 1 : Nat) : Int)) = xs[0]? := by
  have hpos : ¬ (((k + 1 : Nat) : Int) ≤ 0) := by omega
  have hnext : ¬ (((k + 1 : Nat) : Int) ≤ (k : Int)) := by omega
  have he : (((k + 1 : Nat) : Int) - (k : Int) - 1).toNat = 0 := by omega
  simp only [counterTape, if_neg hpos, if_neg hnext, he]

theorem counterTape_advance (k : Nat) (xs : List Bool) :
    counterTape k (false :: xs) = counterTape (k + 1) xs := by
  funext i
  by_cases h₀ : i ≤ 0
  · simp [counterTape, h₀]
  by_cases hk : i ≤ (k : Int)
  · have hkk : i ≤ ((k + 1 : Nat) : Int) := by omega
    simp only [counterTape, if_neg h₀, if_pos hk, if_pos hkk]
  by_cases he : i = ((k + 1 : Nat) : Int)
  · subst i
    rw [counterTape_first]
    have hpos : ¬ (((k + 1 : Nat) : Int) ≤ 0) := by omega
    simp only [counterTape, if_neg hpos, if_pos (le_refl _), List.getElem?_cons_zero]
  · have hn : ¬ i ≤ ((k + 1 : Nat) : Int) := by omega
    have hs : (i - (k : Int) - 1).toNat = (i - ((k + 1 : Nat) : Int) - 1).toNat + 1 := by
      omega
    simp only [counterTape, if_neg h₀, if_neg hk, if_neg hn, hs, List.getElem?_cons_succ]

theorem counterTape_write_cons (k : Nat) (a b : Bool) (xs : List Bool) :
    putBit (counterTape k (a :: xs)) (((k + 1 : Nat) : Int)) b = counterTape k (b :: xs) := by
  funext i
  by_cases he : i = ((k + 1 : Nat) : Int)
  · subst i
    rw [counterTape_first]; simp [putBit]
  · unfold putBit
    rw [if_neg he]
    by_cases h₀ : i ≤ 0
    · simp [counterTape, h₀]
    by_cases hk : i ≤ (k : Int)
    · simp [counterTape, h₀, hk]
    have hi : (i - (k : Int) - 1).toNat ≠ 0 := by omega
    simp only [counterTape, if_neg h₀, if_neg hk, List.getElem?_cons, if_neg hi]

theorem counterTape_write_nil (k : Nat) (b : Bool) :
    putBit (counterTape k []) (((k + 1 : Nat) : Int)) b = counterTape k [b] := by
  funext i
  by_cases he : i = ((k + 1 : Nat) : Int)
  · subst i
    rw [counterTape_first]; simp [putBit]
  · unfold putBit
    rw [if_neg he]
    by_cases h₀ : i ≤ 0
    · simp [counterTape, h₀]
    by_cases hk : i ≤ (k : Int)
    · simp [counterTape, h₀, hk]
    have hi : (i - (k : Int) - 1).toNat ≠ 0 := by omega
    simp only [counterTape, if_neg h₀, if_neg hk, List.getElem?_cons, if_neg hi, List.getElem?_nil]

theorem counterTape_filled (k : Nat) (xs : List Bool) (j : Nat)
    (hp : 0 < j) (hj : j ≤ k + xs.length) :
    ∃ b : Bool, counterTape k xs j = some b := by
  have h₀ : ¬ (j : Int) ≤ 0 := by omega
  by_cases h : j ≤ k
  · exact ⟨false, by simp [counterTape, Nat.ne_of_gt hp, h]⟩
  · have hk : ¬ (j : Int) ≤ (k : Int) := by omega
    let i := ((j : Int) - (k : Int) - 1).toNat
    have hi : i < xs.length := by dsimp [i]; omega
    exact ⟨xs[i], by simpa only [counterTape, if_neg h₀, if_neg hk] using List.getElem?_eq_getElem hi⟩

private def cfg (q : Fin 3) (input work : Nat) (tape : Int → Option Bool) :
    headerMachine.Config :=
  ⟨q, input, fun _ => work, fun _ => tape, []⟩

private theorem cfg_safe {w cap q input work tape} (hi : input ≤ (w : List Bool).length)
    (hw : work ≤ cap) : Safe w cap (cfg q input work tape) := by
  simp [Safe, cfg, hi, hw]

private theorem step_scan_true (w : List Bool) (p : Nat) (t : Int → Option Bool)
    (h : readInput w (p : Int) = .data true) :
    headerMachine.step w (cfg scan p 0 t) = some (cfg carry (p + 1) 1 t) := by
  simp [SearchTransducer.step, headerMachine, cfg, h, moveOffset]
  funext i j
  exact ite_self _

private theorem step_scan_false (w : List Bool) (p : Nat) (t : Int → Option Bool)
    (h : readInput w (p : Int) = .data false) :
    headerMachine.step w (cfg scan p 0 t) = none := by
  simp [SearchTransducer.step, headerMachine, cfg, h]

private theorem step_carry_true (w : List Bool) (p k : Nat) (xs : List Bool) :
    headerMachine.step w (cfg carry p (k + 1) (counterTape k (true :: xs))) =
      some (cfg carry p (k + 2) (counterTape (k + 1) xs)) := by
  have hcs : carry ≠ scan := by decide
  have hread : counterTape k (true :: xs) ((k : Int) + 1) = some true := by
    simpa using counterTape_first k (true :: xs)
  simp [SearchTransducer.step, headerMachine, cfg, hcs, hread, moveOffset, ← counterTape_advance]
  refine ⟨funext (fun _ => by omega), ?_⟩
  exact congrArg (fun (f : Int → Option Bool) => fun _ : Fin 1 => f)
    (counterTape_write_cons k true false xs)

private theorem step_carry_false (w : List Bool) (p k : Nat) (xs : List Bool) :
    headerMachine.step w (cfg carry p (k + 1) (counterTape k (false :: xs))) =
      some (cfg rewind p k (counterTape k (true :: xs))) := by
  have hcs : carry ≠ scan := by decide
  have hread : counterTape k (false :: xs) ((k : Int) + 1) = some false := by
    simpa using counterTape_first k (false :: xs)
  simp [SearchTransducer.step, headerMachine, cfg, hcs, hread, moveOffset]
  exact congrArg (fun (f : Int → Option Bool) => fun _ : Fin 1 => f)
    (counterTape_write_cons k false true xs)

private theorem step_carry_nil (w : List Bool) (p k : Nat) :
    headerMachine.step w (cfg carry p (k + 1) (counterTape k [])) =
      some (cfg rewind p k (counterTape k [true])) := by
  have hcs : carry ≠ scan := by decide
  have hread : counterTape k [] ((k : Int) + 1) = none := by
    simpa using counterTape_first k []
  simp [SearchTransducer.step, headerMachine, cfg, hcs, hread, moveOffset]
  exact congrArg (fun (f : Int → Option Bool) => fun _ : Fin 1 => f)
    (counterTape_write_nil k true)

private theorem step_rewind_succ (w : List Bool) (p j : Nat) (t : Int → Option Bool) (b : Bool)
    (h : t (((j + 1 : Nat) : Int)) = some b) :
    headerMachine.step w (cfg rewind p (j + 1) t) = some (cfg rewind p j t) := by
  have hrs : rewind ≠ scan := by decide
  have hrc : rewind ≠ carry := by decide
  simp [SearchTransducer.step, headerMachine, cfg, hrs, hrc, (show t (↑j + 1) = some b by simpa using h), moveOffset]
  funext i j
  exact ite_self _

private theorem step_rewind_zero (w : List Bool) (p : Nat) (t : Int → Option Bool)
    (h : t 0 = none) :
    headerMachine.step w (cfg rewind p 0 t) = some (cfg scan p 0 t) := by
  have hrs : rewind ≠ scan := by decide
  have hrc : rewind ≠ carry := by decide
  simp [SearchTransducer.step, headerMachine, cfg, hrs, hrc, h, moveOffset]
  funext i j
  exact ite_self _


private theorem carry_correct (word : List Bool) (cap input written : Nat) (xs : List Bool)
    (hi : input ≤ word.length) (hw : written + (increment xs).length ≤ cap) :
    ∃ ticks head, head ≤ written + (increment xs).length ∧
      SafeRun word cap ticks
        (cfg carry input (written + 1) (counterTape written xs))
        (cfg rewind input head (counterTape written (increment xs))) := by
  induction xs generalizing written with
  | nil =>
    have hw' : written + 1 ≤ cap := by simpa [increment] using hw
    exact ⟨1, written, by simp [increment],
      SafeRun.singleton (cfg_safe hi hw') (step_carry_nil word input written)
        (cfg_safe hi (by omega))⟩
  | cons b xs ih =>
    cases b with
    | false =>
      have hw' : written + 1 ≤ cap := by simp [increment] at hw; omega
      exact ⟨1, written, by simp [increment],
        SafeRun.singleton (cfg_safe hi hw') (step_carry_false word input written xs)
          (cfg_safe hi (by omega))⟩
    | true =>
      have hsize : written + (increment (true :: xs)).length =
          (written + 1) + (increment xs).length := by
        simp [increment]; omega
      obtain ⟨ticks, head, hhead, hrun⟩ := ih (written + 1) (by rwa [hsize] at hw)
      refine ⟨ticks + 1, head, hhead.trans_eq hsize.symm, ?_⟩
      have hstart : written + 1 ≤ cap := by omega
      refine SafeRun.cons (cfg_safe hi hstart) (step_carry_true word input written xs) ?_
      rw [increment, counterTape_advance]
      exact hrun

private theorem rewind_correct (word : List Bool) (cap input written head : Nat)
    (xs : List Bool) (hi : input ≤ word.length) (hw : written + xs.length ≤ cap)
    (hj : head ≤ written + xs.length) :
    SafeRun word cap (head + 1) (cfg rewind input head (counterTape written xs))
      (cfg scan input 0 (counterTape written xs)) := by
  induction head with
  | zero =>
    exact SafeRun.singleton (cfg_safe hi (Nat.zero_le cap))
      (step_rewind_zero word input _ (counterTape_zero written xs))
      (cfg_safe hi (Nat.zero_le cap))
  | succ head ih =>
    obtain ⟨b, hb⟩ := counterTape_filled written xs (head + 1) (by omega) hj
    exact SafeRun.cons (cfg_safe hi (hj.trans hw)) (step_rewind_succ word input head _ b hb)
      (ih (by omega))

/-- The fixed input format needed by the header phase. -/
def headed (n : Nat) (body : List Bool) : List Bool :=
  List.replicate n true ++ false :: body

theorem read_headed_true (n p : Nat) (body : List Bool) (hp : p < n) :
    readInput (headed n body) (p : Int) = .data true := by
  have hn : ¬ (p : Int) < 0 := by omega
  have hh : p < (List.replicate n true).length := by simpa using hp
  simp [readInput, headed, hn, List.getElem?_append_left hh, List.getElem?_replicate_of_lt hp]

theorem read_headed_false (n : Nat) (body : List Bool) :
    readInput (headed n body) (n : Int) = .data false := by
  have hn : ¬ (n : Int) < 0 := by omega
  simp [readInput, headed, hn]

/-- At the phase boundary the input head is at position k and the counter
head is back on its left marker. -/
def scanned (k : Nat) : headerMachine.Config :=
  cfg scan k 0 (counterTape 0 (counterBits k))

theorem scanned_zero : scanned 0 = headerMachine.initial := by
  have ht : counterTape 0 [] = fun _ => none := by
    funext i
    simp [counterTape]
  simp [scanned, cfg, counterBits, ht, initial, headerMachine]

theorem scan_prefix (n t : Nat) (body : List Bool) (ht : t ≤ n) :
    ∃ ticks, SafeRun (headed n body) (Nat.log2 n + 1) ticks headerMachine.initial (scanned t) := by
  induction t with
  | zero =>
    refine ⟨0, ?_⟩
    rw [← scanned_zero]
    exact .refl (cfg_safe (by simp) (by simp))
  | succ t ih =>
    obtain ⟨prev, hprev⟩ := ih (by omega)
    have hip : t + 1 ≤ (headed n body).length := by
      simp [headed]
      omega
    have hw := counterBits_length_le (t + 1) n ht
    change (increment (counterBits t)).length ≤ _ at hw
    have hcap : 0 + (increment (counterBits t)).length ≤ Nat.log2 n + 1 := by simpa using hw
    obtain ⟨ticks, r, hr, hcarry⟩ :=
      carry_correct (headed n body) (Nat.log2 n + 1) (t + 1) 0 (counterBits t) hip hcap
    have hrewind :=
      rewind_correct (headed n body) (Nat.log2 n + 1) (t + 1) 0 r (increment (counterBits t)) hip hcap hr
    have hrun : SafeRun (headed n body) (Nat.log2 n + 1) (ticks + (r + 1) + 1)
        (scanned t) (scanned (t + 1)) := by
      apply SafeRun.cons (cfg_safe (by omega) (by simp))
        (step_scan_true (headed n body) t _ (read_headed_true n t body (by omega)))
      exact hcarry.trans hrewind
    exact ⟨_, hprev.trans hrun⟩

private def executeFrom (word : List Bool) : Nat → headerMachine.Config → Option headerMachine.Config
  | 0, c => some c
  | k + 1, c => (headerMachine.step word c).bind (executeFrom word k)

private theorem execute_succ_end (word : List Bool) (t : Nat) (c : headerMachine.Config) :
    executeFrom word (t + 1) c = (executeFrom word t c).bind (headerMachine.step word) := by
  induction t generalizing c with
  | zero => cases he : headerMachine.step word c <;> simp [executeFrom, he]
  | succ t ih =>
    simp only [executeFrom]
    cases he : headerMachine.step word c with
    | none => simp
    | some d => exact ih d

private theorem after_execute (word : List Bool) (t : Nat) :
    headerMachine.after word t = executeFrom word t headerMachine.initial := by
  induction t with
  | zero => rfl
  | succ t ih => rw [after, ih, execute_succ_end]

private theorem SafeRun.execute_eq {word cap ticks c d} (h : SafeRun word cap ticks c d) :
    executeFrom word ticks c = some d := by
  induction h with
  | refl => rfl
  | cons _ hstep _ ih => simp [executeFrom, hstep, ih]

private theorem SafeRun.safe_until_halt {word cap ticks c d} (h : SafeRun word cap ticks c d)
    (hhalt : headerMachine.step word d = none) {j} {e : headerMachine.Config}
    (he : executeFrom word j c = some e) : Safe word cap e := by
  induction h generalizing j e with
  | refl hs =>
    cases j with
    | zero =>
      have hce := Option.some.inj he
      simpa [← hce] using hs
    | succ j => simp [executeFrom, hhalt] at he
  | cons hs hstep _ ih =>
    cases j with
    | zero =>
      have hce := Option.some.inj he
      simpa [← hce] using hs
    | succ j =>
      apply ih hhalt
      simpa [executeFrom, hstep] using he

/-- The physical header machine halts on the delimiter and stores the exact
order in its growing binary counter, with logarithmic workspace. -/
theorem headerMachine_correct (n : Nat) (body : List Bool) :
    (∃ ticks, headerMachine.after (headed n body) ticks = some (scanned n)) ∧
      headerMachine.step (headed n body) (scanned n) = none ∧
      headerMachine.logarithmicWorkspace 1 (headed n body) := by
  obtain ⟨ticks, hr⟩ := scan_prefix n n body le_rfl
  have hhalt := step_scan_false (headed n body) n (counterTape 0 (counterBits n))
    (read_headed_false n body)
  refine ⟨⟨ticks, (after_execute _ _).trans (SafeRun.execute_eq hr)⟩, hhalt, ?_⟩
  intro j e he
  rw [after_execute] at he
  obtain ⟨hin, hi, hwh, hw⟩ := SafeRun.safe_until_halt hr hhalt he
  refine ⟨by omega, hi, fun i => ?_⟩
  change Fin 1 at i
  have i0 : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  have hn : n ≤ (headed n body).length + 1 := by simp [headed]; omega
  have hlo : Nat.log2 n ≤ Nat.log2 ((headed n body).length + 1) := by
    by_cases hz : n = 0
    · simp [hz]
    · exact (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le hz).trans hn)
  simp only [Nat.one_mul]
  omega

theorem headed_encodeCayley (n : Nat) [Mul (Fin n)] :
    ∃ body, encodeCayley n = headed n body := by
  refine ⟨(List.finRange n).flatMap (fun x =>
    (List.finRange n).flatMap (fun y => encodeLabel (Nat.log2 n + 1) (x * y).val)), ?_⟩
  unfold encodeCayley headed
  rw [List.append_assoc]
  rfl

theorem headerMachine_cayley (n : Nat) [Mul (Fin n)] :
    (∃ ticks, headerMachine.after (encodeCayley n) ticks = some (scanned n)) ∧
      headerMachine.step (encodeCayley n) (scanned n) = none ∧
      headerMachine.logarithmicWorkspace 1 (encodeCayley n) := by
  obtain ⟨body, hb⟩ := headed_encodeCayley n
  rw [hb]
  exact headerMachine_correct n body


/-- Return the read-only input head to position zero while preserving every caller
work tape, work head, and emitted bit. -/
def rewindInput (tapes : Nat) : SearchTransducer where
  states := 2
  workTapes := tapes
  initialState := 0
  transition q input _ :=
    if q = 0 then
      match input with
      | .leftEnd => some (1, .right, fun _ => ⟨none, .stay⟩, none)
      | _ => some (0, .left, fun _ => ⟨none, .stay⟩, none)
    else none

def rewindInputConfig (tapes : Nat) (q : Fin 2) (p : Int)
    (head : Fin tapes → Int) (cell : Fin tapes → Int → Option Bool)
    (prior : List Bool) : (rewindInput tapes).Config :=
  ⟨q, p, head, cell, prior⟩

private theorem rewindInput_move (tapes : Nat) (word : List Bool) (p : Int)
    (hp : 0 ≤ p) (head : Fin tapes → Int) (cell : Fin tapes → Int → Option Bool)
    (prior : List Bool) :
    (rewindInput tapes).step word (rewindInputConfig tapes 0 p head cell prior) =
      some (rewindInputConfig tapes 0 (p - 1) head cell prior) := by
  cases hread : word[p.toNat]? <;>
    simp [SearchTransducer.step, rewindInput, rewindInputConfig, readInput,
      Int.not_lt.mpr hp, hread, moveOffset, sub_eq_add_neg]
  all_goals
    funext i j
    exact ite_self _

private theorem rewindInput_return (tapes : Nat) (word : List Bool)
    (head : Fin tapes → Int) (cell : Fin tapes → Int → Option Bool) (prior : List Bool) :
    (rewindInput tapes).step word (rewindInputConfig tapes 0 (-1) head cell prior) =
      some (rewindInputConfig tapes 1 0 head cell prior) := by
  simp [SearchTransducer.step, rewindInput, rewindInputConfig, readInput, moveOffset]
  funext i j
  exact ite_self _

theorem rewindInput_prefix (tapes : Nat) (word : List Bool) (p k : Nat)
    (hk : k ≤ p + 1) (head : Fin tapes → Int) (cell : Fin tapes → Int → Option Bool)
    (prior : List Bool) :
    TableIO.afterFrom (rewindInput tapes) word (rewindInputConfig tapes 0 p head cell prior) k =
      some (rewindInputConfig tapes 0 ((p : Int) - k) head cell prior) := by
  induction k with
  | zero => simp [TableIO.afterFrom]
  | succ k ih =>
    rw [TableIO.afterFrom, ih (by omega)]
    have hm := rewindInput_move tapes word ((p : Int) - k) (by omega) head cell prior
    rw [Option.bind_some, hm]
    congr 2
    omega

theorem rewindInput_correct (tapes : Nat) (word : List Bool) (p : Nat)
    (head : Fin tapes → Int) (cell : Fin tapes → Int → Option Bool) (prior : List Bool) :
    TableIO.afterFrom (rewindInput tapes) word (rewindInputConfig tapes 0 p head cell prior)
        (p + 2) = some (rewindInputConfig tapes 1 0 head cell prior) ∧
      (rewindInput tapes).step word (rewindInputConfig tapes 1 0 head cell prior) = none := by
  constructor
  · rw [show p + 2 = (p + 1) + 1 by omega, TableIO.afterFrom,
        rewindInput_prefix tapes word p (p + 1) le_rfl head cell prior]
    simpa using rewindInput_return tapes word head cell prior
  · simp [SearchTransducer.step, rewindInput, rewindInputConfig]

/-- Any reachable rewind configuration stays between the starting head position
and the left endmarker, with unchanged work tapes and output. -/
theorem rewindInput_bounds (tapes : Nat) (word : List Bool) (p k : Nat)
    (head : Fin tapes → Int) (cell : Fin tapes → Int → Option Bool) (prior : List Bool)
    (c : (rewindInput tapes).Config)
    (hc : TableIO.afterFrom (rewindInput tapes) word (rewindInputConfig tapes 0 p head cell prior) k =
      some c) :
    (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ p ∧
      c.workHead = head ∧ c.workCell = cell ∧ c.outputReversed = prior := by
  by_cases hk : k ≤ p + 1
  · rw [rewindInput_prefix tapes word p k hk head cell prior] at hc
    cases hc
    exact ⟨by change (-1 : Int) ≤ (p : Int) - k; omega,
      by change (p : Int) - k ≤ (p : Int); omega, rfl, rfl, rfl⟩
  have hcorrect := rewindInput_correct tapes word p head cell prior
  have hnone (j : Nat) :
      TableIO.afterFrom (rewindInput tapes) word (rewindInputConfig tapes 0 p head cell prior)
        ((p + 2) + (j + 1)) = none := by
    induction j with
    | zero =>
      rw [TableIO.afterFrom, hcorrect.1]
      simpa using hcorrect.2
    | succ j ih =>
      rw [show (p + 2) + (j + 1 + 1) = ((p + 2) + (j + 1)) + 1 by omega,
        TableIO.afterFrom, ih]
      rfl
  have hk' : k = p + 2 ∨ ∃ j, k = (p + 2) + (j + 1) := by
    by_cases he : k = p + 2
    · exact Or.inl he
    · exact Or.inr ⟨k - (p + 3), by omega⟩
  rcases hk' with he | ⟨j, he⟩
  · rw [he, hcorrect.1] at hc
    cases hc
    exact ⟨by change (-1 : Int) ≤ 0; decide, by change (0 : Int) ≤ (p : Int); omega, rfl, rfl, rfl⟩
  · rw [he, hnone j] at hc
    contradiction
end Mathproof.MinimumGeneration.InputScan
