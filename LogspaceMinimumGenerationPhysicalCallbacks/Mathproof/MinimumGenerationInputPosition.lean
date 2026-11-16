import Mathproof.MinimumGenerationTableIO
import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

namespace Mathproof.MinimumGeneration.InputPosition

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open Mathproof.MinimumGeneration.TableIO (afterFrom)

/-- A scratch address is stored least significant bit first between two blanks.
A borrow sweep consumes one unit and advances the read-only input one cell.
When the sweep underflows, the input is already at the requested position. -/
def skip : SearchTransducer where
  states := 10
  workTapes := 1
  initialState := 0
  transition s input cells :=
    let go := fun (q : Fin 10) (i w : Move) (b : Option (Option Bool)) =>
      some (q, i, (fun _ : Fin 1 => ⟨b, w⟩), none)
    match s.val with
    | 0 => go 1 .stay .right none
    | 1 => match cells 0 with
      | some false => go 1 .stay .right (some (some true))
      | some true => go 2 .stay .right (some (some false))
      | none => go 4 .stay .left none
    | 2 => match cells 0 with
      | some _ => go 2 .stay .right none
      | none => go 3 .right .left none
    | 3 => match cells 0 with
      | some _ => go 3 .stay .left none
      | none => go 0 .stay .stay none
    | 4 => match cells 0 with
      | some _ => go 4 .stay .left none
      | none => go 5 .stay .stay none
    | 6 => go 7 .stay .right none
    | 7 => match cells 0, input with
      | none, _ => go 8 .stay .left none
      | some _, .data bit => go 7 .right .right (some (some bit))
      | some _, _ => none
    | 8 => match cells 0 with
      | some _ => go 8 .stay .left none
      | none => go 9 .stay .stay none
    | _ => none

def digits (bits : List Bool) : ℕ :=
  bits.foldr (fun b z => Nat.bit b z) 0

def work (bits : List Bool) (p : Int) : Option Bool :=
  if p ≤ 0 then none else bits[(p - 1).toNat]?

def cfg (bits : List Bool) (q : Fin 10) (a : ℕ) (p : ℕ) (out : List Bool) :
    skip.Config :=
  ⟨q, a, fun _ => p, fun _ => work bits, out⟩

@[simp] private theorem read_origin (b : List Bool) : work b 0 = none := by
  simp [work]

@[simp] private theorem read_cell (b : List Bool) (i : ℕ) :
    work b ((i : Int) + 1) = b[i]? := by
  simp [work, show ¬ ((i : Int) + 1 ≤ 0) by omega]

private theorem step_start (word b : List Bool) (a : ℕ) (out : List Bool) :
    skip.step word (cfg b 0 a 0 out) = some (cfg b 1 a 1 out) := by
  simp [SearchTransducer.step, skip, cfg, moveOffset]
  funext i j
  exact ite_self _

private theorem work_update (b : List Bool) (i : ℕ) (bit : Bool) (hi : i < b.length) :
    (fun p : Int => if p = (↑(i + 1) : Int) then some bit else work b p) =
      work (b.set i bit) := by
  funext p
  by_cases hp : p ≤ 0
  · rw [if_neg (by omega)]
    simp only [work, if_pos hp]
  · have he : p = (↑(i + 1) : Int) ↔ (p - 1).toNat = i := by omega
    simp only [work, if_neg hp, List.getElem?_set, he]
    by_cases h : (p - 1).toNat = i
    · simp [h, hi]
    · rw [if_neg h]
      simp only [ne_comm.mp h, if_false]

private def sweepState (borrow : Bool) : Fin 10 := if borrow then 1 else 2
private def rewindState (borrow : Bool) : Fin 10 := if borrow then 4 else 3
private def nextBit (borrow b : Bool) : Bool := b ^^ borrow
private def carryBit (borrow b : Bool) : Bool := borrow && !b

private theorem set_append_cons (pre : List Bool) (b bit : Bool) (bs : List Bool) :
    (pre ++ b :: bs).set pre.length bit = pre ++ bit :: bs := by
  induction pre with
  | nil => rfl
  | cons p pre ih => simp [ih]

private theorem step_sweep (word pre bs : List Bool) (b borrow : Bool)
    (a : ℕ) (out : List Bool) :
    skip.step word (cfg (pre ++ b :: bs) (sweepState borrow) a (pre.length + 1) out) =
      some (cfg (pre ++ nextBit borrow b :: bs) (sweepState (carryBit borrow b))
        a (pre.length + 2) out) := by
  have hr : work (pre ++ b :: bs) ((pre.length : Int) + 1) = some b := by
    rw [read_cell, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hu1 := work_update (pre ++ b :: bs) pre.length true (by simp)
  have hu0 := work_update (pre ++ b :: bs) pre.length false (by simp)
  rw [set_append_cons] at hu1 hu0
  have h1 : (fun (_ : Fin 1) (p : Int) => if p = (pre.length : Int) + 1 then some true else work (pre ++ b :: bs) p) =
      (fun _ => work (pre ++ true :: bs)) := funext (fun _ => hu1)
  have h0 : (fun (_ : Fin 1) (p : Int) => if p = (pre.length : Int) + 1 then some false else work (pre ++ b :: bs) p) =
      (fun _ => work (pre ++ false :: bs)) := funext (fun _ => hu0)
  cases borrow <;> cases b <;>
    simp only [SearchTransducer.step, skip, cfg, sweepState, carryBit, nextBit,
      Bool.false_eq_true, if_false, if_true, Fin.val_one, Fin.val_two, hr, moveOffset,
      Option.map_some, Option.getD_none, Option.getD_some, Option.elim, Int.add_zero,
      Int.natCast_succ, ite_self, Bool.true_and, Bool.not_true, Bool.not_false, Bool.xor_true] <;>
    first | rfl | rw [h1] | rw [h0]

private theorem step_turn (word b : List Bool) (borrow : Bool) (a : ℕ) (out : List Bool) :
    skip.step word (cfg b (sweepState borrow) a (b.length + 1) out) =
      some (cfg b (rewindState borrow) (if borrow then a else a + 1) b.length out) := by
  have hr : work b ((b.length : Int) + 1) = none := by
    rw [read_cell, List.getElem?_eq_none (Nat.le_refl _)]
  cases borrow <;> simp [SearchTransducer.step, skip, cfg, sweepState, rewindState,
    hr, moveOffset]

private theorem step_rewind (word b : List Bool) (borrow : Bool) (a i : ℕ)
    (out : List Bool) (hi : i < b.length) :
    skip.step word (cfg b (rewindState borrow) a (i + 1) out) =
      some (cfg b (rewindState borrow) a i out) := by
  have hr : work b ((i : Int) + 1) = some b[i] := by
    rw [read_cell, List.getElem?_eq_getElem hi]
  cases borrow <;> simp [SearchTransducer.step, skip, cfg, rewindState,
    hr, moveOffset]

private theorem step_finish (word b : List Bool) (borrow : Bool) (a : ℕ) (out : List Bool) :
    skip.step word (cfg b (rewindState borrow) a 0 out) =
      some (cfg b (if borrow then 5 else 0) a 0 out) := by
  cases borrow <;> simp [SearchTransducer.step, skip, cfg, rewindState, moveOffset, ite_self]

private theorem step_halt (word b : List Bool) (a : ℕ) (out : List Bool) :
    skip.step word (cfg b 5 a 0 out) = none := rfl

private def borrowWord : Bool → List Bool → Bool × List Bool
  | c, [] => (c, [])
  | c, b :: bs =>
    let tail := borrowWord (carryBit c b) bs
    (tail.1, nextBit c b :: tail.2)

private theorem borrowWord_length (c : Bool) (bs : List Bool) :
    (borrowWord c bs).2.length = bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [borrowWord, ih]

private theorem digits_lt (bs : List Bool) : digits bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    change Nat.bit b (digits bs) < 2 ^ (bs.length + 1)
    rw [Nat.pow_succ, Nat.bit_val]
    cases b <;> simp <;> omega

private theorem borrowWord_value (c : Bool) (bs : List Bool) :
    digits (borrowWord c bs).2 + c.toNat = digits bs +
      (borrowWord c bs).1.toNat * 2 ^ bs.length := by
  induction bs generalizing c with
  | nil => simp [borrowWord, digits]
  | cons b bs ih =>
    have h := ih (carryBit c b)
    change Nat.bit (nextBit c b) (digits (borrowWord (carryBit c b) bs).2) + c.toNat =
      Nat.bit b (digits bs) + (borrowWord (carryBit c b) bs).1.toNat * 2 ^ (bs.length + 1)
    rw [Nat.pow_succ, Nat.bit_val, Nat.bit_val, ← Nat.mul_assoc]
    cases c <;> cases b <;>
      simp only [nextBit, carryBit, Bool.xor_false, Bool.xor_true, Bool.false_and,
        Bool.true_and, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.toNat_true,
        ] at h ⊢ <;> omega

def within (word : List Bool) (cap : ℕ) (q : skip.Config) : Prop :=
  (-1 : Int) ≤ q.inputHead ∧ q.inputHead ≤ (word.length : Int) ∧
    ∀ i, (q.workHead i).natAbs ≤ cap

private theorem cfg_within (word b : List Bool) (s : Fin 10) (a p cap : ℕ)
    (out : List Bool) (ha : a ≤ word.length) (hp : p ≤ cap) :
    within word cap (cfg b s a p out) := by
  constructor
  · change (-1 : Int) ≤ (a : Int)
    omega
  · refine ⟨by simpa [cfg] using ha, fun i => ?_⟩
    simpa [cfg] using hp

private inductive Run (word : List Bool) (cap : ℕ) :
    skip.Config → skip.Config → Prop
  | stop {q} : within word cap q → Run word cap q q
  | step {q q' t} : within word cap q → skip.step word q = some q' →
      Run word cap q' t → Run word cap q t

private theorem Run.trans {word : List Bool} {cap : ℕ} {q t u : skip.Config}
    (h : Run word cap q t) (g : Run word cap t u) : Run word cap q u := by
  induction h with
  | stop _ => exact g
  | step h hr _ ih => exact .step h hr (ih g)

private theorem afterFrom_first (M : SearchTransducer) (word : List Bool)
    (q : M.Config) (k : ℕ) :
    afterFrom M word q (k + 1) =
      (M.step word q).bind (fun t => afterFrom M word t k) := by
  induction k with
  | zero => simp [afterFrom]
  | succ k ih => rw [afterFrom, ih, Option.bind_assoc]; rfl

private theorem Run.verified {word : List Bool} {cap : ℕ} {q t : skip.Config}
    (proof : Run word cap q t) (halt : skip.step word t = none) :
    (∃ k, afterFrom skip word q k = some t) ∧
      (∀ k x, afterFrom skip word q k = some x → within word cap x) := by
  induction proof with
  | stop hb =>
    refine ⟨⟨0, rfl⟩, ?_⟩
    intro k x hx
    cases k with
    | zero =>
      have hq := Option.some.inj (show some _ = some x from hx)
      simpa only [hq] using hb
    | succ k => simp [afterFrom_first, halt] at hx
  | step hb ht _ ih =>
    obtain ⟨⟨k, hk⟩, hp⟩ := ih halt
    refine ⟨⟨k + 1, by simpa [afterFrom_first, ht] using hk⟩, ?_⟩
    intro j x hx
    cases j with
    | zero =>
      have hq := Option.some.inj (show some _ = some x from hx)
      simpa only [hq] using hb
    | succ j => exact hp j x (by simpa [afterFrom_first, ht] using hx)

private theorem sweep_run (word pre bs : List Bool) (borrow : Bool) (a cap : ℕ)
    (out : List Bool) (ha : a ≤ word.length) (hp : pre.length + bs.length + 1 ≤ cap) :
    Run word cap
      (cfg (pre ++ bs) (sweepState borrow) a (pre.length + 1) out)
      (cfg (pre ++ (borrowWord borrow bs).2) (sweepState (borrowWord borrow bs).1)
        a (pre.length + bs.length + 1) out) := by
  induction bs generalizing pre borrow with
  | nil => simpa [borrowWord] using
      Run.stop (cfg_within word pre (sweepState borrow) a (pre.length + 1) cap out ha (by simpa using hp))
  | cons b bs ih =>
    refine Run.step (cfg_within word _ _ _ _ _ _ ha (by simp at hp; omega))
      (step_sweep word pre bs b borrow a out) ?_
    have hnext := ih (pre ++ [nextBit borrow b]) (carryBit borrow b) (by simp at hp ⊢; omega)
    simpa [borrowWord, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

private theorem rewind_run (word bits : List Bool) (borrow : Bool) (a j cap : ℕ)
    (out : List Bool) (ha : a ≤ word.length) (hj : j ≤ bits.length) (hc : j ≤ cap) :
    Run word cap (cfg bits (rewindState borrow) a j out)
      (cfg bits (if borrow then 5 else 0) a 0 out) := by
  induction j with
  | zero =>
    have hb := cfg_within word bits (rewindState borrow) a 0 cap out ha (Nat.zero_le _)
    exact .step hb (step_finish _ _ _ _ _) (.stop (cfg_within _ _ _ _ 0 _ _ ha (Nat.zero_le _)))
  | succ j ih =>
    exact .step (cfg_within word bits _ a (j+1) cap out ha hc)
      (step_rewind _ _ _ _ _ _ (by omega))
      (ih (by omega) (by omega))

private theorem skip_run (word : List Bool) (a : ℕ) (bits : List Bool) (cap : ℕ)
    (out : List Bool) (ha : a + digits bits ≤ word.length) (hc : bits.length + 1 ≤ cap) :
    ∃ done, done.length = bits.length ∧
      Run word cap (cfg bits 0 a 0 out) (cfg done 5 (a + digits bits) 0 out) := by
  let newBits := (borrowWord true bits).2
  let borrow := (borrowWord true bits).1
  have hlen : newBits.length = bits.length := borrowWord_length _ _
  have hvalue := borrowWord_value true bits
  change digits newBits + 1 = digits bits + borrow.toNat * 2 ^ bits.length at hvalue
  have hs := Run.step (cfg_within word bits 0 a 0 cap out (by omega) (by omega))
    (step_start word bits a out)
    (show Run word cap (cfg bits 1 a 1 out) (cfg newBits (sweepState borrow) a (bits.length + 1) out) by
      simpa [newBits, borrow, sweepState] using sweep_run word [] bits true a cap out (by omega) (by simpa using hc))
  have hb : borrow = true ↔ digits bits = 0 := by
    have hlimit := digits_lt newBits
    rw [hlen] at hlimit
    cases hcarry : borrow <;> rw [hcarry] at hvalue <;> simp at hvalue ⊢ <;> omega
  have ht := step_turn word newBits borrow a out
  rw [hlen] at ht
  by_cases h : digits bits = 0
  · have hcarr := hb.mpr h
    rw [hcarr] at hs ht
    refine ⟨newBits, hlen, hs.trans ?_⟩
    rw [h, Nat.add_zero]
    refine Run.step (cfg_within word newBits _ a _ cap out (by omega) hc) ht ?_
    simpa [← hlen] using rewind_run word newBits true a newBits.length cap out (by omega) le_rfl (by omega)
  · have hcarr : borrow = false := by
      cases he : borrow
      · rfl
      · exact (h (hb.mp he)).elim
    rw [hcarr] at hs ht hvalue
    simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hvalue
    have hh := rewind_run word newBits false (a+1) newBits.length cap out (by omega)
      le_rfl (by omega)
    have hsz : digits newBits < digits bits := by omega
    obtain ⟨done, hdone, hrun⟩ := skip_run word (a + 1) newBits cap out (by omega) (by omega)
    refine ⟨done, hdone.trans hlen, hs.trans ?_⟩
    refine Run.step (cfg_within word newBits _ a _ cap out (by omega) hc) ht ?_
    have hin : Run word cap (cfg newBits 3 (a+1) bits.length out)
      (cfg newBits 0 (a+1) 0 out) := by simpa [← hlen, rewindState] using hh
    refine hin.trans ?_
    simpa only [show a + 1 + digits newBits = a + digits bits by omega] using hrun
termination_by digits bits

/-- Starting with a binary displacement on a work tape, advance the shared
read-only input head by exactly that displacement, using bounded work space.
The input is never used as a work tape and the output is preserved. -/
theorem skip_correct (word bits out : List Bool) (a : ℕ)
    (h : a + digits bits ≤ word.length) :
    ∃ (k : ℕ) (done : List Bool),
      done.length = bits.length ∧
      afterFrom skip word (cfg bits 0 a 0 out) k = some (cfg done 5 (a + digits bits) 0 out) ∧
      skip.step word (cfg done 5 (a + digits bits) 0 out) = none ∧
      ∀ j x, afterFrom skip word (cfg bits 0 a 0 out) j = some x →
        within word (bits.length + 1) x := by
  obtain ⟨done, hlen, run⟩ := skip_run word a bits (bits.length + 1) out h le_rfl
  have hh := step_halt word done (a + digits bits) out
  obtain ⟨⟨k, hk⟩, hp⟩ := run.verified hh
  exact ⟨k, done, hlen, hk, hh, hp⟩

private theorem readInput_at (word : List Bool) (a : ℕ) (ha : a < word.length) :
    SearchTransducer.readInput word (a : Int) = .data word[a] := by
  simp [SearchTransducer.readInput, List.getElem?_eq_getElem ha]

private theorem capture_start (word bits out : List Bool) (a : ℕ) :
    skip.step word (cfg bits 6 a 0 out) = some (cfg bits 7 a 1 out) := by
  simp [SearchTransducer.step, skip, cfg, moveOffset]
  funext i j
  exact ite_self _

private theorem capture_bit (word pre tail out : List Bool) (b : Bool) (a : ℕ)
    (ha : a < word.length) :
    skip.step word (cfg (pre ++ b :: tail) 7 a (pre.length + 1) out) =
      some (cfg (pre ++ word[a] :: tail) 7 (a+1) (pre.length + 2) out) := by
  have hr : work (pre ++ b :: tail) ((pre.length : Int) + 1) = some b := by
    rw [read_cell, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hu := work_update (pre ++ b :: tail) pre.length word[a] (by simp)
  rw [set_append_cons] at hu
  have hw : (fun (_ : Fin 1) (p : Int) =>
      if p = (pre.length : Int) + 1 then some word[a] else work (pre ++ b :: tail) p) =
      (fun _ => work (pre ++ word[a] :: tail)) := funext (fun _ => hu)
  simp [SearchTransducer.step, skip, cfg, readInput_at _ _ ha, hr, moveOffset]
  refine ⟨?_, hw⟩
  funext i
  omega

private theorem capture_turn (word bits out : List Bool) (a : ℕ) :
    skip.step word (cfg bits 7 a (bits.length + 1) out) =
      some (cfg bits 8 a bits.length out) := by
  simp [SearchTransducer.step, skip, cfg, moveOffset]
  funext i j
  exact ite_self _

private theorem capture_back (word bits out : List Bool) (a i : ℕ) (hi : i < bits.length) :
    skip.step word (cfg bits 8 a (i + 1) out) = some (cfg bits 8 a i out) := by
  have hr : work bits ((i : Int) + 1) = some bits[i] := by
    rw [read_cell, List.getElem?_eq_getElem hi]
  simp [SearchTransducer.step, skip, cfg, moveOffset, hr]
  funext i j
  exact ite_self _

private theorem capture_finish (word bits out : List Bool) (a : ℕ) :
    skip.step word (cfg bits 8 a 0 out) = some (cfg bits 9 a 0 out) := by
  simp [SearchTransducer.step, skip, cfg, moveOffset]
  funext i j
  exact ite_self _

private theorem capture_rewind (word bits out : List Bool) (a j : ℕ)
    (ha : a ≤ word.length) (hj : j ≤ bits.length) :
    Run word (bits.length + 1) (cfg bits 8 a j out) (cfg bits 9 a 0 out) := by
  induction j with
  | zero =>
    exact .step (cfg_within _ _ _ _ _ _ _ ha (by omega)) (capture_finish _ _ _ _)
      (.stop (cfg_within _ _ _ _ _ _ _ ha (by omega)))
  | succ j ih =>
    exact .step (cfg_within _ _ _ _ _ _ _ ha (by omega))
      (capture_back _ _ _ _ _ (by omega)) (ih (by omega))

def window (word : List Bool) (a w : ℕ) : List Bool := (word.drop a).take w

@[simp] theorem window_length (word : List Bool) (a w : ℕ) (h : a + w ≤ word.length) :
    (window word a w).length = w := by
  simp [window]
  omega

private theorem window_succ (word : List Bool) (a w : ℕ) (h : a < word.length) :
    window word a (w + 1) = word[a] :: window word (a + 1) w := by
  induction a generalizing word with
  | zero => cases word with
    | nil => simp at h
    | cons x xs => simp [window]
  | succ a ih => cases word with
    | nil => simp at h
    | cons x xs =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
      simpa [window, Nat.succ_eq_add_one] using ih xs h

private theorem capture_run (word pre tail out : List Bool) (a cap : ℕ)
    (ha : a + tail.length ≤ word.length) (hc : pre.length + tail.length + 1 ≤ cap) :
    Run word cap (cfg (pre ++ tail) 7 a (pre.length + 1) out)
      (cfg (pre ++ window word a tail.length) 7 (a + tail.length)
        (pre.length + tail.length + 1) out) := by
  induction tail generalizing pre a with
  | nil =>
    simpa [window] using Run.stop (cfg_within word pre 7 a (pre.length + 1) cap out
      (by omega) (by simpa using hc))
  | cons b tail ih =>
    have hlt : a < word.length := by simp at ha; omega
    refine .step (cfg_within word _ _ _ _ _ _ (by omega) (by simp at hc; omega))
      (capture_bit word pre tail out b a hlt) ?_
    have hnext := ih (pre ++ [word[a]]) (a+1) (by simp at ha; omega)
      (by simp at hc ⊢; omega)
    have harr : a + 1 + tail.length = a + (b :: tail).length := by simp; omega
    rw [harr] at hnext
    simpa [window_succ word a tail.length hlt, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hnext

/-- Copy a contiguous input block into a prepared work bank. The initial contents
of the bank determine its width but are overwritten. The input stops one cell
past the copied block; the work head returns to the left marker. -/
theorem capture_correct (word bits out : List Bool) (a : ℕ)
    (ha : a + bits.length ≤ word.length) :
    ∃ k, afterFrom skip word (cfg bits 6 a 0 out) k =
        some (cfg (window word a bits.length) 9 (a + bits.length) 0 out) ∧
      skip.step word (cfg (window word a bits.length) 9 (a + bits.length) 0 out) = none ∧
      ∀ j x, afterFrom skip word (cfg bits 6 a 0 out) j = some x →
        within word (bits.length + 1) x := by
  let result := window word a bits.length
  have hr : result.length = bits.length := window_length _ _ _ ha
  have hbody : Run word (bits.length + 1) (cfg bits 7 a 1 out)
      (cfg result 7 (a + bits.length) (bits.length + 1) out) := by
    simpa [result] using capture_run word [] bits out a (bits.length+1) ha (by simp)
  have htail := capture_rewind word result out (a+bits.length) result.length ha le_rfl
  rw [hr] at htail
  have hturn := capture_turn word result out (a+bits.length)
  rw [hr] at hturn
  have hrun := Run.step (cfg_within word bits 6 a 0 (bits.length+1) out (by omega) (by omega))
    (capture_start word bits out a)
    (hbody.trans (.step (cfg_within word result 7 _ _ _ out ha le_rfl) hturn htail))
  have hh : skip.step word (cfg result 9 (a + bits.length) 0 out) = none := rfl
  obtain ⟨⟨k, hk⟩, hp⟩ := hrun.verified hh
  exact ⟨k, hk, hh, hp⟩

/-- The live contiguous capture at the encoded table address reads the exact
little-endian label of the requested product. -/
theorem window_encodeCayley (n : ℕ) (M : Mul (Fin n)) (row col : Fin n) :
    window (@encodeCayley n M) (TableIO.offset n row.val col.val) (TableIO.width n) =
      encodeLabel (TableIO.width n) (M.mul row col).val := by
  have hw : 0 < TableIO.width n := by simp [TableIO.width]
  have hb := @TableIO.tableAddress_lt_inputLength n M row col (TableIO.width n - 1) (by omega)
  have hlen : TableIO.offset n row.val col.val + TableIO.width n ≤ (@encodeCayley n M).length := by omega
  apply List.ext_getElem?
  intro i
  by_cases hi : i < TableIO.width n
  · have he : (encodeLabel (TableIO.width n) (M.mul row col).val)[i]? =
        some ((M.mul row col).val.testBit i) := by
      simp [encodeLabel, List.getElem?_eq_getElem (by simpa using hi : i < (List.range (TableIO.width n)).length)]
    rw [he]
    unfold window
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop]
    exact @TableIO.tableBit_correct n M row col i hi
  · rw [List.getElem?_eq_none (by rw [window_length _ _ _ hlen]; omega),
        List.getElem?_eq_none (by simp; omega)]

private theorem digits_testBit (b : List Bool) (i : ℕ) :
    (digits b).testBit i = (b[i]?).getD false := by
  induction b generalizing i with
  | nil => simp [digits]
  | cons b bs ih =>
    cases i with
    | zero =>
      change (Nat.bit b (digits bs)).testBit 0 = b
      cases b <;> simp [Nat.testBit, Nat.bit]
    | succ i =>
      change (Nat.bit b (digits bs)).testBit (i+1) = (bs[i]?).getD false
      rw [Nat.testBit_bit_succ, ih]

theorem digits_encodeLabel (w a : ℕ) (ha : a < 2 ^ w) :
    digits (encodeLabel w a) = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [digits_testBit]
  by_cases hi : i < w
  · simp [encodeLabel, List.getElem?_eq_getElem (by simpa using hi : i < (List.range w).length)]
  · have he : (encodeLabel w a)[i]? = none := List.getElem?_eq_none (by simp; omega)
    rw [he]
    exact (Nat.testBit_eq_false_of_lt (ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))).symm

theorem capture_tableEntry (n : ℕ) (M : Mul (Fin n)) (row col : Fin n)
    (bits out : List Bool) (hwidth : bits.length = TableIO.width n) :
    let word := @encodeCayley n M
    let a := TableIO.offset n row.val col.val
    ∃ k, afterFrom skip word (cfg bits 6 a 0 out) k =
        some (cfg (encodeLabel (TableIO.width n) (M.mul row col).val) 9
          (a + TableIO.width n) 0 out) ∧
      ∀ j x, afterFrom skip word (cfg bits 6 a 0 out) j = some x →
        within word (TableIO.width n + 1) x := by
  let word := @encodeCayley n M
  let a := TableIO.offset n row.val col.val
  have hw : 0 < TableIO.width n := by simp [TableIO.width]
  have hb := @TableIO.tableAddress_lt_inputLength n M row col (TableIO.width n - 1) (by omega)
  change a + (TableIO.width n - 1) < word.length at hb
  obtain ⟨k, hrun, _, hp⟩ := capture_correct word bits out a (by omega)
  rw [hwidth, window_encodeCayley n M row col] at hrun
  exact ⟨k, hrun, by simpa only [hwidth] using hp⟩

end Mathproof.MinimumGeneration.InputPosition
