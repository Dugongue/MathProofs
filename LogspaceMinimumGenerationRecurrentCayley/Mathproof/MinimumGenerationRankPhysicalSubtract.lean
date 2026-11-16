import Mathproof.MinimumGenerationInputPosition
import Mathproof.MinimumGenerationTapeCompose
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMFixedWord20261001

/-!
A two-work-tape subtractor for prepared binary words. The second tape is
overwritten by the difference. Finite control returns the final borrow.
-/

namespace Mathproof.MinimumGeneration.RankPhysicalSubtract

open SearchTransducer Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open Lax51Proofs.RamToTM

private def scanState (borrow : Bool) : Fin 7 := if borrow then 2 else 1
private def returnState (borrow : Bool) : Fin 7 := if borrow then 4 else 3

def done (borrow : Bool) : Fin 7 := if borrow then 6 else 5

private def action (m : Move) (record : Option Bool) (bank : Fin 2) :
    Action (Option Bool) :=
  ⟨if bank = 1 then record.map some else none, m⟩

abbrev machine : SearchTransducer where
  states := 7
  workTapes := 2
  initialState := 0
  transition q _ read :=
    let next (r : Fin 7) (m : Move) (record : Option Bool := none) :=
      some (r, .stay, action m record, none)
    if q = 0 then next (scanState false) .right
    else if q = 1 ∨ q = 2 then
      let borrow := decide (q = 2)
      match read 0, read 1 with
      | some b, some a =>
        let out := fullSubtractor a b borrow
        next (scanState out.2) .right (some out.1)
      | none, none => next (returnState borrow) .left
      | _, _ => none
    else if q = 3 ∨ q = 4 then
      let borrow := decide (q = 4)
      match read 1 with
      | some _ => next (returnState borrow) .left
      | none => next (done borrow) .stay
    else none

/-- Both register heads are at the same local offset. The first bank is the
subtrahend and the second is the mutable minuend. -/
def cfg (q : Fin 7) (pos : Nat) (target source out : List Bool) (parked : Int) :
    machine.Config :=
  ⟨q, parked, fun _ => pos, fun t => InputPosition.work (if t = 0 then source else target), out⟩

private theorem work_middle (before : List Bool) (bit : Bool) (after : List Bool) :
    InputPosition.work (before ++ bit :: after) (before.length + 1 : Nat) = some bit := by
  simp only [InputPosition.work]
  have hp : ¬ ((before.length + 1 : Nat) : Int) ≤ 0 := by omega
  have hIndex : (((before.length + 1 : Nat) : Int) - 1).toNat = before.length := by omega
  rw [if_neg hp, hIndex, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

private theorem work_blank (bits : List Bool) :
    InputPosition.work bits (bits.length + 1 : Nat) = none := by
  simp only [InputPosition.work]
  have hp : ¬ ((bits.length + 1 : Nat) : Int) ≤ 0 := by omega
  have hIndex : (((bits.length + 1 : Nat) : Int) - 1).toNat = bits.length := by omega
  rw [if_neg hp, hIndex]
  exact List.getElem?_eq_none (by omega)

private theorem work_replace (before : List Bool) (a b : Bool) (after : List Bool) (j : Int) :
    (if j = (before.length + 1 : Nat) then some b
      else InputPosition.work (before ++ a :: after) j) =
      InputPosition.work (before ++ b :: after) j := by
  by_cases hEq : j = (before.length + 1 : Nat)
  · rw [if_pos hEq, hEq, work_middle]
  · rw [if_neg hEq]
    by_cases hZero : j ≤ 0
    · simp [InputPosition.work, hZero]
    · simp only [InputPosition.work, if_neg hZero]
      by_cases hBefore : (j - 1).toNat < before.length
      · rw [List.getElem?_append_left hBefore, List.getElem?_append_left hBefore]
      · have hAfter : before.length ≤ (j - 1).toNat := by omega
        rw [List.getElem?_append_right hAfter, List.getElem?_append_right hAfter]
        have hn : (j - 1).toNat - before.length ≠ 0 := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
        rw [hk]
        rfl

private theorem bound (word : List Bool) (B pos : Nat) (q : Fin 7)
    (target source out : List Bool) (parked : Int) (hp : pos ≤ B)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length) :
    machine.Bounded word B (cfg q pos target source out parked) := by
  exact ⟨hin.1, hin.2, fun _ => hp⟩

private theorem one {word : List Bool} {B : Nat} {c d : machine.Config}
    (h : machine.step word c = some d) (hc : machine.Bounded word B c)
    (hd : machine.Bounded word B d) : machine.BoundedSegment word B c d 1 := by
  refine ⟨by simpa [runFrom] using h, ?_⟩
  intro k hk e he
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · simpa [runFrom] using (Option.some.inj he ▸ hc)
  · change machine.step word c = some e at he
    rw [h] at he
    exact (Option.some.inj he) ▸ hd

private theorem enter (word target source out : List Bool) (parked : Int) :
    machine.step word (cfg 0 0 target source out parked) =
      some (cfg (scanState false) 1 target source out parked) := by
  simp [SearchTransducer.step, machine, cfg, action, moveOffset]

private theorem scan_bit (word tp sp xs ys out : List Bool) (a b borrow : Bool)
    (hp : tp.length = sp.length) (parked : Int) :
    let q := fullSubtractor a b borrow
    machine.step word (cfg (scanState borrow) (tp.length + 1)
      (tp ++ a :: xs) (sp ++ b :: ys) out parked) =
      some (cfg (scanState q.2) (tp.length + 2)
        (tp ++ q.1 :: xs) (sp ++ b :: ys) out parked) := by

  have hb' : (sp ++ b :: ys)[tp.length]? = some b := by
    rw [hp, List.getElem?_append_right le_rfl, Nat.sub_self]
    rfl
  cases borrow <;>
    simp [SearchTransducer.step, machine, cfg, action, scanState, hb', moveOffset,
      Int.add_assoc]
  all_goals
    funext t j
    fin_cases t
    · simp
    · simpa using work_replace tp a (fullSubtractor a b _).1 xs j

private theorem scan_end (word target source out : List Bool) (borrow : Bool)
    (hp : target.length = source.length) (parked : Int) :
    machine.step word
      (cfg (scanState borrow) (target.length + 1) target source out parked) =
      some (cfg (returnState borrow) target.length target source out parked) := by

  unfold SearchTransducer.step
  have hb' : source[target.length]? = none := List.getElem?_eq_none (by omega)
  cases borrow <;> simp [machine, cfg, action, scanState, returnState, hb', moveOffset]

private theorem return_bit (word target source out : List Bool) (borrow : Bool)
    (p : Nat) (hp : p < target.length) (parked : Int) :
    machine.step word (cfg (returnState borrow) (p+1) target source out parked) =
      some (cfg (returnState borrow) p target source out parked) := by

  unfold SearchTransducer.step
  cases borrow <;> simp [machine, cfg, action, returnState, moveOffset,
    List.getElem?_eq_getElem hp]

private theorem return_end (word target source out : List Bool) (borrow : Bool) (parked : Int) :
    machine.step word (cfg (returnState borrow) 0 target source out parked) =
      some (cfg (done borrow) 0 target source out parked) := by
  have hm : InputPosition.work target 0 = none := rfl
  cases borrow <;> simp [SearchTransducer.step, machine, cfg, action, returnState, done,
    hm, moveOffset]

theorem stop (word target source out : List Bool) (borrow : Bool) (parked : Int) :
    machine.step word (cfg (done borrow) 0 target source out parked) = none := by
  cases borrow <;> simp [SearchTransducer.step, machine, cfg, done]

private theorem scan (word out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (xs ys tp sp : List Bool) (hxy : xs.length = ys.length) (hp : tp.length = sp.length)
    (borrow : Bool) :
    machine.BoundedSegment word (tp.length + xs.length + 1)
      (cfg (scanState borrow) (tp.length + 1) (tp ++ xs) (sp ++ ys) out parked)
      (cfg (returnState (subBorrowOut xs ys borrow)) (tp.length + xs.length)
        (tp ++ subBits xs ys borrow) (sp ++ ys) out parked)
      (xs.length + 1) := by
  induction xs generalizing ys tp sp borrow with
  | nil =>
    cases ys with
    | nil =>
      simp only [List.append_nil, List.length_nil, Nat.add_zero, subBits, subBorrowOut]
      exact one (scan_end word tp sp out borrow hp parked)
        (bound _ _ _ _ _ _ _ _ le_rfl hin) (bound _ _ _ _ _ _ _ _ (by omega) hin)
    | cons b ys => simp at hxy
  | cons a xs ih =>
    cases ys with
    | nil => simp at hxy
    | cons b ys =>
      have ht : xs.length = ys.length := by simpa using hxy
      let result := fullSubtractor a b borrow
      have hPrefix : (tp ++ [result.1]).length = (sp ++ [b]).length := by simp [hp]
      have rest := ih ys (tp ++ [result.1]) (sp ++ [b]) ht hPrefix result.2
      have hWidth : (tp ++ [result.1]).length + xs.length = tp.length + (a :: xs).length := by
        simp
        omega
      have headEq : (tp ++ [result.1]).length + 1 = tp.length + 2 := by simp
      rw [hWidth, headEq] at rest
      simp only [List.append_assoc, List.singleton_append] at rest
      have first := one (scan_bit word tp sp xs ys out a b borrow hp parked)
        (B := tp.length + (a :: xs).length + 1)
        (bound _ _ _ _ _ _ _ _ (by simp) hin)
        (bound _ _ _ _ _ _ _ _ (by simp <;> omega) hin)
      have all := BoundedSegment.append machine first rest
      have hCount : 1 + (xs.length + 1) = (a :: xs).length + 1 := by simp only [List.length_cons]; omega
      rw [hCount] at all
      exact all

private theorem rewind (word target source out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length) (borrow : Bool) (p : Nat)
    (hp : p ≤ target.length) :
    machine.BoundedSegment word (target.length + 1)
      (cfg (returnState borrow) p target source out parked)
      (cfg (done borrow) 0 target source out parked) (p + 1) := by
  induction p with
  | zero =>
    exact one (return_end word target source out borrow parked)
      (bound _ _ _ _ _ _ _ _ (by omega) hin) (bound _ _ _ _ _ _ _ _ (by omega) hin)
  | succ p ih =>
    have first := one (return_bit word target source out borrow p (by omega) parked)
      (B := target.length + 1) (bound _ _ _ _ _ _ _ _ (by omega) hin)
      (bound _ _ _ _ _ _ _ _ (by omega) hin)
    have combined := BoundedSegment.append machine first (ih (by omega))
    simpa [Nat.add_comm 1, Nat.add_assoc] using combined

/-- The actual machine subtracts the prepared words, reports borrow, returns
both heads to the delimiters, and preserves both external tape positions. -/
theorem execute (word target source out : List Bool) (parked : Int)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (hlen : target.length = source.length) :
    let borrow := subBorrowOut target source false
    let difference := subBits target source false
    machine.BoundedSegment word (target.length + 1) (cfg 0 0 target source out parked)
      (cfg (done borrow) 0 difference source out parked) (2 * target.length + 3) ∧
    machine.step word (cfg (done borrow) 0 difference source out parked) = none := by
  let borrow := subBorrowOut target source false
  let difference := subBits target source false
  have hdiff : difference.length = target.length := subBits_length_of_eq false hlen
  have front := one (enter word target source out parked)
    (B := target.length + 1) (bound _ _ _ _ _ _ _ _ (by omega) hin)
    (bound _ _ _ _ _ _ _ _ (by omega) hin)
  have middle := scan word out parked hin target source [] [] hlen rfl false
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at middle
  have tail := rewind word difference source out parked hin borrow target.length (by omega)
  rw [hdiff] at tail
  have all := BoundedSegment.append machine (BoundedSegment.append machine front middle) tail
  have hCount : 1 + (target.length + 1) + (target.length + 1) = 2 * target.length + 3 := by omega
  rw [hCount] at all
  exact ⟨all, stop word difference source out borrow parked⟩

theorem execute_of_le (word out : List Bool) (parked : Int) (w x y : Nat)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (hx : x < 2^w) (hxy : y ≤ x) :
    machine.BoundedSegment word (w + 1)
      (cfg 0 0 (fixedBits w x) (fixedBits w y) out parked)
      (cfg (done false) 0 (fixedBits w (x-y)) (fixedBits w y) out parked) (2*w+3) ∧
    machine.step word (cfg (done false) 0 (fixedBits w (x-y)) (fixedBits w y) out parked) = none := by
  simpa only [fixedBits_length, subBorrowOut_fixed_false_of_le w hx (hxy.trans_lt hx) hxy,
    ← fixedBits_sub_of_le w hxy] using
      execute word (fixedBits w x) (fixedBits w y) out parked hin (by simp)

private theorem bitsValue_eq_digits (xs : List Bool) : bitsValue xs = InputPosition.digits xs := by
  induction xs <;> simp [bitsValue, InputPosition.digits, *]

theorem fixedBits_eq_encodeLabel (w x : Nat) (hx : x < 2^w) :
    fixedBits w x = encodeLabel w x := by
  apply bitsValue_injective_of_length (by simp)
  rw [bitsValue_fixedBits_of_lt hx, bitsValue_eq_digits, InputPosition.digits_encodeLabel _ _ hx]

/-- Execute the subtractor on the common live register encoding. The final
finite control directly reports an unsigned comparison, including underflow. -/
theorem execute_encoded (word out : List Bool) (parked : Int) (w x y : Nat)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (hx : x < 2^w) (hy : y < 2^w) :
    let trial := subBits (encodeLabel w x) (encodeLabel w y) false
    machine.BoundedSegment word (w+1) (cfg 0 0 (encodeLabel w x) (encodeLabel w y) out parked)
      (cfg (done (decide (x<y))) 0 trial (encodeLabel w y) out parked) (2*w+3) ∧
    machine.step word (cfg (done (decide (x<y))) 0 trial (encodeLabel w y) out parked) = none := by
  have h := execute word (fixedBits w x) (fixedBits w y) out parked hin (by simp)
  dsimp only at h ⊢
  rw [subBorrowOut_fixed_eq_decide_lt w x y hx hy, fixedBits_length,
    fixedBits_eq_encodeLabel w x hx, fixedBits_eq_encodeLabel w y hy] at h
  exact h

theorem execute_encoded_of_le (word out : List Bool) (parked : Int) (w x y : Nat)
    (hin : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (hx : x < 2^w) (hxy : y ≤ x) :
    machine.BoundedSegment word (w + 1)
      (cfg 0 0 (encodeLabel w x) (encodeLabel w y) out parked)
      (cfg (done false) 0 (encodeLabel w (x-y)) (encodeLabel w y) out parked) (2*w+3) ∧
    machine.step word (cfg (done false) 0 (encodeLabel w (x-y)) (encodeLabel w y) out parked) = none := by
  have h := execute_of_le word out parked w x y hin hx hxy
  rwa [fixedBits_eq_encodeLabel w x hx, fixedBits_eq_encodeLabel w y (hxy.trans_lt hx),
    fixedBits_eq_encodeLabel w (x-y) ((Nat.sub_le x y).trans_lt hx)] at h


end Mathproof.MinimumGeneration.RankPhysicalSubtract
