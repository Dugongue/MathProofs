import Mathproof.MinimumGenerationInputPosition

namespace Mathproof.MinimumGeneration.TapeOutput

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open InputPosition (work)
open TableIO (afterFrom)

/-- Emit the live contents of a marked binary bank, least significant bit
first. Only the output channel is written. -/
def machine : SearchTransducer where
  states := 2
  workTapes := 1
  initialState := 0
  transition s _ cells :=
    if s.val = 0 then some (1, .stay, (fun _ => ⟨none, .right⟩), none)
    else (cells 0).map (fun bit => (1, .stay, (fun _ => ⟨none, .right⟩), some bit))

def start (bits prior : List Bool) (p : Int) : machine.Config :=
  ⟨machine.initialState, p, fun _ => 0, fun _ => work bits, prior.reverse⟩

private def body (bits prior : List Bool) (p : Int) (j : ℕ) : machine.Config :=
  ⟨⟨1, by decide⟩, p, fun _ => (j : Int) + 1, fun _ => work bits,
    (bits.take j).reverse ++ prior.reverse⟩

private theorem enter (word bits prior : List Bool) (p : Int) :
    machine.step word (start bits prior p) = some (body bits prior p 0) := by
  simp [SearchTransducer.step, machine, start, body, moveOffset]
  funext i x
  exact ite_self _

private theorem write (word bits prior : List Bool) (p : Int) (j : ℕ)
    (hj : j < bits.length) :
    machine.step word (body bits prior p j) = some (body bits prior p (j+1)) := by
  have hr : work bits ((j : Int) + 1) = some bits[j] := by
    simp [work, show ¬ (j : Int) + 1 ≤ 0 by omega, List.getElem?_eq_getElem hj]
  unfold SearchTransducer.step
  change (Option.map _ (Option.map _ (work bits ((j : Int) + 1)))) =
    some (body bits prior p (j+1))
  rw [hr]
  simp only [Option.map, Option.some.injEq, body, moveOffset, Int.add_zero,
    Option.getD_none, Option.elim, Int.natCast_succ,
    List.take_succ_eq_append_getElem hj, List.reverse_append, List.reverse_singleton,
    List.cons_append, List.nil_append]
  congr 1
  funext i x
  exact ite_self _

private theorem halt (word bits prior : List Bool) (p : Int) :
    machine.step word (body bits prior p bits.length) = none := by
  have hr : work bits ((bits.length : Int) + 1) = none := by
    simp [work, show ¬ (bits.length : Int) + 1 ≤ 0 by omega]
  simp [SearchTransducer.step, machine, body, hr]

private theorem emit_prefix (word bits prior : List Bool) (p : Int) (j : ℕ)
    (hj : j ≤ bits.length) :
    afterFrom machine word (start bits prior p) (j+1) = some (body bits prior p j) := by
  induction j with
  | zero => exact enter word bits prior p
  | succ j ih =>
    rw [afterFrom, ih (by omega)]
    exact write word bits prior p j (by omega)

/-- Directly emit a live binary label in its required output format. The input
head and work cells stay fixed. All work-head positions are bounded by the
length of the bank plus its end marker. -/
theorem emit_live (word bits prior : List Bool) (p : Int) :
    ∃ c : machine.Config,
      afterFrom machine word (start bits prior p) (bits.length + 1) = some c ∧
      machine.step word c = none ∧ c.outputReversed.reverse = prior ++ bits ∧
      ∀ j d, afterFrom machine word (start bits prior p) j = some d →
        d.inputHead = p ∧ d.workCell = (start bits prior p).workCell ∧
        ∀ i, (d.workHead i).natAbs ≤ bits.length + 1 := by
  refine ⟨body bits prior p bits.length, emit_prefix _ _ _ _ _ le_rfl, halt _ _ _ _, ?_, ?_⟩
  · simp [body]
  · have hn : ∀ k, afterFrom machine word (start bits prior p) (bits.length + 2 + k) = none := by
      intro k
      induction k with
      | zero =>
        change (afterFrom machine word (start bits prior p) (bits.length+1)).bind
          (machine.step word) = none
        rw [emit_prefix word bits prior p bits.length le_rfl]
        exact halt word bits prior p
      | succ k ih => rw [Nat.add_succ, afterFrom, ih]; rfl
    intro j d hd
    have hj : j ≤ bits.length + 1 := by
      by_contra! h
      obtain ⟨k, he⟩ := Nat.exists_eq_add_of_le (show bits.length+2 ≤ j by omega)
      rw [he, hn] at hd
      contradiction
    cases j with
    | zero =>
      have he := Option.some.inj (show some (start bits prior p) = some d from hd)
      subst d
      exact ⟨rfl, rfl, fun i => by simp [start]⟩
    | succ j =>
      rw [emit_prefix word bits prior p j (by omega)] at hd
      injection hd with he
      subst d
      refine ⟨rfl, rfl, fun i => ?_⟩
      change ((j : Int) + 1).natAbs ≤ bits.length+1
      rw [show (j : Int) + 1 = ((j+1 : ℕ) : Int) by omega, Int.natAbs_natCast]
      exact hj

theorem emit_label (word prior : List Bool) (p : Int) (w a : ℕ) :
    ∃ c : machine.Config,
      afterFrom machine word (start (encodeLabel w a) prior p) (w+1) = some c ∧
      machine.step word c = none ∧ c.outputReversed.reverse = prior ++ encodeLabel w a ∧
      ∀ j d, afterFrom machine word (start (encodeLabel w a) prior p) j = some d →
        d.inputHead = p ∧ d.workCell = (start (encodeLabel w a) prior p).workCell ∧
        ∀ i, (d.workHead i).natAbs ≤ w+1 := by
  simpa only [length_encodeLabel] using emit_live word (encodeLabel w a) prior p

end Mathproof.MinimumGeneration.TapeOutput
