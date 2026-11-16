import Mathproof.MinimumGenerationInputScan

namespace Mathproof.MinimumGeneration.RegisterInit

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open SearchTransducer
open InputScan (counterTape putBit)

private def start : Fin 4 := 0
private def fill : Fin 4 := 1
private def back : Fin 4 := 2
private def done : Fin 4 := 3

/-- Use the two blank delimiters of a live binary register to install an all-zero
register of the same width on a second initially blank work tape. -/
def prepareZeros : SearchTransducer where
  states := 4
  workTapes := 2
  initialState := start
  transition q _ read :=
    if q = start then some (fill, .stay, fun _ => ⟨none, .right⟩, none)
    else if q = fill then
      match read 0 with
      | some _ => some (fill, .stay,
          fun i => ⟨if i = (0 : Fin 2) then none else some (some false), .right⟩, none)
      | none => some (back, .stay, fun _ => ⟨none, .left⟩, none)
    else if q = back then
      match read 0 with
      | some _ => some (back, .stay, fun _ => ⟨none, .left⟩, none)
      | none => some (done, .stay, fun _ => ⟨none, .stay⟩, none)
    else none

def registerConfig (q : Fin 4) (input : Int) (head : Nat)
    (bits : List Bool) (written : Nat) (prior : List Bool) : prepareZeros.Config :=
  ⟨q, input, fun _ => head, fun i : Fin 2 => if i = (0 : Fin 2) then counterTape 0 bits else counterTape written [], prior⟩

def zeroStart (input : Int) (bits : List Bool) (prior : List Bool) : prepareZeros.Config :=
  registerConfig start input 0 bits 0 prior

def zeroDone (input : Int) (bits : List Bool) (prior : List Bool) : prepareZeros.Config :=
  registerConfig done input 0 bits bits.length prior

private theorem start_move (word bits prior : List Bool) (input : Int) :
    prepareZeros.step word (zeroStart input bits prior) =
      some (registerConfig fill input 1 bits 0 prior) := by
  simp [SearchTransducer.step, prepareZeros, zeroStart, registerConfig, moveOffset]
  funext i j
  exact ite_self _

private theorem fill_move (word bits prior : List Bool) (input : Int) (j : Nat)
    (hj : j < bits.length) :
    prepareZeros.step word (registerConfig fill input (j + 1) bits j prior) =
      some (registerConfig fill input (j + 2) bits (j + 1) prior) := by
  have hread : counterTape 0 bits ((j : Int) + 1) = some bits[j] := by
    have h₀ : ¬ (j : Int) + 1 ≤ 0 := by omega
    have he : ((j : Int) + 1 - 0 - 1).toNat = j := by omega
    simp only [counterTape, Int.natCast_zero, if_neg h₀, he, List.getElem?_eq_getElem hj]
  have hs : fill ≠ start := by decide
  simp [SearchTransducer.step, prepareZeros, registerConfig, hs, hread, moveOffset]
  refine ⟨funext (fun _ => by omega), ?_⟩
  funext i x
  by_cases hi : i = (0 : Fin 2)
  · simp only [hi]
    exact ite_self _
  · have ht := (InputScan.counterTape_write_nil j false).trans (InputScan.counterTape_advance j [])
    have htx := congrFun ht x
    simpa [hi, putBit] using htx

private theorem fill_turn (word bits prior : List Bool) (input : Int) :
    prepareZeros.step word (registerConfig fill input (bits.length + 1) bits bits.length prior) =
      some (registerConfig back input bits.length bits bits.length prior) := by
  have hread : counterTape 0 bits ((bits.length : Int) + 1) = none := by
    have h₀ : ¬ (bits.length : Int) + 1 ≤ 0 := by omega
    have he : ((bits.length : Int) + 1 - 0 - 1).toNat = bits.length := by omega
    simp only [counterTape, Int.natCast_zero, if_neg h₀, he, List.getElem?_eq_none (Nat.le_refl _)]
  have hs : fill ≠ start := by decide
  simp [SearchTransducer.step, prepareZeros, registerConfig, hs, hread, moveOffset]
  funext i x
  exact ite_self _

private theorem back_move (word bits prior : List Bool) (input : Int) (j : Nat)
    (hj : j < bits.length) :
    prepareZeros.step word (registerConfig back input (j + 1) bits bits.length prior) =
      some (registerConfig back input j bits bits.length prior) := by
  have hread : ∃ b : Bool, counterTape 0 bits ((j : Int) + 1) = some b := by
    simpa using InputScan.counterTape_filled 0 bits (j + 1) (by omega) (by omega)
  obtain ⟨b, hb⟩ := hread
  have hs : back ≠ start := by decide
  have hf : back ≠ fill := by decide
  simp [SearchTransducer.step, prepareZeros, registerConfig, hs, hf, hb, moveOffset]
  funext i x
  exact ite_self _

private theorem back_end (word bits prior : List Bool) (input : Int) :
    prepareZeros.step word (registerConfig back input 0 bits bits.length prior) =
      some (zeroDone input bits prior) := by
  have hs : back ≠ start := by decide
  have hf : back ≠ fill := by decide
  simp [SearchTransducer.step, prepareZeros, registerConfig, zeroDone, hs, hf, moveOffset]
  funext i x
  exact ite_self _

theorem prepareZeros_fill (word bits prior : List Bool) (input : Int) (j : Nat)
    (hj : j ≤ bits.length) :
    TableIO.afterFrom prepareZeros word (zeroStart input bits prior) (j + 1) =
      some (registerConfig fill input (j + 1) bits j prior) := by
  induction j with
  | zero => exact start_move word bits prior input
  | succ j ih =>
    rw [TableIO.afterFrom, ih (by omega)]
    exact fill_move word bits prior input j (by omega)

theorem prepareZeros_rewind (word bits prior : List Bool) (input : Int) (k : Nat)
    (hk : k ≤ bits.length) :
    TableIO.afterFrom prepareZeros word (zeroStart input bits prior) (bits.length + 2 + k) =
      some (registerConfig back input (bits.length - k) bits bits.length prior) := by
  induction k with
  | zero =>
    rw [Nat.add_zero, show bits.length + 2 = (bits.length + 1) + 1 by omega,
      TableIO.afterFrom, prepareZeros_fill word bits prior input bits.length le_rfl]
    exact fill_turn word bits prior input
  | succ k ih =>
    rw [show bits.length + 2 + (k + 1) = (bits.length + 2 + k) + 1 by omega,
      TableIO.afterFrom, ih (by omega),
      show bits.length - k = (bits.length - (k + 1)) + 1 by omega]
    exact back_move word bits prior input _ (by omega)

theorem prepareZeros_correct (word bits prior : List Bool) (input : Int) :
    TableIO.afterFrom prepareZeros word (zeroStart input bits prior)
        (bits.length + 2 + bits.length + 1) = some (zeroDone input bits prior) ∧
      prepareZeros.step word (zeroDone input bits prior) = none := by
  constructor
  · rw [TableIO.afterFrom, prepareZeros_rewind word bits prior input bits.length le_rfl,
        Nat.sub_self]
    exact back_end word bits prior input
  · have hs : done ≠ start := by decide
    have hf : done ≠ fill := by decide
    have hb : done ≠ back := by decide
    simp [SearchTransducer.step, prepareZeros, registerConfig, zeroDone, hs, hf, hb]


private theorem zerosRepresentation (k n : Nat) :
    counterTape k (List.replicate n false) = counterTape (k + n) [] := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, InputScan.counterTape_advance, ih]
    congr 1
    omega

theorem zeroDone_bank (bits prior : List Bool) (input : Int) :
    (zeroDone input bits prior).workCell (1 : Fin 2) =
      counterTape 0 (List.replicate bits.length false) := by
  have hz : (1 : Fin 2) ≠ 0 := by decide
  simpa only [zeroDone, registerConfig, if_neg hz, Nat.zero_add] using
    (zerosRepresentation 0 bits.length).symm

private theorem prepareZeros_past (word bits prior : List Bool) (input : Int) (k : Nat) :
    TableIO.afterFrom prepareZeros word (zeroStart input bits prior)
      ((bits.length + 2 + bits.length + 1) + (k + 1)) = none := by
  induction k with
  | zero =>
    rw [TableIO.afterFrom, (prepareZeros_correct word bits prior input).1]
    exact (prepareZeros_correct word bits prior input).2
  | succ k ih =>
    rw [show ((bits.length + 2 + bits.length + 1) + (k + 1 + 1)) =
      ((bits.length + 2 + bits.length + 1) + (k + 1)) + 1 by omega, TableIO.afterFrom, ih]
    rfl

/-- Every reachable configuration preserves the caller input head, output, and
source tape, and each of the two work heads stays within the initialized width
and its one right delimiter. -/
theorem prepareZeros_bounds (word bits prior : List Bool) (input : Int) (k : Nat)
    (c : prepareZeros.Config)
    (hc : TableIO.afterFrom prepareZeros word (zeroStart input bits prior) k = some c) :
    c.inputHead = input ∧ c.outputReversed = prior ∧
      c.workCell (0 : Fin 2) = counterTape 0 bits ∧
      ∀ i, 0 ≤ c.workHead i ∧ c.workHead i ≤ (bits.length : Int) + 1 := by
  have hb (q : Fin 4) (head written : Nat) (hhead : head ≤ bits.length + 1) :
      (registerConfig q input head bits written prior).inputHead = input ∧
      (registerConfig q input head bits written prior).outputReversed = prior ∧
      (registerConfig q input head bits written prior).workCell (0 : Fin 2) =
        counterTape 0 bits ∧
      ∀ i, 0 ≤ (registerConfig q input head bits written prior).workHead i ∧
        (registerConfig q input head bits written prior).workHead i ≤ (bits.length : Int) + 1 := by
    refine ⟨rfl, rfl, by simp [registerConfig], fun _ => ?_⟩
    change (0 : Int) ≤ (head : Int) ∧ (head : Int) ≤ (bits.length : Int) + 1
    omega
  by_cases hz : k = 0
  · subst k
    change some (zeroStart input bits prior) = some c at hc
    cases hc
    exact hb start 0 0 (by omega)
  by_cases hf : k ≤ bits.length + 1
  · let j := k - 1
    have hj : k = j + 1 := by dsimp [j]; omega
    rw [hj, prepareZeros_fill word bits prior input j (by omega)] at hc
    cases hc
    exact hb fill (j + 1) j (by omega)
  by_cases hr : k ≤ bits.length + 2 + bits.length
  · let j := k - (bits.length + 2)
    have hj : k = bits.length + 2 + j := by dsimp [j]; omega
    rw [hj, prepareZeros_rewind word bits prior input j (by omega)] at hc
    cases hc
    exact hb back (bits.length - j) bits.length (by omega)
  by_cases hd : k = bits.length + 2 + bits.length + 1
  · rw [hd, (prepareZeros_correct word bits prior input).1] at hc
    cases hc
    exact hb done 0 bits.length (by omega)
  · let j := k - (bits.length + 2 + bits.length + 2)
    have hj : k = (bits.length + 2 + bits.length + 1) + (j + 1) := by dsimp [j]; omega
    rw [hj, prepareZeros_past] at hc
    contradiction
end Mathproof.MinimumGeneration.RegisterInit
