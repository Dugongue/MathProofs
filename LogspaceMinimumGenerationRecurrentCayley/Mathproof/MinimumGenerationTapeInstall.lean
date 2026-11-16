import Mathproof.MinimumGenerationInputPosition
import Mathproof.MinimumGenerationTapeCompose

namespace Mathproof.MinimumGeneration.TapeInstall

open SearchTransducer
open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open InputPosition (work)

variable {W : Nat}

private def changes (source : Fin W → Option (Fin W)) (read : Fin W → Option Bool)
    (i : Fin W) : Option (Option Bool) :=
  (source i).map read

/-- A clock register marks a finite copy window. At each column each destination
copies the symbol from its designated source bank, including blanks. Other banks
are left untouched. This permits overwriting uninitialized or dirty destinations. -/
abbrev machine (clock : Fin W) (source : Fin W → Option (Fin W)) : SearchTransducer where
  states := 4
  workTapes := W
  initialState := 0
  transition q _ read :=
    let go := fun (r : Fin 4) (m : Move) (wr : Fin W → Option (Option Bool)) =>
      some (r, .stay, (fun i => ⟨wr i, m⟩), none)
    if q = 0 then go 1 .right (fun _ => none)
    else if q = 1 then
      match read clock with
      | some _ => go 1 .right (changes source read)
      | none => go 2 .left (fun _ => none)
    else if q = 2 then
      match read clock with
      | some _ => go 2 .left (fun _ => none)
      | none => go 3 .stay (fun _ => none)
    else none

def installed (source : Fin W → Option (Fin W)) (old : Fin W → Int → Option Bool)
    (copied : Nat) (i : Fin W) (p : Int) : Option Bool :=
  if 1 ≤ p ∧ p ≤ (copied : Int) then (source i).elim (old i p) (fun j => old j p)
  else old i p

theorem installed_source (source : Fin W → Option (Fin W))
    (old : Fin W → Int → Option Bool) (k : Nat) (i : Fin W) (hi : source i = none) :
    installed source old k i = old i := by
  funext p
  change (if 1 ≤ p ∧ p ≤ (k : Int) then (source i).elim (old i p) (fun j => old j p)
    else old i p) = old i p
  rw [hi, Option.elim_none]
  exact ite_self _

@[simp] theorem installed_zero (source : Fin W → Option (Fin W))
    (old : Fin W → Int → Option Bool) : installed source old 0 = old := by
  funext i p
  unfold installed
  rw [if_neg]
  omega

private theorem installed_next (source : Fin W → Option (Fin W))
    (old : Fin W → Int → Option Bool) (k : Nat) (i : Fin W) (p : Int) :
    (if p = (k : Int) + 1 then
      (changes source (fun j => installed source old k j ((k : Int) + 1)) i).getD
        (installed source old k i p) else installed source old k i p) =
      installed source old (k + 1) i p := by
  by_cases hp : p = (k : Int) + 1
  · subst p
    have h0 : ¬ (1 ≤ (k : Int) + 1 ∧ (k : Int) + 1 ≤ (k : Int)) := by omega
    have h1 : 1 ≤ (k : Int) + 1 ∧ (k : Int) + 1 ≤ ((k + 1 : Nat) : Int) := by omega
    have hold (j : Fin W) : installed source old k j ((k : Int) + 1) = old j ((k : Int) + 1) :=
      if_neg h0
    cases he : source i with
    | none =>
      unfold changes
      rw [he, Option.map_none, Option.getD_none, if_pos rfl, hold i]
      simp only [installed, if_pos h1, he, Option.elim_none]
    | some j =>
      unfold changes
      rw [he, Option.map_some, Option.getD_some, if_pos rfl, hold j]
      simp only [installed, if_pos h1, he, Option.elim_some]
  · have he : (1 ≤ p ∧ p ≤ (k : Int)) ↔ (1 ≤ p ∧ p ≤ ((k + 1 : Nat) : Int)) := by omega
    simp only [if_neg hp, installed, he]

private def cfg (clock : Fin W) (source : Fin W → Option (Fin W))
    (q : Fin 4) (input head : Int) (cells : Fin W → Int → Option Bool)
    (prior : List Bool) : (machine clock source).Config :=
  ⟨q, input, fun _ => head, cells, prior⟩

def start (clock : Fin W) (source : Fin W → Option (Fin W))
    (input : Int) (cells : Fin W → Int → Option Bool) (prior : List Bool) :
    (machine clock source).Config :=
  cfg clock source 0 input 0 cells prior

def stop (clock : Fin W) (source : Fin W → Option (Fin W))
    (input : Int) (cells : Fin W → Int → Option Bool) (prior : List Bool) (width : Nat) :
    (machine clock source).Config :=
  cfg clock source 3 input 0 (installed source cells width) prior

private theorem copyStep (clock : Fin W) (source : Fin W → Option (Fin W))
    (word prior : List Bool) (input head : Int) (cells : Fin W → Int → Option Bool)
    (q r : Fin 4) (m : Move) (wr : Fin W → Option (Option Bool))
    (h : (machine clock source).transition q (readInput word input) (fun i => cells i head) =
      some (r, .stay, (fun i => ⟨wr i, m⟩), none)) :
    (machine clock source).step word (cfg clock source q input head cells prior) =
      some (cfg clock source r input (head + moveOffset m)
        (fun i p => if p = head then (wr i).getD (cells i p) else cells i p) prior) := by
  unfold SearchTransducer.step cfg
  rw [h]
  simp [moveOffset]

private theorem idleStep (clock : Fin W) (source : Fin W → Option (Fin W))
    (word prior : List Bool) (input head : Int) (cells : Fin W → Int → Option Bool)
    (q r : Fin 4) (m : Move)
    (h : (machine clock source).transition q (readInput word input) (fun i => cells i head) =
      some (r, .stay, (fun _ => ⟨none, m⟩), none)) :
    (machine clock source).step word (cfg clock source q input head cells prior) =
      some (cfg clock source r input (head + moveOffset m) cells prior) := by
  rw [copyStep clock source word prior input head cells q r m (fun _ => none) h]
  exact congrArg (fun tape => some (cfg clock source r input (head + moveOffset m) tape prior))
    (funext fun i => funext fun p => ite_self (cells i p))

private theorem work_bit (bits : List Bool) (i : Nat) :
    work bits ((i : Int) + 1) = bits[i]? := by
  simp [work, show ¬ ((i : Int) + 1 ≤ 0) by omega]

private theorem forward (clock : Fin W) (source : Fin W → Option (Fin W))
    (clockNotDest : source clock = none)
    (word bits prior : List Bool) (input : Int) (cells : Fin W → Int → Option Bool)
    (hc : cells clock = work bits) (j : Nat) (hj : j ≤ bits.length) :
    (machine clock source).runFrom word (start clock source input cells prior) (j + 1) =
      some (cfg clock source 1 input ((j : Int) + 1) (installed source cells j) prior) := by
  induction j with
  | zero =>
    simpa [runFrom, start, moveOffset] using
      idleStep clock source word prior input 0 cells 0 1 .right rfl
  | succ j ih =>
    have hj' : j < bits.length := by omega
    rw [runFrom, ih (by omega), Option.bind_some]
    have hread : installed source cells j clock ((j : Int) + 1) = some bits[j] := by
      rw [installed_source source cells j clock clockNotDest, hc, work_bit, List.getElem?_eq_getElem hj']
    have hs := copyStep clock source word prior input ((j : Int) + 1)
      (installed source cells j) 1 1 .right
      (changes source (fun i => installed source cells j i ((j : Int) + 1)))
      (by simp [machine, hread])
    have hx := funext fun i => funext (installed_next source cells j i)
    simpa [hx, moveOffset, Int.add_assoc] using hs

private theorem rewind (clock : Fin W) (source : Fin W → Option (Fin W))
    (clockNotDest : source clock = none)
    (word bits prior : List Bool) (input : Int) (cells : Fin W → Int → Option Bool)
    (hc : cells clock = work bits) (j : Nat) (hj : j ≤ bits.length) :
    (machine clock source).runFrom word (start clock source input cells prior)
       (bits.length + 2 + j) =
      some (cfg clock source 2 input (bits.length - j : Nat)
        (installed source cells bits.length) prior) := by
  have hclock := installed_source source cells bits.length clock clockNotDest
  induction j with
  | zero =>
    rw [Nat.add_zero, show bits.length + 2 = (bits.length + 1) + 1 by omega, runFrom,
      forward clock source clockNotDest word bits prior input cells hc bits.length le_rfl,
      Option.bind_some]
    have hread : installed source cells bits.length clock ((bits.length : Int) + 1) = none := by
      rw [hclock, hc, work_bit, List.getElem?_eq_none le_rfl]
    simpa [moveOffset] using
      idleStep clock source word prior input ((bits.length : Int) + 1)
        (installed source cells bits.length) 1 2 .left (by simp [machine, hread])
  | succ j ih =>
    rw [show bits.length + 2 + (j + 1) = (bits.length + 2 + j) + 1 by omega, runFrom,
      ih (by omega), Option.bind_some]
    let i := bits.length - (j + 1)
    have he : (↑(bits.length - j) : Int) = (i : Int) + 1 := by dsimp [i]; omega
    have hi : i < bits.length := by omega
    have hread : installed source cells bits.length clock ((i : Int) + 1) = some bits[i] := by
      rw [hclock, hc, work_bit, List.getElem?_eq_getElem hi]
    rw [he]
    simpa [moveOffset] using
      idleStep clock source word prior input ((i : Int) + 1) (installed source cells bits.length)
        2 2 .left (by simp [machine, hread])

/-- One physical sweep installs the entire family of marked output banks
from live source templates, then returns all heads to their origins. -/
theorem execute (clock : Fin W) (source : Fin W → Option (Fin W))
    (clockNotDest : source clock = none)
    (word bits prior : List Bool) (input : Int) (cells : Fin W → Int → Option Bool)
    (hc : cells clock = work bits)
    (hi : (-1 : Int) ≤ input ∧ input ≤ word.length) :
    (machine clock source).BoundedSegment word (bits.length + 1)
      (start clock source input cells prior) (stop clock source input cells prior bits.length)
      (bits.length + 2 + bits.length + 1) ∧
    (machine clock source).step word (stop clock source input cells prior bits.length) = none := by
  let M := machine clock source
  let ticks := bits.length + 2 + bits.length + 1
  have hresult : M.runFrom word (start clock source input cells prior) ticks =
      some (stop clock source input cells prior bits.length) := by
    dsimp only [ticks]
    rw [runFrom, rewind clock source clockNotDest word bits prior input cells hc bits.length le_rfl,
      Nat.sub_self, Option.bind_some]
    have hread : installed source cells bits.length clock 0 = none := by
      rw [installed_source source cells bits.length clock clockNotDest, hc]
      simp [work]
    simpa [stop, moveOffset] using
      idleStep clock source word prior input 0 (installed source cells bits.length)
        2 3 .stay (by simp [machine, hread])
  refine ⟨⟨hresult, ?_⟩, by simp [machine, SearchTransducer.step, stop, cfg]⟩
  intro k hk c hRun
  have hconfig (q : Fin 4) (h : Int) (mc : Fin W → Int → Option Bool)
      (hh : h.natAbs ≤ bits.length + 1) :
      M.Bounded word (bits.length + 1) (cfg clock source q input h mc prior) :=
    ⟨hi.1, hi.2, fun _ => hh⟩
  by_cases hz : k = 0
  · subst k
    change some _ = some c at hRun
    cases hRun
    exact hconfig 0 0 cells (by simp)
  by_cases hf : k ≤ bits.length + 1
  · let j := k - 1
    have hk' : k = j + 1 := by dsimp [j]; omega
    rw [hk', forward clock source clockNotDest word bits prior input cells hc j (by omega)] at hRun
    cases hRun
    exact hconfig 1 ((j : Int) + 1) _ (by omega)
  by_cases hr : k ≤ bits.length + 2 + bits.length
  · let j := k - (bits.length + 2)
    have hk' : k = bits.length + 2 + j := by dsimp [j]; omega
    rw [hk', rewind clock source clockNotDest word bits prior input cells hc j (by omega)] at hRun
    cases hRun
    exact hconfig 2 (bits.length - j : Nat) _ (by omega)
  · have hk' : k = ticks := by dsimp [ticks] at *; omega
    rw [hk', hresult] at hRun
    cases hRun
    exact hconfig 3 0 _ (by simp)

/-- Agreement outside the write window suffices to get exact tape equality on
a destination. No hypothesis about its previous contents inside is needed. -/
theorem installed_exact (source : Fin W → Option (Fin W))
    (cells : Fin W → Int → Option Bool) (width : Nat) (i j : Fin W)
    (hs : source i = some j) (outside : ∀ p, p < 1 ∨ (width : Int) < p → cells i p = cells j p) :
    installed source cells width i = cells j := by
  funext p
  by_cases hp : 1 ≤ p ∧ p ≤ (width : Int)
  · simp [installed, hp, hs]
  · simpa [installed, hp] using outside p (by omega)

end Mathproof.MinimumGeneration.TapeInstall
