import Mathproof.MinimumGenerationInputScan
import Mathproof.MinimumGenerationTapeCompose
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases

/-!
# Extend a live binary register using a width template
-/

namespace Mathproof.MinimumGeneration.TapeWiden

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)
open SearchTransducer
open InputScan (counterTape putBit)

private def action (source target : Move) (write : Option Bool) (i : Fin 2) :
    Action (Option Bool) :=
  if i = 0 then ⟨none, source⟩ else ⟨write.map some, target⟩

/-- Follow the target to its right delimiter, append one zero for each
template bit, and return both heads to their left delimiters. -/
abbrev machine : SearchTransducer where
  states := 6
  workTapes := 2
  initialState := 0
  transition q _ read :=
    let go := fun (r : Fin 6) (ps pt : Move) (bit : Option Bool) =>
      some (r, .stay, action ps pt bit, none)
    if q = 0 then go 1 .stay .right none
    else if q = 1 then
      match read 1 with
      | some _ => go 1 .stay .right none
      | none => go 2 .right .stay none
    else if q = 2 then
      match read 0 with
      | some _ => go 2 .right .right (some false)
      | none => go 3 .left .left none
    else if q = 3 then
      match read 0 with
      | some _ => go 3 .left .stay none
      | none => go 4 .stay .stay none
    else if q = 4 then
      match read 1 with
      | some _ => go 4 .stay .left none
      | none => go 5 .stay .stay none
    else none

private def cfg (q : Fin 6) (s t : ℕ) (i : Int) (src dst prior : List Bool) : machine.Config :=
  ⟨q, i, fun bank => if bank = 0 then (s : Int) else (t : Int),
    fun bank => if bank = 0 then counterTape 0 src else counterTape 0 dst, prior⟩

def startConfig (input : Int) (template target prior : List Bool) : machine.Config :=
  cfg 0 0 0 input template target prior

def stopConfig (input : Int) (template target prior : List Bool) : machine.Config :=
  cfg 5 0 0 input template (target ++ List.replicate template.length false) prior

private theorem tape_end (bits : List Bool) :
    counterTape 0 bits ((bits.length + 1 : ℕ) : Int) = none := by
  have hp : ¬ ((bits.length + 1 : ℕ) : Int) ≤ 0 := by omega
  have he : (((bits.length + 1 : ℕ) : Int) - 0 - 1).toNat = bits.length := by omega
  simp only [counterTape, Int.natCast_zero, if_neg hp, he, List.getElem?_eq_none le_rfl]

private theorem tape_append (bits : List Bool) :
    putBit (counterTape 0 bits) ((bits.length + 1 : ℕ) : Int) false =
      counterTape 0 (bits ++ [false]) := by
  funext j
  by_cases hj : j ≤ 0
  · have hne : j ≠ ((bits.length + 1 : ℕ) : Int) := by omega
    simp only [putBit, if_neg hne, counterTape, if_pos hj]
  let a := (j - 0 - 1).toNat
  have he : j = ((bits.length + 1 : ℕ) : Int) ↔ a = bits.length := by
    dsimp [a]
    omega
  simp only [putBit, counterTape, Int.natCast_zero, if_neg hj, he]
  change (if a = bits.length then some false else bits[a]?) = (bits ++ [false])[a]?
  by_cases ha : a < bits.length
  · rw [if_neg (Nat.ne_of_lt ha), List.getElem?_append_left ha]
  · have hle : bits.length ≤ a := by omega
    rw [List.getElem?_append_right hle]
    by_cases h : a = bits.length
    · simp [h]
    · have hp : a - bits.length ≠ 0 := by omega
      simp [h, hp, hle]

private theorem step_cfg (word : List Bool) (input : Int) (prior src dst dst' : List Bool)
    (q r : Fin 6) (s t s' t' : ℕ) (ds dt : Move) (w : Option Bool)
    (htr : machine.transition q (readInput word input)
      (fun bank => if bank = 0 then counterTape 0 src s else counterTape 0 dst t) =
      some (r, .stay, action ds dt w, none))
    (hs : (s' : Int) = (s : Int) + moveOffset ds)
    (ht : (t' : Int) = (t : Int) + moveOffset dt)
    (hw : (fun p => if p = (t : Int) then (w.map some).getD (counterTape 0 dst p)
      else counterTape 0 dst p) = counterTape 0 dst') :
    machine.step word (cfg q s t input src dst prior) =
      some (cfg r s' t' input src dst' prior) := by
  unfold SearchTransducer.step
  have scan : (fun bank => (cfg q s t input src dst prior).workCell bank
      ((cfg q s t input src dst prior).workHead bank)) =
      (fun bank => if bank = 0 then counterTape 0 src s else counterTape 0 dst t) := by
    funext b
    by_cases hb : b = 0 <;> simp [cfg, hb]
  rw [scan]
  change Option.map _ (machine.transition q (readInput word input) _) = _
  rw [htr]
  simp only [Option.map_some, Option.some.injEq, cfg, moveOffset, Int.add_zero, Option.elim]
  congr 1
  · funext b
    by_cases hb : b = 0
    · simpa [action, hb, moveOffset] using hs.symm
    · simpa [action, hb, moveOffset] using ht.symm
  · funext b p
    by_cases hb : b = 0
    · simp [action, hb]
    · simpa only [action, hb, if_false] using congrFun hw p

private theorem fixed_step (word : List Bool) (input : Int) (prior src dst : List Bool)
    (q r : Fin 6) (s t s' t' : ℕ) (ds dt : Move)
    (htr : machine.transition q (readInput word input)
      (fun bank => if bank = 0 then counterTape 0 src s else counterTape 0 dst t) =
      some (r, .stay, action ds dt none, none))
    (hs : (s' : Int) = (s : Int) + moveOffset ds)
    (ht : (t' : Int) = (t : Int) + moveOffset dt) :
    machine.step word (cfg q s t input src dst prior) =
      some (cfg r s' t' input src dst prior) :=
  step_cfg word input prior src dst dst q r s t s' t' ds dt none htr hs ht
    (funext fun _ => ite_self _)

private theorem bound_cfg {word out src dst : List Bool} {input : Int} {B s t : ℕ}
    {q : Fin 6} (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) (hs : s ≤ B) (ht : t ≤ B) :
    machine.Bounded word B (cfg q s t input src dst out) := by
  refine ⟨hin.1, hin.2, ?_⟩
  intro b
  by_cases hb : b = 0 <;> simp [cfg, hb, hs, ht]

private theorem segment_step {word : List Bool} {B : ℕ} {c d : machine.Config}
    (step : machine.step word c = some d)
    (left : machine.Bounded word B c) (right : machine.Bounded word B d) :
    machine.BoundedSegment word B c d 1 := by
  refine ⟨step, ?_⟩
  intro n hn p hp
  have h : n = 0 ∨ n = 1 := by omega
  rcases h with rfl | rfl
  · have he := Option.some.inj hp
    cases he
    exact left
  · have he := Option.some.inj (step.symm.trans hp)
    cases he
    exact right

private theorem segment_scan (word : List Bool) (C : ℕ → machine.Config) (n B : ℕ)
    (steps : ∀ j < n, machine.step word (C j) = some (C (j + 1)))
    (bound : ∀ j ≤ n, machine.Bounded word B (C j)) :
    machine.BoundedSegment word B (C 0) (C n) n := by
  induction n with
  | zero =>
    refine ⟨rfl, ?_⟩
    intro k hk d hd
    have h : k = 0 := by omega
    subst k
    cases Option.some.inj hd
    exact bound 0 le_rfl
  | succ n ih =>
    have hfirst := ih (fun j hj => steps j (by omega)) (fun j hj => bound j (by omega))
    exact BoundedSegment.append machine hfirst (segment_step
      (steps n (by omega)) (bound n (by omega)) (bound (n + 1) le_rfl))


private theorem seekRun (word src dst out : List Bool) (input : Int)
    (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) :
    machine.BoundedSegment word (2 * dst.length + 1)
      (cfg 1 0 1 input src dst out) (cfg 1 0 (dst.length + 1) input src dst out) dst.length := by
  let C := fun j : ℕ => cfg 1 0 (j + 1) input src dst out
  apply segment_scan word C
  · intro j hj
    obtain ⟨b, hb⟩ := InputScan.counterTape_filled 0 dst (j + 1) (by omega) (by omega)
    simp only [Int.natCast_add, Int.natCast_one] at hb
    exact fixed_step word input out src dst 1 1 0 (j + 1) 0 (j + 1 + 1) .stay .right
      (by simp [machine, hb]) (by simp [moveOffset]) (by simp [moveOffset])
  · intro j hj
    exact bound_cfg hin (by omega) (by omega)

private theorem fillRun (word src dst out : List Bool) (input : Int)
    (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) (hlen : src.length = dst.length) :
    machine.BoundedSegment word (2 * dst.length + 1)
      (cfg 2 1 (dst.length + 1) input src dst out)
      (cfg 2 (dst.length + 1) (2 * dst.length + 1) input src
        (dst ++ List.replicate dst.length false) out) dst.length := by
  let C := fun j : ℕ =>
    cfg 2 (j + 1) (dst.length + j + 1) input src (dst ++ List.replicate j false) out
  have run := segment_scan word C dst.length (2 * dst.length + 1) ?_ ?_
  · have eq : dst.length + dst.length + 1 = 2 * dst.length + 1 := by omega
    simpa [C, eq] using run
  · intro j hj
    obtain ⟨b, hb⟩ := InputScan.counterTape_filled 0 src (j + 1) (by omega) (by omega)
    simp only [Int.natCast_add, Int.natCast_one] at hb
    have hw : putBit (counterTape 0 (dst ++ List.replicate j false))
        ((dst.length + j + 1 : ℕ) : Int) false =
        counterTape 0 (dst ++ List.replicate (j + 1) false) := by
      have h := tape_append (dst ++ List.replicate j false)
      simpa only [List.length_append, List.length_replicate, List.replicate_add,
        List.replicate_one, List.append_assoc] using h
    refine step_cfg word input out src _ _ 2 2 (j + 1) (dst.length + j + 1)
      (j + 1 + 1) (dst.length + (j + 1) + 1) .right .right (some false)
      (by simp [machine, hb]) (by simp [moveOffset]) (by simp [moveOffset]; omega) ?_
    exact hw
  · intro j hj
    exact bound_cfg hin (by omega) (by omega)

private theorem rewindSource (word src dst out : List Bool) (input : Int) (w : ℕ)
    (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) (hlen : src.length = w) :
    machine.BoundedSegment word (2 * w + 1)
      (cfg 3 w (2*w) input src dst out) (cfg 3 0 (2*w) input src dst out) w := by
  let C := fun j : ℕ => cfg 3 (w - j) (2*w) input src dst out
  have run := segment_scan word C w (2*w+1) ?_ ?_
  · simpa [C] using run
  · intro j hj
    obtain ⟨b, hb⟩ := InputScan.counterTape_filled 0 src (w-j) (by omega) (by omega)
    refine fixed_step word input out src dst 3 3 (w-j) (2*w) (w-(j+1)) (2*w) .left .stay
      (by simp [machine, hb]) ?_ (by simp [moveOffset])
    simp only [moveOffset]
    omega
  · intro j hj
    exact bound_cfg hin (by omega) (by omega)

private theorem rewindTarget (word src dst out : List Bool) (input : Int) (w : ℕ)
    (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) (hlen : dst.length = 2*w) :
    machine.BoundedSegment word (2 * w + 1)
      (cfg 4 0 (2*w) input src dst out) (cfg 4 0 0 input src dst out) (2*w) := by
  let C := fun j : ℕ => cfg 4 0 (2*w-j) input src dst out
  have run := segment_scan word C (2*w) (2*w+1) ?_ ?_
  · simpa [C] using run
  · intro j hj
    obtain ⟨b, hb⟩ := InputScan.counterTape_filled 0 dst (2*w-j) (by omega) (by omega)
    refine fixed_step word input out src dst 4 4 0 (2*w-j) 0 (2*w-(j+1)) .stay .left
      (by simp [machine, hb]) (by simp [moveOffset]) ?_
    simp only [moveOffset]
    omega
  · intro j hj
    exact bound_cfg hin (by omega) (by omega)

/-- Appending zeros preserves the low bits and takes exactly five scans
of the original width plus five control transitions. -/
theorem executeWiden (word src dst out : List Bool) (input : Int)
    (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) (hlen : src.length = dst.length) :
    machine.BoundedSegment word (2 * dst.length + 1)
      (startConfig input src dst out) (stopConfig input src dst out) (5 * dst.length + 5) ∧
    machine.step word (stopConfig input src dst out) = none := by
  let w := dst.length
  let final := dst ++ List.replicate w false
  have hfinal : final.length = 2*w := by simp [final, w]; omega
  have e01 := fixed_step word input out src dst 0 1 0 0 0 1 .stay .right
    (by simp [machine]) (by simp [moveOffset]) (by simp [moveOffset])
  have hblank : counterTape 0 dst ((w : Int) + 1) = none := by
    simpa [w] using tape_end dst
  have e12 := fixed_step word input out src dst 1 2 0 (w+1) 1 (w+1) .right .stay
    (by simp [machine, hblank]) (by simp [moveOffset]) (by simp [moveOffset])
  have hturn : counterTape 0 src ((w : Int) + 1) = none := by
    simpa [w, hlen] using tape_end src
  have e23 := fixed_step word input out src final 2 3 (w+1) (2*w+1) w (2*w) .left .left
    (by simp [machine, hturn]) (by simp [moveOffset]) (by simp [moveOffset])
  have e34 := fixed_step word input out src final 3 4 0 (2*w) 0 (2*w) .stay .stay
    (by simp [machine]) (by simp [moveOffset]) (by simp [moveOffset])
  have e45 := fixed_step word input out src final 4 5 0 0 0 0 .stay .stay
    (by simp [machine]) (by simp [moveOffset]) (by simp [moveOffset])
  have b01 := segment_step (B := 2*w+1) e01 (bound_cfg hin (by omega) (by omega))
    (bound_cfg hin (by omega) (by omega))
  have b12 := segment_step (B := 2*w+1) e12 (bound_cfg hin (by omega) (by omega))
    (bound_cfg hin (by omega) (by omega))
  have b23 := segment_step (B := 2*w+1) e23 (bound_cfg hin (by omega) (by omega))
    (bound_cfg hin (by omega) (by omega))
  have b34 := segment_step (B := 2*w+1) e34 (bound_cfg hin (by omega) (by omega))
    (bound_cfg hin (by omega) (by omega))
  have b45 := segment_step (B := 2*w+1) e45 (bound_cfg hin (by omega) (by omega))
    (bound_cfg hin (by omega) (by omega))
  have run := BoundedSegment.append machine b01
    (BoundedSegment.append machine (seekRun word src dst out input hin)
      (BoundedSegment.append machine b12
        (BoundedSegment.append machine (fillRun word src dst out input hin hlen)
          (BoundedSegment.append machine b23
            (BoundedSegment.append machine (rewindSource word src final out input w hin hlen)
              (BoundedSegment.append machine b34
                (BoundedSegment.append machine (rewindTarget word src final out input w hin hfinal) b45)))))))
  refine ⟨?_, rfl⟩
  have lengths : 1 + (w + (1 + (w + (1 + (w + (1 + (2*w + 1))))))) = 5*w+5 := by omega
  simpa only [w, final, startConfig, stopConfig, hlen, lengths] using run

theorem encodeLabel_double {v w : ℕ} (cap : v < 2 ^ w) :
    encodeLabel w v ++ List.replicate w false = encodeLabel (2*w) v := by
  apply List.ext_getElem
  · simp [length_encodeLabel]
    omega
  · intro j hleft hright
    by_cases hj : j < w
    · rw [List.getElem_append_left (by simpa only [length_encodeLabel] using hj)]
      simp [encodeLabel]
    · have hle : w ≤ j := by omega
      rw [List.getElem_append_right (by simpa only [length_encodeLabel] using hle)]
      simp [encodeLabel, Nat.testBit_eq_false_of_lt (cap.trans_le (Nat.pow_le_pow_right (by decide) hle))]

/-- A numerical exit configuration on the same physical bank layout. -/
def stopLabelConfig (input : Int) (template out : List Bool) (w v : ℕ) : machine.Config :=
  cfg 5 0 0 input template (encodeLabel (2*w) v) out

/-- The physically widened register has an exact double-width numerical
encoding as well as the original template, unchanged. -/
theorem executeWidenLabel (word src out : List Bool) (input : Int) (w v : ℕ)
    (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) (hlen : src.length = w) (cap : v < 2 ^ w) :
    machine.BoundedSegment word (2*w + 1) (startConfig input src (encodeLabel w v) out)
      (stopLabelConfig input src out w v) (5*w+5) ∧
    machine.step word (stopLabelConfig input src out w v) = none := by
  have h := executeWiden word src (encodeLabel w v) out input hin (hlen.trans (length_encodeLabel _ _).symm)
  simpa only [stopConfig, stopLabelConfig, hlen, length_encodeLabel, encodeLabel_double cap] using h
end Mathproof.MinimumGeneration.TapeWiden
