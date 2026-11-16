import Mathproof.MinimumGenerationBipartiteRawQuery
import Mathproof.MinimumGenerationTapeInstall
import Mathproof.MinimumGenerationTapeWiden
import Mathproof.MinimumGenerationTapeAddition

namespace Mathproof.MinimumGeneration.PhysicalGreedyHeader

open SearchTransducer
open InputPosition (work)

variable {W : Nat}

def width (n : Nat) := 4 * TableIO.width n

def graphOrder (n : Nat) := n+n

def header (n s t : Nat) := graphOrder n + s + t + 3

def markers (n s t : Nat) (j : Fin 5) : Nat :=
  if j = 0 then 0
  else if j = 1 then graphOrder n + 1
  else if j = 2 then graphOrder n + s + 2
  else if j = 3 then header n s t
  else header n s t + graphOrder n * graphOrder n + 1

theorem header_eq {n : Nat} (id x : Fin n) :
    header n id.val x.val = Connectivity.ustconHeaderLength
      (BipartiteCayley.left id) (BipartiteCayley.left x) := rfl

theorem end_eq {n : Nat} (id x : Fin n)
    (bits : Connectivity.AdjBits (Fin (n+n))) :
    markers n id.val x.val 4 =
      (Connectivity.ustconWord bits (BipartiteCayley.left id) (BipartiteCayley.left x)).length + 1 := by
  rw [Connectivity.ustconWord_length]
  rfl

theorem virtualFit {n s t : Nat} (hs : s < n) (ht : t < n) :
    markers n s t 4 < 2 ^ width n := by
  let q := 2 ^ TableIO.width n
  have nlt : n < q := Nat.lt_log2_self
  have q2 : 2 ≤ q := by omega
  have hq : 4 * (q : Int)^2 ≤ (q : Int)^4 := by
    have h0 : 0 ≤ (q : Int)^2 := sq_nonneg _
    have h1 : 4 ≤ (q : Int)^2 := by
      have z : 2 ≤ (q : Int) := by exact_mod_cast q2
      nlinarith [mul_nonneg (show 0 ≤ (q : Int) - 2 by omega) (show 0 ≤ (q : Int)+2 by omega)]
    nlinarith [mul_nonneg h0 (show 0 ≤ (q : Int)^2 - 4 by omega)]
  have hm : (markers n s t 4 : Int) < 4*(q : Int)^2 := by
    change ((header n s t + (n+n)*(n+n)+1 : Nat) : Int) < _
    simp only [header, graphOrder, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have z : (n : Int) + 1 ≤ q := by exact_mod_cast nlt
    have z₀ : 0 ≤ (q : Int) - n - 1 := by omega
    have z₁ : 0 ≤ (q : Int) + n + 1 := by omega
    have zz : 0 ≤ ((q : Int) - n - 1) * ((q : Int) + n + 1) := mul_nonneg z₀ z₁
    have hs' : (s : Int) < n := by exact_mod_cast hs
    have ht' : (t : Int) < n := by exact_mod_cast ht
    nlinarith
  have he : 2 ^ width n = q^4 := by
    unfold width q
    rw [Nat.mul_comm 4, Nat.pow_mul]
  rw [he]
  exact_mod_cast hm.trans_le hq

theorem registerFit {n s t : Nat} (hs : s < n) (ht : t < n) :
    (∀ j, markers n s t j < 2 ^ width n) ∧
    graphOrder n < 2 ^ width n ∧ header n s t + 1 < 2 ^ width n := by
  have main := virtualFit hs ht
  have hEnd : markers n s t 4 =
      header n s t + graphOrder n * graphOrder n + 1 := rfl
  rw [hEnd] at main
  refine ⟨?_, ?_, by omega⟩
  · intro j
    fin_cases j <;> simp [markers, header, graphOrder] at * <;> omega
  · dsimp [header, graphOrder] at *
    omega

/-- Register values reused across all candidate queries of this source. -/
def fixed (n id : Nat) (j : Fin 8) : Nat :=
  if j = 0 then 0 else if j = 1 then 1 else if j = 2 then graphOrder n
  else if j = 3 then graphOrder n+1 else if j = 4 then graphOrder n+id+2
  else if j = 5 then header n id 0
  else if j = 6 then header n id 0 + graphOrder n * graphOrder n + 1
  else header n id 0+1

theorem after_add (n id x : Nat) :
    fixed n id 5 + x = markers n id x 3 ∧
    fixed n id 6 + x = markers n id x 4 ∧
    fixed n id 7 + x = header n id x + 1 := by
  simp [fixed, markers, header, graphOrder] <;> omega

theorem register_work (w v : Nat) :
    TapeAddition.register w v = work (encodeLabel w v) := by
  funext p
  unfold TapeAddition.register work
  by_cases hp : p < 1
  · have h0 : p ≤ 0 := by omega
    rw [if_pos hp, if_pos h0]
  · have h0 : ¬ p ≤ 0 := by omega
    rw [if_neg hp, if_neg h0]

theorem encodeLabel_four {v w : Nat} (cap : v < 2 ^ w) :
    encodeLabel w v ++ List.replicate (3*w) false = encodeLabel (4*w) v := by
  have cap' : v < 2 ^ (2*w) := cap.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have one := TapeWiden.encodeLabel_double cap
  have two := TapeWiden.encodeLabel_double cap'
  rw [show 4*w = 2*(2*w) by omega, ← two, ← one, List.append_assoc, ← List.replicate_add]
  congr 2
  omega

/-- Installing the low columns into a cleared wide register preserves its high
zero extension. Copier sources remain unchanged. -/
theorem installLow {n x : Nat} (fit : x < 2 ^ TableIO.width n)
    (dst src : Fin W) (pick : Fin W → Option (Fin W))
    (select : pick dst = some src) (cells : Fin W → Int → Option Bool)
    (low : cells src = work (encodeLabel (TableIO.width n) x))
    (zero : cells dst = work (encodeLabel (width n) 0)) :
    TapeInstall.installed pick cells (TableIO.width n) dst = work (encodeLabel (width n) x) := by
  let w := TableIO.width n
  have high : encodeLabel (width n) 0 = encodeLabel w 0 ++ List.replicate (3*w) false :=
    (encodeLabel_four (Nat.two_pow_pos w)).symm
  have target : encodeLabel (width n) x = encodeLabel w x ++ List.replicate (3*w) false :=
    (encodeLabel_four fit).symm
  funext p
  simp only [TapeInstall.installed, select, Option.elim_some, low, zero, high, target]
  by_cases h : 1 ≤ p ∧ p ≤ (w : Int)
  · rw [if_pos h]
    simp only [Option.elim_some, work, if_neg (show ¬ p ≤ 0 by omega)]
    rw [List.getElem?_append_left (by simp only [length_encodeLabel]; omega)]
  · rw [if_neg h]
    by_cases lp : p ≤ 0
    · simp [work, lp]
    · have right : w ≤ (p - 1).toNat := by omega
      simp only [work, if_neg lp]
      rw [List.getElem?_append_right (by simpa only [length_encodeLabel] using right),
        List.getElem?_append_right (by simpa only [length_encodeLabel] using right)]
      simp only [length_encodeLabel]

end Mathproof.MinimumGeneration.PhysicalGreedyHeader
