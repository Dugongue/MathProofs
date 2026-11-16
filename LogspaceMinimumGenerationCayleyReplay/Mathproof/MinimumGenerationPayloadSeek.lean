import Mathproof.MinimumGenerationInputScan
import Mathproof.MinimumGenerationTapeCompose

namespace Mathproof.MinimumGeneration.PayloadSeek

open SearchTransducer
open Mathproof.Multitape.Locality (moveOffset)
open InputScan (headed read_headed_true read_headed_false headed_encodeCayley)

variable {W : Nat}

/-- Return to the left input endmarker, scan the unary header, and leave the
input head at the beginning of the table. No work tape or output is changed. -/
abbrev machine (W : Nat) : SearchTransducer where
  states := 3
  workTapes := W
  initialState := 0
  transition q input _ :=
    if q = 0 then
      match input with
      | .leftEnd => some (1, .right, fun _ => ⟨none, .stay⟩, none)
      | _ => some (0, .left, fun _ => ⟨none, .stay⟩, none)
    else if q = 1 then
      match input with
      | .data true => some (1, .right, fun _ => ⟨none, .stay⟩, none)
      | .data false => some (2, .right, fun _ => ⟨none, .stay⟩, none)
      | _ => none
    else none

def cfg (q : Fin 3) (p : Int) (h : Fin W → Int) (m : Fin W → Int → Option Bool)
    (prior : List Bool) : (machine W).Config :=
  ⟨q, p, h, m, prior⟩

private theorem left (word : List Bool) (p : Int) (hp : 0 ≤ p) (h : Fin W → Int)
    (m : Fin W → Int → Option Bool) (prior : List Bool) :
    (machine W).step word (cfg 0 p h m prior) = some (cfg 0 (p - 1) h m prior) := by
  cases hp' : word[p.toNat]? <;>
    simp [SearchTransducer.step, cfg, machine, readInput, Int.not_lt.mpr hp, hp', moveOffset,
      sub_eq_add_neg]
  all_goals
    funext i j
    exact ite_self _

private theorem turn (word : List Bool) (h : Fin W → Int) (m : Fin W → Int → Option Bool)
    (prior : List Bool) :
    (machine W).step word (cfg 0 (-1) h m prior) = some (cfg 1 0 h m prior) := by
  simp [SearchTransducer.step, cfg, machine, readInput, moveOffset]
  funext i j
  exact ite_self _

private theorem scan_true (word : List Bool) (p : Nat)
    (hp : readInput word (p : Int) = .data true)
    (h : Fin W → Int) (m : Fin W → Int → Option Bool) (prior : List Bool) :
    (machine W).step word (cfg 1 p h m prior) = some (cfg 1 (p + 1 : Nat) h m prior) := by
  simp [SearchTransducer.step, cfg, machine, hp, moveOffset]
  funext i j
  exact ite_self _

private theorem scan_false (word : List Bool) (p : Nat)
    (hp : readInput word (p : Int) = .data false)
    (h : Fin W → Int) (m : Fin W → Int → Option Bool) (prior : List Bool) :
    (machine W).step word (cfg 1 p h m prior) = some (cfg 2 (p + 1 : Nat) h m prior) := by
  simp [SearchTransducer.step, cfg, machine, hp, moveOffset]
  funext i j
  exact ite_self _

private theorem prefix_left (word : List Bool) (p k : Nat) (hk : k ≤ p + 1)
    (h : Fin W → Int) (m : Fin W → Int → Option Bool) (prior : List Bool) :
    (machine W).runFrom word (cfg 0 p h m prior) k = some (cfg 0 ((p : Int) - k) h m prior) := by
  induction k with
  | zero => simp [runFrom]
  | succ k ih =>
    rw [runFrom, ih (by omega), Option.bind_some]
    have he : (p : Int) - (↑(k + 1) : Int) = ((p : Int) - k) - 1 := by omega
    rw [he]
    exact left word ((p : Int) - k) (by omega) h m prior

private theorem prefix_header (n k : Nat) (hk : k ≤ n) (body : List Bool)
    (h : Fin W → Int) (m : Fin W → Int → Option Bool) (prior : List Bool) :
    (machine W).runFrom (headed n body) (cfg 1 0 h m prior) k =
      some (cfg 1 k h m prior) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runFrom, ih (by omega), Option.bind_some]
    exact scan_true (headed n body) k (read_headed_true n k body (by omega)) h m prior

theorem executeHeaded {B : Nat} (n p : Nat) (body : List Bool)
    (h : Fin W → Int) (m : Fin W → Int → Option Bool) (prior : List Bool)
    (hp : p ≤ (headed n body).length) (hb : ∀ i, (h i).natAbs ≤ B) :
    (machine W).BoundedSegment (headed n body) B (cfg 0 p h m prior) (cfg 2 (n + 1 : Nat) h m prior)
      (p + 2 + n + 1) ∧
    (machine W).step (headed n body) (cfg 2 (n + 1 : Nat) h m prior) = none := by
  let word := headed n body
  have hp' : p ≤ word.length := hp
  have ht : (machine W).runFrom word (cfg 0 p h m prior) (p + 2) = some (cfg 1 0 h m prior) := by
    rw [show p + 2 = p + 1 + 1 by omega, runFrom, prefix_left word p (p + 1) le_rfl h m prior,
      Option.bind_some, show (p : Int) - (↑(p + 1) : Int) = -1 by omega]
    exact turn word h m prior
  have hn : n + 1 ≤ word.length := by simp [word, headed]
  have hr : (machine W).runFrom word (cfg 0 p h m prior) (p + 2 + n + 1) =
      some (cfg 2 (n + 1 : Nat) h m prior) := by
    rw [runFrom, runFrom_add, ht, Option.bind_some, prefix_header n n le_rfl body h m prior,
      Option.bind_some]
    exact scan_false word n (read_headed_false n body) h m prior
  refine ⟨⟨hr, ?_⟩, by simp [SearchTransducer.step, cfg, machine]⟩
  intro k hk c hc
  by_cases hcl : k ≤ p + 1
  · rw [prefix_left word p k hcl h m prior] at hc
    cases hc
    exact ⟨by change (-1 : Int) ≤ (p : Int) - k; omega,
      by change (p : Int) - k ≤ (word.length : Int); omega, hb⟩
  by_cases hfinal : k = p + 2 + n + 1
  · rw [hfinal, hr] at hc
    cases hc
    exact ⟨by change (-1 : Int) ≤ (↑(n + 1) : Int); omega,
      by change (↑(n + 1) : Int) ≤ (word.length : Int); omega, hb⟩
  let j := k - (p + 2)
  have he : k = p + 2 + j := by dsimp [j]; omega
  have hj : j ≤ n := by dsimp [j]; omega
  rw [he, runFrom_add, ht, Option.bind_some, prefix_header n j hj body h m prior] at hc
  cases hc
  exact ⟨by change (-1 : Int) ≤ (j : Int); omega,
    by change (j : Int) ≤ (word.length : Int); omega, hb⟩

/-- The raw Cayley-table interface, with all caller banks parked. -/
theorem executeCayley {B : Nat} (n p : Nat) (M : Mul (Fin n)) (h : Fin W → Int)
    (m : Fin W → Int → Option Bool) (prior : List Bool)
    (hp : p ≤ (@encodeCayley n M).length) (hb : ∀ i, (h i).natAbs ≤ B) :
    (machine W).BoundedSegment (@encodeCayley n M) B (cfg 0 p h m prior)
      (cfg 2 (n + 1 : Nat) h m prior) (p + 2 + n + 1) ∧
    (machine W).step (@encodeCayley n M) (cfg 2 (n + 1 : Nat) h m prior) = none := by
  obtain ⟨body, hword⟩ := @headed_encodeCayley n M
  rw [hword] at hp ⊢
  exact executeHeaded n p body h m prior hp hb

end Mathproof.MinimumGeneration.PayloadSeek
