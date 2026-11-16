import Mathproof.MinimumGenerationPayloadSeek

namespace Mathproof.MinimumGeneration.PayloadSeek

open SearchTransducer
open Mathproof.Multitape.Locality (moveOffset)

/-- Seek to the table payload from anywhere on the physical input, including
either endmarker. The cases share the existing finite seek machine. -/
theorem executeFrom {W B n : Nat} (p : Int) (M : Mul (Fin n)) (h : Fin W → Int)
    (m : Fin W → Int → Option Bool) (prior : List Bool)
    (bp : (-1 : Int) ≤ p ∧ p ≤ (@encodeCayley n M).length)
    (bh : ∀ i, (h i).natAbs ≤ B) :
    let word := @encodeCayley n M
    ∃ k, (machine W).BoundedSegment word B (cfg 0 p h m prior)
      (cfg 2 (n+1 : Nat) h m prior) k ∧
      (machine W).step word (cfg 2 (n+1 : Nat) h m prior) = none := by
  let word := @encodeCayley n M
  by_cases pos : 0 ≤ p
  · have fromNat : (p.toNat : Int) = p := Int.toNat_of_nonneg pos
    have fits : p.toNat ≤ (@encodeCayley n M).length := by omega
    have worked := executeCayley (B := B) n p.toNat M h m prior fits bh
    rw [fromNat] at worked
    exact ⟨_, worked⟩
  · have atLeft : p = -1 := by omega
    subst p
    let start := cfg 0 (0 : Int) h m prior
    let left := cfg 0 (-1 : Int) h m prior
    let finish := cfg 2 (n+1 : Nat) h m prior
    have first : (machine W).runFrom word start 1 = some left := by
      change (machine W).step word start = some left
      cases r : word[0]? <;>
        simp [SearchTransducer.step,start,left,cfg,machine,readInput,r,moveOffset]
      all_goals funext i j; exact ite_self _
    obtain ⟨long, stop⟩ := executeCayley (B := B) n 0 M h m prior (by omega) bh
    have exactLen : 0 + 2 + n + 1 = 1 + (n + 2) := by omega
    rw [exactLen] at long
    have reaches := long.1
    change (machine W).runFrom word start (1 + (n+2)) = some finish at reaches
    rw [runFrom_add, first, Option.bind_some] at reaches
    refine ⟨n+2, ⟨reaches, ?_⟩, stop⟩
    intro k hk c row
    apply long.2 (1+k) (by omega) c
    change (machine W).runFrom word start (1+k) = _
    rw [runFrom_add, first, Option.bind_some]
    exact row

end Mathproof.MinimumGeneration.PayloadSeek
