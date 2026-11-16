import Mathproof.MinimumGenerationGreedyOrdinal
import Mathproof.MinimumGenerationResidualExecution

namespace Mathproof.MinimumGenerationResidual.GreedyReplay

open Mathproof.MinimumGeneration
open TowerReplay Subgroup

variable {n : Nat}

def generatorList (query : (Fin n → Bool) → Fin n → Bool)
    (eligible : Nat → Fin n → Fin n → Bool) (level : Nat) (x : Fin n) : List (Fin n) :=
  GreedyOrdinal.collect (GreedyGenerator.accept query (eligible level x)) 0 n

/-- The tower's child operation asks for a single greedy generator ordinal.
No computation of the specification list is used by this implementation. -/
def child (query : (Fin n → Bool) → Fin n → Bool)
    (eligible : Nat → Fin n → Fin n → Bool) : Child :=
  fun level x j =>
    if hx : x < n then
      (GreedyOrdinal.ordinal (GreedyGenerator.accept query (eligible level ⟨x,hx⟩)) 0 n j).map Fin.val
    else if j = 0 then some n else none

theorem child_eq (query : (Fin n → Bool) → Fin n → Bool)
    (eligible : Nat → Fin n → Fin n → Bool) :
    child query eligible = rawResidualChild n (generatorList query eligible) := by
  funext l x j
  unfold child rawResidualChild
  split
  · rename_i hx
    rw [GreedyOrdinal.ordinal_exact]
    rfl
  · rename_i hx
    rfl

/-- A greedy ordinal query suffices for the checked radical–socle replay. The
radix is logarithmic in the group order. Residual membership and subgroup
membership are the source calls supplied to the executable controller. -/
theorem replay {query : (Fin n → Bool) → Fin n → Bool} [Group (Fin n)]
    (correct : ChiefExecution.CorrectMembership query)
    (K : Nat → Subgroup (Fin n)) [∀ l, (K l).Normal] (hZero : K 0 = ⊥)
    (mode : Nat → Bool) (eligible : Nat → Fin n → Fin n → Bool)
    (hEligible : ∀ l x y, eligible l x y = true ↔ y ∈ sourceResidual (mode l) x)
    (hLayer : ∀ l (x : Fin n), x ∈ K (l+1) ↔
      if mode (l+1) then QuotientGroup.mk' (K l) x ∈ socle (Fin n ⧸ K l)
      else QuotientGroup.mk' (K l) x ∈ solvableRadical (Fin n ⧸ K l))
    (hFree : ∀ l, mode (l+1) = true → solvableRadical (Fin n ⧸ K l) = ⊥)
    (l x : Nat) :
    let radix := Nat.log2 n + 1
    ∃ answer, ControlRuns (child query eligible) (rawResidualBase n) radix l x
        (.scan (radix ^ l) 0) (.halt answer) ∧
      controlStep (child query eligible) (rawResidualBase n) radix l x (.halt answer) = none ∧
      (answer = true ↔ rawKernelMember n K l x) := by
  let radix := Nat.log2 n + 1
  let gen := generatorList query eligible
  have hLen (i : Nat) (y : Fin n) : (gen i y).length ≤ radix :=
    (GreedyOrdinal.collect_log_length correct (eligible i y)).trans (Nat.le_succ _)
  have hGen (i : Nat) (y : Fin n) :
      closure {a | a ∈ gen (i+1) y} = sourceResidual (mode (i+1)) y := by
    change closure {a | a ∈ GreedyOrdinal.collect
      (GreedyGenerator.accept query (eligible (i+1) y)) 0 n} = _
    rw [GreedyOrdinal.collect_closure correct]
    have hSet : {a | eligible (i+1) y a = true} = (sourceResidual (mode (i+1)) y : Set (Fin n)) := by
      ext a
      exact hEligible (i+1) y a
    rw [hSet, closure_eq]
  have h := replay_halts_with_kernel_membership n radix (by dsimp [radix]; omega)
    K hZero mode gen hLen hGen hLayer hFree l x
  simpa only [child_eq] using h

end Mathproof.MinimumGenerationResidual.GreedyReplay
