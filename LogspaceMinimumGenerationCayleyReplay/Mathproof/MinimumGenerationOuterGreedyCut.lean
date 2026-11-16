import Mathproof.MinimumGenerationOuterCayleyQuery
import Mathproof.MinimumGenerationGreedyGenerator

namespace Mathproof.MinimumGeneration.OuterCayleyQuery

open BipartiteCayley

variable {G : Type*} [Group G]

private def cayleyShift (S : Set G) (a : G) :
    SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S where
  toFun x := a * x
  map_rel' := by
    intro x y h
    rw [SimpleGraph.mulCayley_adj] at h ⊢
    obtain ⟨hne, h⟩ := h
    have one : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by simp [mul_assoc]
    have two : (a * y)⁻¹ * (a * x) = y⁻¹ * x := by simp [mul_assoc]
    exact ⟨fun e => hne (mul_left_cancel e), by simpa only [one,two] using h⟩

theorem reachable_iff_quotient_mem (S : Set G) (x y : G) :
    (graph S).Reachable (.inl x) (.inl y) ↔ x⁻¹ * y ∈ Subgroup.closure S := by
  rw [reachable_iff, ← cayley_reachable_iff_mem_closure]
  constructor
  · intro h
    simpa [cayleyShift] using h.map (cayleyShift S x⁻¹)
  · intro h
    simpa [cayleyShift, ← mul_assoc] using h.map (cayleyShift S x)

variable {n : Nat} [Group (Fin n)]

/-- Recompute a greedy prefix subgroup using every eligible label below the
same cutoff. Connectivity results are unchanged for every pair of endpoints. -/
theorem reachable_greedyPrefix_iff {query : (Fin n → Bool) → Fin n → Bool}
    (correct : ChiefExecution.CorrectMembership query) (eligible : Fin n → Bool)
    (cut : Nat) (x y : Fin n) :
    (graph {a | GreedyGenerator.accept query eligible a = true ∧ a.val < cut}).Reachable
        (.inl x) (.inl y) ↔
      (graph {a | eligible a = true ∧ a.val < cut}).Reachable (.inl x) (.inl y) := by
  rw [reachable_iff_quotient_mem, reachable_iff_quotient_mem,
    GreedyGenerator.closure_accept_prefix correct eligible cut]

end Mathproof.MinimumGeneration.OuterCayleyQuery
