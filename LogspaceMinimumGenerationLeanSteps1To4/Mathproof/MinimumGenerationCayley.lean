import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Group.Subgroup.Map

namespace Mathproof.MinimumGeneration

variable {G : Type*} [Group G]

/-- Left multiplication preserves the graph with right-multiplication edges. -/
def cayleyLeftHom (S : Set G) (a : G) : SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S where
  toFun x := a * x
  map_rel' := by
    intro x y h
    rw [SimpleGraph.mulCayley_adj] at h ⊢
    rcases h with ⟨hne, hs⟩
    exact ⟨fun he => hne (mul_left_cancel he), by
      simpa [mul_inv_rev, mul_assoc] using hs⟩

/-- A Cayley edge exposes an actual generator or inverse for a streamed word. -/
theorem cayley_adj_has_label (S : Set G) {x y : G} (h : (SimpleGraph.mulCayley S).Adj x y) :
    ∃ z ∈ S, x * z = y ∨ x * z⁻¹ = y := by
  rcases (SimpleGraph.mulCayley_adj S x y).1 h with ⟨_, hx | hy⟩
  · exact ⟨x⁻¹ * y, hx, Or.inl (by simp [← mul_assoc])⟩
  · exact ⟨y⁻¹ * x, hy, Or.inr (by simp [mul_inv_rev, ← mul_assoc])⟩

/-- Undirected Cayley reachability is precisely subgroup generation. -/
theorem cayley_reachable_iff_mem_closure (S : Set G) (g : G) :
    (SimpleGraph.mulCayley S).Reachable 1 g ↔ g ∈ Subgroup.closure S := by
  constructor
  · rw [SimpleGraph.reachable_iff_reflTransGen]
    intro h
    induction h with
    | refl => exact Subgroup.one_mem _
    | tail _ hxy ih =>
      obtain ⟨z, hz, hr | hr⟩ := cayley_adj_has_label S hxy
      · rw [← hr]
        exact Subgroup.mul_mem _ ih (Subgroup.subset_closure hz)
      · rw [← hr]
        exact Subgroup.mul_mem _ ih (Subgroup.inv_mem _ (Subgroup.subset_closure hz))
  · intro hg
    refine Subgroup.closure_induction (p := fun x _ => (SimpleGraph.mulCayley S).Reachable 1 x)
      ?_ SimpleGraph.Reachable.rfl ?_ ?_ hg
    · intro x hx
      by_cases he : x = 1
      · subst x
        exact SimpleGraph.Reachable.rfl
      · apply SimpleGraph.Adj.reachable
        exact (SimpleGraph.mulCayley_adj S 1 x).2 ⟨(fun h => he h.symm), Or.inl (by simpa using hx)⟩
    · intro x y _ _ hrx hry
      apply hrx.trans
      simpa [cayleyLeftHom] using hry.map (cayleyLeftHom S x)
    · intro x _ h
      simpa [cayleyLeftHom] using h.symm.map (cayleyLeftHom S x⁻¹)

end Mathproof.MinimumGeneration
