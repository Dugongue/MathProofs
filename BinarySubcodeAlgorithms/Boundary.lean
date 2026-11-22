import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace BinarySubcode

theorem zero_iff_cut_intersections {K M ι : Type*} [Field K]
    [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι]
    (v : ι → M) (U : Finset ι → Submodule K M)
    (local_mem : ∀ s i, i ∈ s → v i ∈ U s) (empty : U ∅ = ⊥) :
    (∑ i, v i) = 0 ↔ ∀ s : Finset ι,
      (∑ i ∈ s, v i) ∈ U s ⊓ U (Finset.univ \ s) := by
  have partial_mem (s : Finset ι) : (∑ i ∈ s, v i) ∈ U s :=
    (U s).sum_mem (fun i hi => local_mem s i hi)
  constructor
  · intro zero s
    refine ⟨partial_mem s, ?_⟩
    have split : (∑ i ∈ Finset.univ \ s, v i) + (∑ i ∈ s, v i) = 0 := by
      rw [Finset.sum_sdiff s.subset_univ, zero]
    have negated : (∑ i ∈ s, v i) = -(∑ i ∈ Finset.univ \ s, v i) :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using split)
    rw [negated]
    exact Submodule.neg_mem _ (partial_mem (Finset.univ \ s))
  · intro cuts
    have h := (cuts Finset.univ).2
    simpa [empty] using h

end BinarySubcode
