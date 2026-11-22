import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

theorem exists_global_of_many_probes {ι P : Type*} [DecidableEq P]
    (systems : Finset ι) (successes : ι → Finset P) (globalSolution : ι → Prop)
    (budget : ι → ℕ)
    (bound : ∀ i ∈ systems, ¬ globalSolution i → (successes i).card ≤ budget i)
    (many : (systems.biUnion successes).card > ∑ i ∈ systems, budget i) :
    ∃ i ∈ systems, globalSolution i := by
  classical
  by_contra h
  have each : ∀ i ∈ systems, (successes i).card ≤ budget i :=
    fun i hi => bound i hi (fun hg => h ⟨i, hi, hg⟩)
  exact (not_lt_of_ge (Finset.card_biUnion_le.trans (Finset.sum_le_sum each))) many
