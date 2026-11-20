import EvenP6CellsCompute

/-! Size bounds for the actual fixed-space refinement states. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open Module

variable {K A : Type} [Field K] [Fintype K] [DecidableEq K]
  [CommRing A] [Algebra K A] [DecidableEq A] {d : ℕ}

theorem rawCells_prefix_length_le
    (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K)) (k : ℕ) :
    (run enum ((rawFixed C).take k) (if (1 : A) = 0 then [] else [1])).length ≤ d := by
  have hstart : IsPartition (if (1 : A) = 0 then ([] : List A) else [1]) := by
    by_cases h : (1 : A) = 0 <;> simp [h, IsPartition]
  have hp := run_partition enum ((rawFixed C).take k)
    (fun x hx => rawFixed_mem C (List.mem_of_mem_take hx)) hstart
  letI : Module.Finite K A := Module.Finite.of_basis (Basis.ofEquivFun C)
  have hr := partition_length_le (K := K) hp
  rw [C.finrank_eq] at hr
  simpa using hr

theorem single_refinement_candidates_le (enum : Fin (Fintype.card K) ≃ K) (x : A)
    (es : List A) : (refine enum x es).length ≤ es.length * Fintype.card K := by
  unfold refine
  induction es with
  | nil => simp
  | cons e es ih =>
    have hp : (pieces enum x e).length ≤ Fintype.card K := by
      unfold pieces
      simpa only [List.length_ofFn] using List.length_filter_le
        (fun z => decide (z ≠ 0)) (List.ofFn fun i => e * projector x (enum i))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    simpa only [Nat.add_comm] using Nat.add_le_add hp ih

#print axioms rawCells_prefix_length_le
#print axioms single_refinement_candidates_le

end EvenTI.CellProducer
