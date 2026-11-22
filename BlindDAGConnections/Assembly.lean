import Mathlib.Topology.NoetherianSpace
import Mathlib.GroupTheory.GroupAction.Defs
import Mathproof.SymplecticTI

namespace BlindAssembly

open Set TopologicalSpace

theorem finite_closed_tests {X ι : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (C : ι → Set X) (closed : ∀ i, IsClosed (C i)) :
    ∃ t : Finset ι, ∀ x, (∀ i, x ∈ C i) ↔ ∀ i ∈ t, x ∈ C i := by
  classical
  let U : ι → Set X := fun i => (C i)ᶜ
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (⋃ i, U i)).elim_finite_subcover
    U (fun i => (closed i).isOpen_compl) (Subset.rfl)
  refine ⟨t, fun x => ⟨fun h i _ => h i, ?_⟩⟩
  intro h i
  by_contra hx
  have hxU : x ∈ ⋃ j, U j := mem_iUnion.mpr ⟨i, hx⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (ht hxU)
  obtain ⟨hjt, hjx⟩ := mem_iUnion.mp hj
  exact hjx (h j hjt)

theorem finite_reduction_tests {X ι : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (R : Mathproof.SymplecticTI.ReductionSystem X) (src : ι → X)
    (closed : ∀ i, IsClosed {x | R.reduces (src i) x}) :
    ∃ t : Finset ι, ∀ x, (∀ i, R.reduces (src i) x) ↔
      ∀ i ∈ t, R.reduces (src i) x :=
  finite_closed_tests (fun i => {x | R.reduces (src i) x}) closed

theorem finite_common_degenerations {X G ι : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [Group G] [MulAction G X] (src : ι → X) :
    ∃ t : Finset ι, ∀ x, (∀ i, x ∈ closure (MulAction.orbit G (src i))) ↔
      ∀ i ∈ t, x ∈ closure (MulAction.orbit G (src i)) :=
  finite_closed_tests (fun i => closure (MulAction.orbit G (src i)))
    (fun _ => isClosed_closure)

end BlindAssembly
