import EvenPhysicalAction
import Mathlib.Algebra.Group.Subgroup.Basic

namespace EvenTI.Action

variable {K : Type*} [Field K] {d n : Nat}

/-- The subgroup of tuples whose physical mode maps are all scalars. -/
def scalarMap : (Fin d → Kˣ) →* Changes K d n where
  toFun := scalars
  map_one' := by
    funext i
    change (Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom (1 : Kˣ)) = 1
    exact map_one _
  map_mul' u v := by
    funext i
    change (Units.map _ (u i * v i)) = Units.map _ (u i) * Units.map _ (v i)
    rw [map_mul]

theorem scalarMap_mem_range {a : Changes K d n} :
    a ∈ (scalarMap (K := K) (d := d) (n := n)).range ↔ ∃ u, a = scalars u := by
  change (∃ u, scalars u = a) ↔ _
  simp only [eq_comm]

/-- A complete self-comparison pass covers the stabilizer by cosets. For
each successful branch it suffices to test one representative and a
generating set of its homogeneous subgroup. -/
theorem scalarOnly_of_branch_generators
    {T : Tensor K d n} {J : Type*}
    (representative : J → Changes K d n) (generators : J → Set (Changes K d n))
    (cover : ∀ a, act a T = T → ∃ j u, u ∈ Subgroup.closure (generators j) ∧
      a = representative j * u)
    (hRep : ∀ j, ∃ u, representative j = scalars u)
    (hGen : ∀ j a, a ∈ generators j → ∃ u, a = scalars u) :
    ∀ a, act a T = T → ∃ u, a = scalars u := by
  intro a ha
  obtain ⟨j, x, hx, rfl⟩ := cover a ha
  apply scalarMap_mem_range.mp
  exact Subgroup.mul_mem _
    (scalarMap_mem_range.mpr (hRep j))
    (((Subgroup.closure_le _).mpr fun y hy => scalarMap_mem_range.mpr (hGen j y hy)) hx)

#print axioms scalarOnly_of_branch_generators

end EvenTI.Action
