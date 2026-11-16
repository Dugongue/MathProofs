import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Mathproof.MinimumGeneration

open Subgroup

variable {G : Type*} [Group G]

/-- If a subgroup supplements a normal subgroup inside A, its intersection with A
supplements that same subgroup in A. -/
theorem inf_sup_eq_of_normal_supplement (H A J : Subgroup G) [J.Normal]
    (hJA : J ≤ A) (h : H ⊔ J = ⊤) : (H ⊓ A) ⊔ J = A := by
  apply le_antisymm (sup_le inf_le_right hJA)
  intro x hx
  have hx' : x ∈ H ⊔ J := by rw [h]; exact mem_top x
  obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_of_normal_right.mp hx'
  have hyA : y ∈ A := by
    have hmul : x * z⁻¹ ∈ A := A.mul_mem hx (A.inv_mem (hJA hz))
    have heq : x * z⁻¹ = y := by rw [← hyz, mul_inv_cancel_right]
    rwa [heq] at hmul
  exact mem_sup_of_normal_right.mpr ⟨y, ⟨hy, hyA⟩, z, hz, hyz⟩

/-- A characteristic subgroup of a normal subgroup remains normal in the whole group. -/
theorem normal_map_subtype_of_characteristic (A : Subgroup G) [A.Normal]
    (J : Subgroup A) [J.Characteristic] : (J.map A.subtype).Normal := by
  constructor
  intro x hx g
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  refine mem_map.mpr ⟨MulAut.conjNormal g y, ?_, MulAut.conjNormal_apply g y⟩
  apply characteristic_iff_map_le.mp (inferInstance : J.Characteristic) (MulAut.conjNormal g)
  exact mem_map.mpr ⟨y, hy, rfl⟩

/-- The Frattini subgroup of a normal subgroup embeds in the ambient Frattini subgroup. -/
theorem frattini_map_normal_le (A : Subgroup G) [A.Normal]
    [IsCoatomic (Subgroup A)] : (frattini A).map A.subtype ≤ frattini G := by
  let J := (frattini A).map A.subtype
  have : J.Normal := normal_map_subtype_of_characteristic A (frattini A)
  have hJA : J ≤ A := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx
    exact y.property
  change J ≤ Order.radical (Subgroup G)
  simp only [Order.radical, le_iInf_iff, Set.mem_ofPred_eq]
  intro M hM
  by_contra hn
  have hsup : M ⊔ J = ⊤ := hM.2 (M ⊔ J) (lt_of_le_of_ne le_sup_left (fun he => hn (le_sup_right.trans he.symm.le)))
  have hinf : (M ⊓ A) ⊔ J = A := inf_sup_eq_of_normal_supplement M A J hJA hsup
  have hj : J.subgroupOf A = frattini A :=
    comap_map_eq_self_of_injective A.subtype_injective _
  have hsub : (M ⊓ A).subgroupOf A = M.subgroupOf A := by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.property⟩⟩
  have hs : M.subgroupOf A ⊔ frattini A = ⊤ := by
    rw [← hj, ← hsub, ← subgroupOf_sup inf_le_right hJA, hinf, subgroupOf_self]
  have hAM : A ≤ M := by
    intro x hx
    change (⟨x, hx⟩ : A) ∈ M.subgroupOf A
    rw [frattini_nongenerating hs]
    exact mem_top _
  exact hn (hJA.trans hAM)

/-- A quotient by a Frattini subgroup reflects generation of arbitrary sets. -/
theorem closure_quotient_eq_top_iff (J : Subgroup G) [J.Normal]
    [IsCoatomic (Subgroup G)] (hJ : J ≤ frattini G) (s : Set G) :
    closure ((QuotientGroup.mk' J) '' s) = ⊤ ↔ closure s = ⊤ := by
  rw [← MonoidHom.map_closure]
  constructor
  · intro h
    have hsup : closure s ⊔ J = ⊤ := by
      rw [← QuotientGroup.ker_mk' J, ← comap_map_eq, h, comap_top]
    apply frattini_nongenerating
    exact top_unique (hsup ▸ sup_le_sup_left hJ (closure s))
  · intro h
    rw [h, map_top_of_surjective _ (QuotientGroup.mk'_surjective J)]

end Mathproof.MinimumGeneration
