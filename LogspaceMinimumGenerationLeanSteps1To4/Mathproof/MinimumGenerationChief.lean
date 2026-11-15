import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

namespace Mathproof.MinimumGeneration

open Subgroup
variable {G : Type*} [Group G]

/-- A strict prefix change is a chief step if all the elements with strictly
smaller principal normal closures have already been included. -/
theorem chief_step_of_principalClosure_scan (K N L : Subgroup G)
    [N.Normal] [L.Normal]
    (earlier : ∀ z : G, z ∈ N → normalClosure {z} < N → z ∈ K)
    (hKL : K < L) (hLK : L < K ⊔ N) : False := by
  classical
  have hex : ∃ y : G, y ∈ L ∧ y ∉ K := by
    by_contra! h
    exact hKL.not_ge (fun y hy => h y hy)
  obtain ⟨x, hxL, hxK⟩ := hex
  obtain ⟨y, hyK, z, hzN, hprod⟩ := mem_sup_of_normal_right.mp (hLK.le hxL)
  have hyL := hKL.le hyK
  have hzL : z ∈ L := by
    have h := L.mul_mem (L.inv_mem hyL) hxL
    rw [← hprod, inv_mul_cancel_left] at h
    exact h
  have hzClosure : normalClosure ({z} : Set G) ≤ L ⊓ N :=
    le_inf (normalClosure_le_normal (Set.singleton_subset_iff.mpr hzL))
      (normalClosure_le_normal (Set.singleton_subset_iff.mpr hzN))
  have hlt : L ⊓ N < N := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro h
    have hNL : N ≤ L := by rw [← h]; exact inf_le_left
    exact hLK.not_ge (sup_le hKL.le hNL)
  have hzK := earlier z hzN (lt_of_le_of_lt hzClosure hlt)
  exact hxK (hprod ▸ K.mul_mem hyK hzK)

/-- For an abelian minimal normal kernel, a proper subgroup surjecting to
the quotient meets the kernel trivially. -/
theorem inf_eq_bot_of_proper_abelian_chief_supplement (A H : Subgroup G)
    [A.Normal] (commutes : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (minimal : ∀ J : Subgroup G, J.Normal → J ≤ A → J = ⊥ ∨ J = A)
    (supplement : H ⊔ A = ⊤) (proper : H ≠ ⊤) : H ⊓ A = ⊥ := by
  have normalInf : (H ⊓ A).Normal := by
    constructor
    intro x hx g
    have hg : g ∈ H ⊔ A := by rw [supplement]; exact mem_top g
    obtain ⟨h, hh, a, ha, rfl⟩ := mem_sup_of_normal_right.mp hg
    have heq : h * a * x * (h * a)⁻¹ = h * x * h⁻¹ := by
      calc
        h * a * x * (h * a)⁻¹ = h * (a * x) * a⁻¹ * h⁻¹ := by
          simp only [mul_inv_rev]; group
        _ = h * x * h⁻¹ := by rw [commutes a ha x hx.2]; simp [mul_assoc]
    refine ⟨?_, (inferInstance : A.Normal).conj_mem x hx.2 (h * a)⟩
    rw [heq]
    exact H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh)
  rcases minimal (H ⊓ A) normalInf inf_le_right with h | h
  · exact h
  · have hAH : A ≤ H := by rw [← h]; exact inf_le_left
    exact (proper ((sup_eq_left.mpr hAH).symm.trans supplement)).elim

end Mathproof.MinimumGeneration
