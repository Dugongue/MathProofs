import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.LinearCombination

/-! Determinant face extraction and quadratic elimination for Grochow catalogue
problems GP-0605 and GP-0743. This file proves the two algebraic steps. -/

open scoped BigOperators

namespace GrochowCatalogueCertificates

private theorem sum_gap_pos {ι : Type*} [Fintype ι]
    (weight : ι → ℤ) (M : ℤ) (upper : ∀ i, weight i ≤ M)
    {i : ι} (strict : weight i < M) :
    (∑ j, weight j) < ∑ _j : ι, M := by
  classical
  have sum_pos : 0 < ∑ j, (M - weight j) := by
    have hle : M - weight i ≤ ∑ j, (M - weight j) :=
      Finset.single_le_sum (fun j _ => sub_nonneg.mpr (upper j)) (Finset.mem_univ i)
    exact lt_of_lt_of_le (sub_pos.mpr strict) hle
  rw [Finset.sum_sub_distrib] at sum_pos
  exact sub_pos.mp sum_pos

/-- Restricting to entries of highest additive weight preserves each square
    determinant when the selected row and column weights sum to the top weight
    of a full matching, and makes it zero otherwise. -/
theorem determinant_of_max_weight_entries
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) (u v : ι → ℤ) (M : ℤ)
    (upper : ∀ i j, A i j ≠ 0 → u i + v j ≤ M) :
    let B : Matrix ι ι R := fun i j => if u i + v j = M then A i j else 0
    B.det = if (∑ i, u i) + (∑ i, v i) = ∑ _i : ι, M then A.det else 0 := by
  classical
  let B : Matrix ι ι R := fun i j => if u i + v j = M then A i j else 0
  let W := (∑ i, u i) + (∑ i, v i)
  have hW (σ : Equiv.Perm ι) : (∑ i, (u (σ i) + v i)) = W := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ u]
  change B.det =
    if W = (∑ _i : ι, M) then A.det else 0
  by_cases h : W = ∑ _i : ι, M
  · rw [if_pos h, Matrix.det_apply B, Matrix.det_apply A]
    apply Finset.sum_congr rfl
    intro σ _
    congr 1
    by_cases hz : ∃ i, A (σ i) i = 0
    · obtain ⟨i, hi⟩ := hz
      rw [Finset.prod_eq_zero (f := fun j => A (σ j) j) (Finset.mem_univ i) hi]
      apply Finset.prod_eq_zero (f := fun j => B (σ j) j) (Finset.mem_univ i)
      simp [B, hi]
    · have hn : ∀ i, A (σ i) i ≠ 0 := fun i hi => hz ⟨i, hi⟩
      apply Finset.prod_congr rfl
      intro i _
      dsimp [B]
      apply if_pos
      apply le_antisymm (upper (σ i) i (hn i))
      apply le_of_not_gt
      intro hi
      have contra := sum_gap_pos (fun j => u (σ j) + v j) M
        (fun j => upper (σ j) j (hn j)) hi
      rw [hW σ, h] at contra
      exact (lt_irrefl _ contra)
  · rw [if_neg h, Matrix.det_apply B]
    apply Finset.sum_eq_zero
    intro σ _
    have hex : ∃ i, u (σ i) + v i ≠ M := by
      by_contra! hall
      apply h
      rw [← hW σ]
      exact Finset.sum_congr rfl fun i _ => hall i
    obtain ⟨i, hi⟩ := hex
    have hb : B (σ i) i = 0 := if_neg hi
    rw [Finset.prod_eq_zero (f := fun j => B (σ j) j) (Finset.mem_univ i) hb, smul_zero]

/-- The forget-variable norm in the free rank-two Boolean quotient algebra. -/
theorem quadratic_norm {R : Type*} [CommRing R]
    (a b u z : R) (hu : u ^ 2 - u = z) :
    (a + b * u) * (a + b * (1 - u)) = a ^ 2 + a * b - b ^ 2 * z := by
  linear_combination -(b ^ 2) * hu

/-- At Boolean-axis value zero the norm multiplies the two evaluations. -/
theorem quadratic_norm_at_zero {R : Type*} [CommRing R] (a b : R) :
    a ^ 2 + a * b - b ^ 2 * 0 = a * (a + b) := by
  linear_combination

/-- The two gate operations implement OR and AND for violation flags over
    every commutative ring. -/
theorem boolean_violation_gates {R : Type*} [CommRing R] (x y : Bool) :
    let v : Bool → R := fun b => if b then 1 else 0
    (v (x || y) = v x + v y - v x * v y) ∧ (v (x && y) = v x * v y) := by
  cases x <;> cases y <;> simp

#print axioms determinant_of_max_weight_entries
#print axioms quadratic_norm
#print axioms quadratic_norm_at_zero
#print axioms boolean_violation_gates

end GrochowCatalogueCertificates
