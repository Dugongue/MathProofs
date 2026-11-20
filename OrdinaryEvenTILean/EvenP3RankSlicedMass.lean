import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical

noncomputable section

/-- The low-label Fourier mass is bounded by summing over ranks. A
linear growth bound on log-cardinality can therefore beat the corresponding
per-label rank bound even when the uniform minimum rank is too weak. -/
theorem rank_sliced_mass_le {X : Type*} [Fintype X]
    (q : ℝ) (hq : 1 ≤ q) (d r : X → ℕ) (s m a b : ℕ)
    (hRange : ∀ x, d x ≤ s)
    (hCount : ∀ j, ((Finset.univ.filter (fun x => d x = j)).card : ℝ) ≤ q^(a*j+b))
    (hRank : ∀ x, a*d x+b+m ≤ r x) :
    (∑ x, (q ^ r x)⁻¹) ≤ ((s+1 : ℕ) : ℝ) * (q^m)⁻¹ := by
  have hq' : 0 < q := by linarith
  let fiber (j : ℕ) : Finset X := Finset.univ.filter (fun x => d x = j)
  have hs : (∑ j ∈ Finset.range (s+1), ∑ x ∈ fiber j, (q ^ r x)⁻¹) =
      ∑ x, (q ^ r x)⁻¹ := by
    simp only [fiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    have hx : d x ∈ Finset.range (s+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (hRange x))
    simp only [Finset.sum_ite_eq, hx, if_true]
  rw [← hs]
  calc
    _ ≤ ∑ _j ∈ Finset.range (s+1), (q^m)⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ _x ∈ fiber j, (q^(a*j+b+m))⁻¹ := by
          apply Finset.sum_le_sum
          intro x hx
          have hEq : d x = j := (Finset.mem_filter.mp hx).2
          apply inv_anti₀ (by positivity)
          apply pow_le_pow_right₀ hq
          simpa only [hEq] using (hRank x)
        _ = (fiber j).card * (q^(a*j+b+m))⁻¹ := by simp [nsmul_eq_mul]
        _ ≤ q^(a*j+b) * (q^(a*j+b+m))⁻¹ :=
          mul_le_mul_of_nonneg_right (hCount j) (by positivity)
        _ = (q^m)⁻¹ := by
          rw [pow_add q (a*j+b) m, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ = _ := by simp [nsmul_eq_mul]

#print axioms rank_sliced_mass_le

end
end Mathproof.EvenTI.OrderFour
