import EvenP2Fibers

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical
open EvenTI.Primary

noncomputable section

private theorem mean_const_le {A : Type*} [Fintype A] {a : ℝ} (ha : 0 ≤ a) :
    mean (fun _ : A => a) ≤ a := by
  by_cases he : Fintype.card A = 0
  · simp [mean, he, ha]
  · have hcast : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast he
    simp [mean, mul_comm, hcast]

/-- Normalize only after summing the costs of the exact fibers, so that
the uniformly random source law retains its original fiber weights. -/
theorem mean_le_of_exact_fibers {A B : Type*} [Fintype A] [Fintype B]
    (key : A → B) (cost : A → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ b, mean (fun x : {a : A // key a = b} => cost x.val) ≤ C) :
    mean cost ≤ C := by
  have fiber_sum (f : A → ℝ) :
      (∑ a, f a) = ∑ b, ∑ x : {a : A // key a = b}, f x.val := by
    rw [← Fintype.sum_sigma']
    exact (Equiv.sum_comp (Equiv.sigmaFiberEquiv key) f).symm
  refine le_trans ?_ (mean_const_le (A := A) hC)
  unfold mean
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [fiber_sum cost, fiber_sum (fun _ => C)]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : IsEmpty {a : A // key a = b}
  · simp [Finset.univ_eq_empty]
  · letI : Nonempty {a : A // key a = b} := not_isEmpty_iff.mp hb
    have hpos : (0 : ℝ) < Fintype.card {a : A // key a = b} := by positivity
    simpa [mul_comm C] using (div_le_iff₀ hpos).mp (h b)

#print axioms mean_le_of_exact_fibers

end
end Mathproof.EvenTI.OrderFour
