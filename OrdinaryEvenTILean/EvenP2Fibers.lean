import EvenP2Mean

namespace Mathproof.EvenTI.Singular.Coverage

open scoped BigOperators Classical
open EvenTI.Primary Mathproof.EvenOrdinaryTISingular

noncomputable section

private theorem sum_fibers {A B : Type*} [Fintype A] [Fintype B]
    (k : A → B) (f : A → ℝ) :
    (∑ a, f a) = ∑ b, ∑ x : {a : A // k a = b}, f x.val := by
  rw [← Fintype.sum_sigma']
  exact (Equiv.sum_comp (Equiv.sigmaFiberEquiv k) f).symm

/-- A uniform bound on every nonexceptional exact fiber gives the
same bound on the whole sample, plus the exceptional source fraction. -/
theorem event_le_of_fibers {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (k : A → B) (bad : A → Prop) (exceptional : B → Prop)
    (p : ℝ) (hp : 0 ≤ p)
    (h : ∀ b, ¬ exceptional b → uniformFraction {a : A // k a = b}
      (fun a => bad a.val) ≤ p) :
    event bad ≤ event (fun a => exceptional (k a)) + p := by
  let f (a : A) : ℝ := if bad a then 1 else 0
  let g (a : A) : ℝ := (if exceptional (k a) then 1 else 0) + p
  change mean f ≤ _
  have hf : mean f ≤ mean g := by
    unfold mean
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [sum_fibers k f, sum_fibers k g]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : exceptional b
    · exact Finset.sum_le_sum fun x _ => by
        simp only [g, x.property, if_pos hb, f]
        split <;> linarith
    · by_cases hEmpty : IsEmpty {a : A // k a = b}
      · simp [Finset.univ_eq_empty]
      · letI : Nonempty {a : A // k a = b} := not_isEmpty_iff.mp hEmpty
        have hCount : (0 : ℝ) < Fintype.card {a : A // k a = b} := by positivity
        have hBound := h b hb
        rw [← event_as_fraction] at hBound
        change (∑ x : {a : A // k a = b}, f x.val) /
          Fintype.card {a : A // k a = b} ≤ p at hBound
        have hg (x : {a : A // k a = b}) : g x.val = p := by
          simp only [g, x.property, if_neg hb, zero_add]
        simp_rw [hg]
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_comm (Fintype.card {a : A // k a = b} : ℝ)] using (div_le_iff₀ hCount).mp hBound
  refine hf.trans_eq ?_
  have ha : (Fintype.card A : ℝ) ≠ 0 := by positivity
  simp only [mean, event, g, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, add_div]
  rw [mul_comm (Fintype.card A : ℝ) p, mul_div_cancel_right₀ _ ha]

#print axioms event_le_of_fibers

end
end Mathproof.EvenTI.Singular.Coverage
