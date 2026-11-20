import EvenPrimaryEnvelope

open scoped BigOperators Classical

namespace EvenTI.Primary

noncomputable section

def weight {Ω A : Type*} [Fintype Ω] (a : Ω → A) (y : A) : ℝ :=
  event (fun x => a x = y)

theorem mean_comp_eq_weight {Ω A : Type*} [Fintype Ω] [Fintype A]
    (a : Ω → A) (f : A → ℝ) :
    mean (f ∘ a) = ∑ y, f y * weight a y := by
  classical
  have h (x : Ω) :
      (∑ y : A, f y * (if a x = y then (1:ℝ) else 0)) = f (a x) := by
    rw [Finset.sum_eq_single (a x)]
    · simp
    · intro b _ hb
      have hn : a x ≠ b := Ne.symm hb
      simp [hn]
    · simp
  calc
    _ = mean (fun x => ∑ y : A, f y * (if a x = y then (1:ℝ) else 0)) :=
      congrArg mean (funext fun x => (h x).symm)
    _ = _ := by simp only [mean_sum, mean_mul, weight, event]

/-- An L1 perturbation of a marginal law costs at most the pointwise bound
times the L1 error in its expectation. No joint law is involved. -/
theorem mean_comp_le_uniform_add_l1 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (a : Ω → A) (f : A → ℝ) (M δ : ℝ) (hM : 0 ≤ M)
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ M)
    (hl1 : (∑ y, |weight a y - (Fintype.card A : ℝ)⁻¹|) ≤ δ) :
    mean (f ∘ a) ≤ mean f + M * δ := by
  have hterm (y : A) :
      f y * (weight a y - (Fintype.card A:ℝ)⁻¹) ≤
        M * |weight a y - (Fintype.card A:ℝ)⁻¹| := by
    calc
      _ ≤ f y * |weight a y - (Fintype.card A:ℝ)⁻¹| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (hf y).1
      _ ≤ _ := mul_le_mul_of_nonneg_right (hf y).2 (abs_nonneg _)
  have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hterm y
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at hsum
  rw [mean_comp_eq_weight]
  have ht := mul_le_mul_of_nonneg_left hl1 hM
  unfold mean
  rw [div_eq_mul_inv]
  linarith

#print axioms mean_comp_le_uniform_add_l1

end
end EvenTI.Primary
