import EvenP3RankSlicedMass

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical

noncomputable section

/-- Combine the rank slices and the large-rank region with distinct bounds
on their masses. The zero label contributes exactly zero. -/
theorem split_label_mass_le {X : Type*} [Fintype X] [Zero X]
    (q : ℝ) (hq : 1 ≤ q) (d r : X → ℕ) (s a b gap highRank : ℕ)
    (sizeBound : ℝ) (hSize : (Fintype.card X : ℝ) ≤ sizeBound)
    (hCount : ∀ j, ((Finset.univ.filter (fun x => d x = j)).card : ℝ) ≤ q^(a*j+b))
    (hLow : ∀ x, x ≠ 0 → d x ≤ s → a*d x+b+gap ≤ r x)
    (hHigh : ∀ x, x ≠ 0 → s < d x → highRank ≤ r x) :
    (∑ x, if x = 0 then 0 else (q ^ r x)⁻¹) ≤
      ((s+1 : ℕ) : ℝ) * (q^gap)⁻¹ + sizeBound * (q^highRank)⁻¹ := by
  have hq' : 0 < q := by linarith
  let S := {x : X // x ≠ 0 ∧ d x ≤ s}
  let low (x : X) : Prop := x ≠ 0 ∧ d x ≤ s
  change _ ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ low]
  apply add_le_add
  · let f (x : X) : ℝ := (q ^ r x)⁻¹
    have hlow : (∑ x ∈ Finset.univ.filter low, if x = 0 then (0 : ℝ) else (q ^ r x)⁻¹) =
        ∑ x : S, f x.val := by
      rw [Finset.sum_subtype (s := Finset.univ.filter low) (p := low)
        (fun x => by simp [low])]
      apply Finset.sum_congr rfl
      intro x _
      exact if_neg x.property.1
    rw [hlow]
    have hCount' (j : ℕ) : ((Finset.univ.filter (fun x : S => d x.val = j)).card : ℝ) ≤ q^(a*j+b) := by
      refine le_trans ?_ (hCount j)
      exact_mod_cast Finset.card_le_card_of_injOn (f := Subtype.val)
        (by intro x hx; simpa using hx) Subtype.val_injective.injOn
    exact rank_sliced_mass_le q hq (d ∘ Subtype.val) (r ∘ Subtype.val) s gap a b
      (fun x => x.property.2) hCount' (fun x => hLow x x.property.1 x.property.2)
  · calc
      _ ≤ ∑ _ : X, (q^highRank)⁻¹ := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : x = 0
        · simp [hx]
          positivity
        · by_cases hg : low x
          · simp only [not_not, hg, ite_false, if_false]
            positivity
          · simp only [if_pos hg, if_neg hx]
            exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hq
              (hHigh x hx (lt_of_not_ge (fun hd => hg ⟨hx,hd⟩))))
      _ = (Fintype.card X : ℝ) * (q^highRank)⁻¹ := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hSize (by positivity)

#print axioms split_label_mass_le

end
end Mathproof.EvenTI.OrderFour
