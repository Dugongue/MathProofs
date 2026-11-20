import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Mathproof.EvenOrdinaryTISingular

private theorem normalized_conditioning_gap (a b g h : ℝ)
    (ha : 0 ≤ a) (hag : a ≤ g) (hb : 0 ≤ b) (hbh : b ≤ h)
    (hg : 0 < g) (hh : 0 ≤ h) :
    |a/g - (a+b)/(g+h)| ≤ h/(g+h) := by
  have hden : 0 < g+h := by positivity
  have he : a/g - (a+b)/(g+h) = ((a/g)*h-b)/(g+h) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg (div_nonneg ha hg.le) hh],
    by nlinarith [mul_le_of_le_one_left hh ((div_le_one hg).mpr hag)]⟩

section Finite

variable {A : Type*} [Fintype A]

noncomputable def eventSize (p : A → Prop) : ℝ := by
  classical
  exact ((@Finset.filter A p (fun _ => Classical.propDecidable _) Finset.univ).card : ℝ)

private theorem eventSize_nonneg (p : A → Prop) : 0 ≤ eventSize p := by
  classical
  unfold eventSize
  positivity

private theorem eventSize_mono {p q : A → Prop} (h : ∀ a, p a → q a) :
    eventSize p ≤ eventSize q := by
  classical
  unfold eventSize
  exact_mod_cast Finset.card_le_card (by intro a ha; simpa using h a (by simpa using ha))

private theorem eventSize_partition (p q : A → Prop) :
    eventSize p = eventSize (fun a => p a ∧ q a) + eventSize (fun a => p a ∧ ¬q a) := by
  classical
  let X : Finset A := @Finset.filter A (fun a => p a ∧ q a)
    (fun _ => Classical.propDecidable _) Finset.univ
  let Y : Finset A := @Finset.filter A (fun a => p a ∧ ¬q a)
    (fun _ => Classical.propDecidable _) Finset.univ
  have hdis : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h₁ : p a ∧ q a := by simpa [X] using ha
    have h₂ : p a ∧ ¬q a := by simpa [Y] using hb
    exact h₂.2 h₁.2
  have hcov : X ∪ Y = Finset.univ.filter p := by
    ext a
    simp [X,Y]
    tauto
  unfold eventSize
  change ((Finset.univ.filter p).card : ℝ) = (X.card : ℝ) + (Y.card : ℝ)
  have hn := Finset.card_union_of_disjoint hdis
  rw [hcov] at hn
  exact_mod_cast hn

/-- Conditioning a finite uniform law on a nonempty event perturbs the
probability of any observed event by at most the discarded mass. -/
theorem uniform_event_conditioning_gap (p good : A → Prop) (hg : 0 < eventSize good) :
    abs (eventSize (fun a => p a ∧ good a) / eventSize good -
      eventSize p / (Fintype.card A : ℝ)) ≤
      eventSize (fun a => ¬good a) / (Fintype.card A : ℝ) := by
  classical
  have hin := eventSize_partition p good
  have hall := eventSize_partition (fun _ : A => True) good
  have hq : (Fintype.card A : ℝ) = eventSize good + eventSize (fun a => ¬good a) := by
    have ht : eventSize (fun _ : A => True) = (Fintype.card A : ℝ) := by
      simp [eventSize]
    have hgood : (fun a : A => True ∧ good a) = good := by
      funext a
      exact true_and _
    have hbad : (fun a : A => True ∧ ¬good a) = (fun a : A => ¬good a) := by
      funext a
      exact true_and _
    rw [ht,hgood,hbad] at hall
    exact hall
  rw [hin,hq]
  exact normalized_conditioning_gap _ _ _ _
    (eventSize_nonneg _) (eventSize_mono (fun _ h => h.2))
    (eventSize_nonneg _) (eventSize_mono (fun _ h => h.2))
    hg (eventSize_nonneg _)

end Finite
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.uniform_event_conditioning_gap
