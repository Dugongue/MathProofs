import EvenSingularPrefix
import EvenSingularColumns
import EvenSingularConditioning

/-! Singular-side restriction: the observed law of a uniform square invertible
matrix is close to the uniform law on a retained block, in every event. -/
namespace Mathproof.EvenOrdinaryTISingular
open Module
open scoped BigOperators

noncomputable section

/-- Event fraction on a finite type, expressed using subtype cardinalities. -/
def uniformFraction (A : Type*) (P : A → Prop) : ℝ :=
  (Nat.card {x : A // P x} : ℝ) / (Nat.card A : ℝ)

theorem uniformFraction_equiv {A B : Type*} (e : A ≃ B) (P : B → Prop) :
    uniformFraction A (fun a => P (e a)) = uniformFraction B P := by
  unfold uniformFraction
  rw [Nat.card_congr e, Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))]

private theorem eventSize_eq_card {A : Type*} [Fintype A] (P : A → Prop) :
    eventSize P = (Nat.card {x : A // P x} : ℝ) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private theorem conditioned_event_card {A : Type*} (P G : A → Prop) :
    Nat.card {x : A // P x ∧ G x} = Nat.card {x : {x : A // G x} // P x.val} := by
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.val, x.property.2⟩, x.property.1⟩
      invFun := fun x => ⟨x.val.val, x.property, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Conditioning error for a predicate after any observation of the sample. -/
theorem uniformFraction_conditioning_gap {A : Type*} [Fintype A]
    (P G : A → Prop) [Nonempty {x : A // G x}] :
    |uniformFraction {x : A // G x} (fun x => P x.val) - uniformFraction A P| ≤
      1 - (Nat.card {x : A // G x} : ℝ) / (Nat.card A : ℝ) := by
  classical
  have hg' : 0 < Nat.card {x : A // G x} := Nat.card_pos
  have hg : 0 < eventSize G := by
    rw [eventSize_eq_card]
    exact_mod_cast hg'
  have h := uniform_event_conditioning_gap P G hg
  rw [eventSize_eq_card, conditioned_event_card, eventSize_eq_card, eventSize_eq_card,
    eventSize_eq_card] at h
  have hcard : Fintype.card {x : A // ¬ G x} =
      Fintype.card A - Fintype.card {x : A // G x} := by
    have hc := Fintype.card_compl_set {x : A | G x}
    exact hc
  have hA : 0 < (Fintype.card A : ℝ) := by
    obtain ⟨x⟩ := ‹Nonempty {x : A // G x}›
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨x.val⟩)
  have hle : Fintype.card {x : A // G x} ≤ Fintype.card A :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [Nat.card_eq_fintype_card] at h
  rw [hcard, Nat.cast_sub hle, sub_div, div_self hA.ne'] at h
  simpa only [uniformFraction, Nat.card_eq_fintype_card] using h

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

/-- A surjective linear crop sends the uniform law to exactly the uniform law.
The translation by a chosen lift identifies every fiber with the kernel. -/
theorem uniformFraction_linear_surjective [Fintype V] [Fintype W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (P : W → Prop) :
    uniformFraction V (fun x => P (f x)) = uniformFraction W P := by
  let s := Function.surjInv hf
  have hs := Function.surjInv_eq hf
  let E (Q : W → Prop) : {x : V // Q (f x)} ≃ {y : W // Q y} × f.ker :=
    { toFun := fun x => (⟨f x.val, x.property⟩, ⟨x.val - s (f x.val), by
        change f (x.val - s (f x.val)) = 0
        rw [map_sub, hs, sub_self]⟩)
      invFun := fun y => ⟨y.2.val + s y.1.val, by
        rw [map_add, hs]
        have h0 : f y.2.val = 0 := y.2.property
        simpa [h0] using y.1.property⟩
      left_inv := fun x => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun y => by
        have h0 : f y.2.val = 0 := y.2.property
        have he : f (y.2.val + s y.1.val) = y.1.val := by rw [map_add, h0, hs, zero_add]
        apply Prod.ext
        · exact Subtype.ext he
        · apply Subtype.ext
          change y.2.val + s y.1.val - s (f (y.2.val + s y.1.val)) = y.2.val
          rw [he, add_sub_cancel_right] }
  have hall : Nat.card V = Nat.card W * Nat.card f.ker := by
    have he := Nat.card_congr (E fun _ => True)
    simpa [Nat.card_prod, Nat.card_subtype_true] using he
  have hk : 0 < Nat.card ↥f.ker := Nat.card_pos
  have hkR : (Nat.card ↥f.ker : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold uniformFraction
  rw [Nat.card_congr (E P), Nat.card_prod, hall, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ hkR]

variable [Fintype K] [Fintype V] [Fintype W]

theorem uniformFraction_independent_suffix {b t : ℕ}
    [Nonempty (Independent K V (b+t))]
    (Q : (Fin b → V) → Prop) :
    uniformFraction (Independent K V (b+t)) (fun x => Q (suffix t x.val)) =
      uniformFraction (Independent K V b) (fun x => Q x.val) := by
  classical
  obtain ⟨x⟩ := ‹Nonempty (Independent K V (b+t))›
  letI : Nonempty (Independent K V b) := ⟨⟨suffix t x.val, suffix_independent t x⟩⟩
  have hV : (Nat.card (Independent K V (b+t)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Independent K V (b+t))).ne'
  have hB : (Nat.card (Independent K V b) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Independent K V b)).ne'
  unfold uniformFraction
  apply (div_eq_div_iff hV hB).mpr
  have hc := independent_suffix_event (K := K) (V := V) (b := b) (t := t)
    (fun y => Q y.val)
  rw [mul_comm (Nat.card (Independent K V (b+t)))] at hc
  exact_mod_cast hc

theorem independent_discard_fraction_le (b : ℕ) (hb : b ≤ finrank K V) :
    1 - (Nat.card (Independent K V b) : ℝ) / (Nat.card (Fin b → V) : ℝ) ≤
      ((Fintype.card K : ℝ)^b - 1) /
        ((Fintype.card K : ℝ)^(finrank K V) * ((Fintype.card K : ℝ) - 1)) := by
  rw [Nat.card_eq_fintype_card (α := Fin b → V)]
  exact dependent_column_fraction_le (K := K) (V := V) b hb

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_conditioning_gap
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_linear_surjective
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_independent_suffix
#print axioms Mathproof.EvenOrdinaryTISingular.independent_discard_fraction_le