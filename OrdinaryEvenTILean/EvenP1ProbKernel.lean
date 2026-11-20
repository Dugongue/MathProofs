import EvenLiveSingularBlock
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Exact finite-field zero-fiber probabilities and their union bound. -/
namespace Mathproof.EvenTI.Reciprocal.PartOne

open Module
open scoped BigOperators
open Mathproof.EvenOrdinaryTISingular (uniformFraction)

noncomputable section

theorem uniformFraction_le_one {A : Type*} [Fintype A] (P : A → Prop) :
    uniformFraction A P ≤ 1 := by
  have h := Nat.card_le_card_of_injective (Subtype.val : {x : A // P x} → A)
    Subtype.val_injective
  unfold uniformFraction
  by_cases hA : Nat.card A = 0
  · rw [hA, Nat.cast_zero, div_zero]
    exact zero_le_one
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hA)).mpr
    exact_mod_cast h

theorem uniformFraction_le_of_imp {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ x, P x → Q x) : uniformFraction A P ≤ uniformFraction A Q := by
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun x : {x : A // P x} => (⟨x.val, h x.val x.property⟩ : {x : A // Q x}))
    (fun _ _ he => Subtype.ext (congrArg (fun y : {x : A // Q x} => (y : A)) he))

theorem uniformFraction_exists_le {A L : Type*} [Fintype A] [Fintype L]
    (P : L → A → Prop) :
    uniformFraction A (fun x => ∃ i, P i x) ≤ ∑ i, uniformFraction A (P i) := by
  classical
  simp only [uniformFraction, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  let F : {x : A // ∃ i, P i x} → Σ i, {x : A // P i x} :=
    fun x => ⟨Classical.choose x.property, ⟨x.val, Classical.choose_spec x.property⟩⟩
  have h : Function.Injective F := fun x y e =>
    Subtype.ext (congrArg (fun t : Σ i, {x : A // P i x} => t.2.val) e)
  have hle := Nat.card_le_card_of_injective F h
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma] at hle ⊢
  exact_mod_cast hle

theorem not_surjective_iff_dual {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    ¬ Function.Surjective f ↔ ∃ z : Dual K W, z ≠ 0 ∧ z.comp f = 0 := by
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h
    obtain ⟨z, hz, hker⟩ := f.range.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr h)
    exact ⟨z, hz, LinearMap.ext fun x => hker ⟨x, rfl⟩⟩
  · rintro ⟨z, hnz, hz⟩
    intro htop
    have hz' : f.range ≤ z.ker := by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun hz x
    rw [htop] at hz'
    exact hnz (LinearMap.ext fun x => hz' (by trivial))

variable {K V W : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup W] [Module K W] [Fintype W]

/-- Independent choices of a vectors are jointly killed with the exact rank
penalty q^(-a r). Applies to different dual-annihilator fibers independently. -/
theorem zero_tuple_fraction (f : V →ₗ[K] W) (a : ℕ) :
    uniformFraction (Fin a → V) (fun x => ∀ i, f (x i) = 0) =
      1 / (Fintype.card K : ℝ) ^ (a * finrank K f.range) := by
  classical
  letI : Fintype f.ker := Fintype.ofFinite _
  let e : {x : Fin a → V // ∀ i, f (x i) = 0} ≃ (Fin a → f.ker) :=
    { toFun := fun x i => ⟨x.val i, x.property i⟩
      invFun := fun x => ⟨fun i => (x i).val, fun i => (x i).property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  unfold uniformFraction
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  rw [Module.card_eq_pow_finrank (K := K) (V := f.ker),
    Module.card_eq_pow_finrank (K := K) (V := V),
    ← f.finrank_range_add_finrank_ker]
  push_cast
  rw [← pow_mul, ← pow_mul]
  rw [show (finrank K f.range + finrank K f.ker) * a =
    finrank K f.ker * a + a * finrank K f.range by ring, pow_add]
  have hq : 0 < (Fintype.card K : ℝ) := by exact_mod_cast (Fintype.card_pos (α := K))
  field_simp

#print axioms zero_tuple_fraction
#print axioms uniformFraction_exists_le
#print axioms not_surjective_iff_dual

end
end Mathproof.EvenTI.Reciprocal.PartOne
