import EvenP1ProbKernel

namespace Mathproof.EvenTI.Reciprocal.PartOne

open Module
open scoped BigOperators
open Mathproof.EvenOrdinaryTISingular (uniformFraction)

noncomputable section

variable {X : Type*} [Fintype X]

/-- Uniform choice of the first sample, then independent uniform choice in
its own fiber. Fibers are allowed to have different sizes. -/
def fiberFailureAverage {Y : X → Type*} (E : (x : X) → Y x → Prop) : ℝ :=
  (∑ x, uniformFraction (Y x) (E x)) / (Fintype.card X : ℝ)

theorem fiberFailureAverage_le_of_imp {Y : X → Type*} [∀ x, Fintype (Y x)]
    {E F : (x : X) → Y x → Prop} (h : ∀ x y, E x y → F x y) :
    fiberFailureAverage E ≤ fiberFailureAverage F := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun x _ => uniformFraction_le_of_imp (h x)

theorem fiberFailureAverage_exists_le {Y : X → Type*} [∀ x, Fintype (Y x)]
    {L : Type*} [Fintype L] (E : L → (x : X) → Y x → Prop) :
    fiberFailureAverage (fun x y => ∃ z, E z x y) ≤ ∑ z, fiberFailureAverage (E z) := by
  unfold fiberFailureAverage
  rw [← Finset.sum_div, Finset.sum_comm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun x _ => uniformFraction_exists_le (fun z => E z x)

/-- The high-rank fibers use their exact rank penalty. The low-rank fibers
may all be bad, so their contribution is at most their total mass. -/
theorem average_zero_tuple_le_of_cutoff {K : Type*} [Field K] [Fintype K]
    {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)] [∀ x, Fintype (V x)]
    {W : Type*} [AddCommGroup W] [Module K W] [Fintype W]
    (f : (x : X) → V x →ₗ[K] W) (a r : ℕ) :
    fiberFailureAverage (fun x (v : Fin a → V x) => ∀ i, f x (v i) = 0) ≤
      uniformFraction X (fun x => finrank K (f x).range < r) +
      1 / (Fintype.card K : ℝ) ^ (a*r) := by
  classical
  let q : ℝ := Fintype.card K
  let low (x : X) := finrank K (f x).range < r
  let c : ℝ := 1 / q^(a*r)
  have hc : 0 ≤ c := by positivity
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast (Fintype.one_lt_card (α := K)).le
  unfold fiberFailureAverage
  calc
    _ ≤ (∑ x, ((if low x then 1 else 0) + c)) / (Fintype.card X : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : low x
      · simp only [if_pos hx]
        exact (uniformFraction_le_one _).trans (le_add_of_nonneg_right hc)
      · simp only [if_neg hx, zero_add]
        rw [zero_tuple_fraction (f x)]
        apply one_div_le_one_div_of_le (pow_pos (zero_lt_one.trans_le hq) _)
        exact pow_le_pow_right₀ hq (Nat.mul_le_mul_left a (le_of_not_gt hx))
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, add_div, Finset.sum_boole, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      unfold uniformFraction
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply add_le_add_right _ _
      by_cases hs : Fintype.card X = 0
      · simpa [hs] using hc
      · have hs' : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast hs
        change (Fintype.card X : ℝ) * c / (Fintype.card X : ℝ) ≤ c
        rw [mul_div_cancel_left₀ _ hs']

/-- Every nonsurjective row map admits a nonzero dual annihilator. The
per-label cutoff estimates bound their union over all dual labels. -/
theorem average_nonsurjective_le_of_cutoff {K : Type*} [Field K] [Fintype K]
    {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)] [∀ x, Fintype (V x)]
    {W Z D : Type*} [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z] [Fintype Z] [AddCommGroup D] [Module K D]
    [Fintype {z : Dual K W // z ≠ 0}]
    {a : ℕ} (rows : (x : X) → (Fin a → V x) → (D →ₗ[K] W))
    (coeff : {z : Dual K W // z ≠ 0} → (x : X) → (V x →ₗ[K] Z))
    (hcoeff : ∀ z x v, z.val.comp (rows x v) = 0 → ∀ i, coeff z x (v i) = 0)
    (r : ℕ) (δ : ℝ)
    (hlow : ∀ z, uniformFraction X (fun x => finrank K (coeff z x).range < r) ≤ δ) :
    fiberFailureAverage (fun x v => ¬ Function.Surjective (rows x v)) ≤
      (Fintype.card {z : Dual K W // z ≠ 0} : ℝ) *
        (δ + 1 / (Fintype.card K : ℝ) ^ (a*r)) := by
  let labelBad (z : {z : Dual K W // z ≠ 0}) (x : X) (v : Fin a → V x) :=
    ∀ i, coeff z x (v i) = 0
  have hpoint x v (hbad : ¬ Function.Surjective (rows x v)) : ∃ z, labelBad z x v := by
    obtain ⟨z, hz, he⟩ := (not_surjective_iff_dual _).mp hbad
    exact ⟨⟨z, hz⟩, hcoeff ⟨z, hz⟩ x v he⟩
  calc
    _ ≤ fiberFailureAverage (fun x v => ∃ z, labelBad z x v) :=
      fiberFailureAverage_le_of_imp hpoint
    _ ≤ ∑ z, fiberFailureAverage (labelBad z) := fiberFailureAverage_exists_le labelBad
    _ ≤ ∑ _ : {z : Dual K W // z ≠ 0}, (δ + 1 / (Fintype.card K : ℝ) ^ (a*r)) :=
      Finset.sum_le_sum fun z _ =>
        (average_zero_tuple_le_of_cutoff (coeff z) a r).trans (add_le_add_left (hlow z) _)
    _ = _ := by simp [mul_add]

#print axioms average_zero_tuple_le_of_cutoff
#print axioms average_nonsurjective_le_of_cutoff

end
end Mathproof.EvenTI.Reciprocal.PartOne
