import EvenP3SingularRectVariation
import EvenP3SingularRectMarginals
import EvenP3SingularLiveCrop
import EvenP2SpectralBasic
import EvenP2PolarTarget

namespace Mathproof.EvenOrdinaryTISingular.RectPolar

open scoped TensorProduct BigOperators Classical
open Module Matrix PolarOperator EvenTI.Action EvenTI.Primary
open Mathproof.Problem17RepeatedBudget Mathproof.Problem17PrimaryTail
open Mathproof.EvenTI.Singular.Coverage
noncomputable section

private theorem mean_cost_le_of_dominates {A B Y : Type*} [Fintype A] [Fintype B] [Fintype Y]
    (f : A → Y) (g : B → Y) (cost : Y → ℝ) (hc : ∀ y, 0 ≤ cost y)
    (h : ∀ P : Y → Prop, uniformFraction A (fun a => P (f a)) ≤
      4 * uniformFraction B (fun b => P (g b))) :
    mean (cost ∘ f) ≤ 4 * mean (cost ∘ g) := by
  have hw (y : Y) : weight f y ≤ 4 * weight g y := by
    have hp := h (· = y)
    simpa only [weight, event_eq_card, uniformFraction] using hp
  rw [mean_comp_eq_weight, mean_comp_eq_weight, Finset.mul_sum]
  exact Finset.sum_le_sum (fun y _ =>
    (mul_le_mul_of_nonneg_left (hw y) (hc y)).trans_eq (by ring))

variable {K : Type*} [Field K] [Fintype K] {n l r u v : ℕ}
variable {R : Submodule K (Coord r n → K)} {S : Submodule K (Coord l n → K)}
variable (pL : (Coord l n → K) →ₗ[K] M K u) (pR : (Coord r n → K) →ₗ[K] M K v)
variable (hL : cropImage S pL ≤ TraceSpace K u) (hR : cropImage R pR ≤ TraceSpace K v)

local instance : Fintype (cropImage S pL ⊗[K] cropImage R pR) :=
  @Fintype.ofFinite _ (Module.finite_of_finite K)
local instance : Fintype (jointTarget K u v) := Fintype.ofFinite _
local instance : Fintype (DenseKernelFiber R S) := Fintype.ofFinite _

def liveJoint (A : DenseKernelFiber R S) : jointTarget K u v :=
  restrictedCovariants hL hR (rawLiveCrop R S pL pR A)

/-- The matrix-law mean plus its Fourier error, multiplied by the
conditioning loss for the original exact two-kernel fiber. -/
theorem live_cost_mean_le (A₀ : DenseKernelFiber R S) (c : ℕ) (hn : 1024 ≤ n)
    (hu : u ≤ n) (hv : v ≤ n) (hd : n ≤ 3 * min u v) (hc : Fintype.card K ^ c ≤ n)
    (hSc : finrank K (M K u ⧸ cropImage S pL) ≤ c)
    (hRc : finrank K (M K v ⧸ cropImage R pR) ≤ c)
    (f : jointTarget K u v → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ y, 0 ≤ f y ∧ f y ≤ B) :
    mean (f ∘ liveJoint pL pR hL hR) ≤
      4 * (mean f + B * ((Fintype.card K : ℝ) ^ (n*n))⁻¹) := by
  let g := restrictedCovariants hL hR
  have h1 : mean (f ∘ liveJoint pL pR hL hR) ≤ 4 * mean (f ∘ g) :=
    mean_cost_le_of_dominates (liveJoint pL pR hL hR) g f (fun y => (hf y).1)
      (fun P => uniformFraction_rawLiveCrop_le_four R S pL pR A₀ (fun x => P (g x)))
  have h2 := mean_comp_le_uniform_add_l1 g f B _ hB hf
    (restricted_covariant_l1_error hL hR n c hn hu hv hd hc hSc hRc)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))

private theorem cost_bound {d : ℕ} (hd : d ≤ n) (A : M K d) :
    0 ≤ (repeatedBudget A.charpoly : ℝ) ∧
      (repeatedBudget A.charpoly : ℝ) ≤ (n^2 : ℕ) := by
  refine ⟨by positivity, (primary_pointwise_cap A).trans ?_⟩
  exact_mod_cast Nat.pow_le_pow_left hd 2

/-- Bounded budget means for both unequal-width covariants, on the literal
uniform dense fiber itself. -/
theorem live_primary_means_le (A₀ : DenseKernelFiber R S) (c : ℕ) (hn : 1024 ≤ n)
    (hu : u ≤ n) (hv : v ≤ n) (hd : n ≤ 3 * min u v) (hc : Fintype.card K ^ c ≤ n)
    (hSc : finrank K (M K u ⧸ cropImage S pL) ≤ c)
    (hRc : finrank K (M K v ⧸ cropImage R pR) ≤ c) :
    mean (fun A => (repeatedBudget (leftCoordinate (liveJoint pL pR hL hR A)).charpoly : ℝ)) ≤
        4 * (budgetConstant K + 1) ∧
    mean (fun A => (repeatedBudget (rightCoordinate (liveJoint pL pR hL hR A)).charpoly : ℝ)) ≤
        4 * (budgetConstant K + 1) := by
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hErr := square_mul_field_decay (K := K) n (by omega)
  constructor
  · have h := live_cost_mean_le pL pR hL hR A₀ c hn hu hv hd hc hSc hRc
      (fun y => (repeatedBudget (leftCoordinate y).charpoly : ℝ)) (n^2 : ℕ)
      (by positivity) (fun y => cost_bound hu (leftCoordinate y))
    have hM := mean_left_primary_budget_le (K := K) (u := u) (v := v) hup hvp
    exact h.trans (by rw [← pow_two]; linarith only [hM,hErr])
  · have h := live_cost_mean_le pL pR hL hR A₀ c hn hu hv hd hc hSc hRc
      (fun y => (repeatedBudget (rightCoordinate y).charpoly : ℝ)) (n^2 : ℕ)
      (by positivity) (fun y => cost_bound hv (rightCoordinate y))
    have hM := mean_right_primary_budget_le (K := K) (u := u) (v := v) hup hvp
    exact h.trans (by rw [← pow_two]; linarith only [hM,hErr])

end
end Mathproof.EvenOrdinaryTISingular.RectPolar

#print axioms Mathproof.EvenOrdinaryTISingular.RectPolar.live_primary_means_le

