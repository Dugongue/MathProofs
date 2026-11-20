import EvenP2SpectralBasic
import EvenP2CropAnchors
import EvenP2FormsFiber
import EvenP2PolarMeasure
import EvenP2PolarTarget

namespace Mathproof.EvenTI.Singular.Coverage

open scoped BigOperators Matrix TensorProduct Classical
open Matrix Module EvenTI.Action EvenTI.Primary
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenTI.Singular.Forms
open Mathproof.EvenOrdinaryTISingular.PolarOperator
open Mathproof.Problem17RepeatedBudget

noncomputable section

variable {K : Type*} [Field K] {l n : ℕ}
variable {R S : Submodule K (Coord (l+1) n → K)}

private theorem left_image_spec (p : GoodPair R S) (i : Fin (l+1)) :
    physicalMatrixImage S i p.ell ≤ TraceZero K (Fin n) ∧
      finrank K (Matrix (Fin n) (Fin n) K ⧸ physicalMatrixImage S i p.ell) ≤ finrank K S :=
  physicalMatrixImage_trace_codim S i p.ell p.ell_mem (p.ell_rank i)

private theorem right_image_spec (p : GoodPair R S) (i : Fin (l+1)) :
    physicalMatrixImage R i p.rho ≤ TraceZero K (Fin n) ∧
      finrank K (Matrix (Fin n) (Fin n) K ⧸ physicalMatrixImage R i p.rho) ≤ finrank K R :=
  physicalMatrixImage_trace_codim R i p.rho p.rho_mem (p.rho_rank i)

def singularPairAnchor (p : GoodPair R S) (i : Fin (l+1)) (A : DenseKernelFiber R S) :
    jointTarget K n :=
  restrictedCovariants (left_image_spec p i).1 (right_image_spec p i).1
    (rawSingularCrop R S i i p.ell p.rho A)

theorem singularPairAnchor_eq_literal (p : GoodPair R S) (i : Fin (l+1))
    (A : DenseKernelFiber R S) :
    (singularPairAnchor p i A).val = literalSingularAnchors i i p.ell p.rho A.val :=
  rawSingularCrop_covariants_eq_literal R S i i p.ell p.rho
    (left_image_spec p i).1 (right_image_spec p i).1 A

def singularModeAnchor (p : GoodPair R S) (i : Fin (l+1) × Bool) (A : DenseKernelFiber R S) :
    Matrix (Fin n) (Fin n) K :=
  jointCoordinate i.2 (singularPairAnchor p i.1 A)

def singularBudget (p : GoodPair R S) (A : DenseKernelFiber R S) : ℕ :=
  ∑ i : Fin (l+1) × Bool, repeatedBudget (singularModeAnchor p i A).charpoly

variable [Fintype K]

private theorem dim_le_of_corankGate (h : Fintype.card K ^ finrank K R ≤ n) :
    finrank K R ≤ n :=
  (show finrank K R < 2 ^ finrank K R from Nat.lt_two_pow_self).le.trans
    ((Nat.pow_le_pow_left Fintype.one_lt_card _).trans h)

theorem singularPairAnchor_event_le (p : GoodPair R S) (i : Fin (l+1))
    (A₀ : DenseKernelFiber R S) (hl : 2 ≤ l) (hn : 64 ≤ n)
    (hGate : Fintype.card K ^ finrank K R ≤ n) (E : jointTarget K n → Prop) :
    uniformFraction (DenseKernelFiber R S) (fun A => E (singularPairAnchor p i A)) ≤
      uniformFraction (jointTarget K n) E + 2 * ((Fintype.card K : ℝ)^(n^2))⁻¹ := by
  let cov := restrictedCovariants (left_image_spec p i).1 (right_image_spec p i).1
  have h1 := uniformFraction_rawSingularCrop_small R S i i p.ell p.rho A₀ hl
    (by omega) (dim_le_of_corankGate (R := R) hGate) (fun Y => E (cov Y))
  have hc := fiber_coranks_eq A₀
  have hL := (left_image_spec p i).2.trans_eq hc.symm
  have hR := (right_image_spec p i).2
  have h2 := restricted_covariant_event_le (left_image_spec p i).1 (right_image_spec p i).1
    (finrank K R) hn hGate hL hR E
  rw [← pow_two] at h2
  exact (sub_le_iff_le_add.mp (abs_le.mp h1).2).trans (by linarith only [h2])

local instance jointFintype : Fintype (jointTarget K n) := Fintype.ofFinite _
local instance fiberFintype : Fintype (DenseKernelFiber R S) := Fintype.ofFinite _

theorem singularModeAnchor_budget_mean (p : GoodPair R S) (i : Fin (l+1) × Bool)
    (A₀ : DenseKernelFiber R S) (hl : 2 ≤ l) (hn : 64 ≤ n)
    (hGate : Fintype.card K ^ finrank K R ≤ n) :
    mean (fun A => (repeatedBudget (singularModeAnchor p i A).charpoly : ℝ)) ≤
      budgetConstant K + 2 := by
  let cost (Y : jointTarget K n) : ℝ := (repeatedBudget (jointCoordinate i.2 Y).charpoly : ℝ)
  have hMean := mean_cost_le_of_events (singularPairAnchor p i.1) id cost (n^2 : ℕ)
    (2 * ((Fintype.card K : ℝ)^(n^2))⁻¹) (by positivity)
    (fun Y => ⟨by dsimp [cost]; positivity, primary_pointwise_cap (jointCoordinate i.2 Y)⟩)
    (fun E => singularPairAnchor_event_le p i.1 A₀ hl hn hGate E)
  have hU : mean cost ≤ budgetConstant K :=
    mean_joint_primary_budget_le (K := K) (n := n) (by omega) i.2
  have hErr := square_mul_field_decay (K := K) n (by omega)
  change mean (cost ∘ singularPairAnchor p i.1) ≤ _
  exact hMean.trans (by
    change mean cost + ↑(n^2 : ℕ) * (2 * ((Fintype.card K : ℝ)^(n^2))⁻¹) ≤ _
    nlinarith only [hU, hErr])

theorem singular_fiber_spectral_gate (p : GoodPair R S)
    (A₀ : DenseKernelFiber R S) (hl : 2 ≤ l) (hn : 64 ≤ n)
    (hGate : Fintype.card K ^ finrank K R ≤ n) :
    uniformFraction (DenseKernelFiber R S)
      (fun A => n^((l+1)+(l+1)) < Fintype.card K ^ singularBudget p A) ≤
        (budgetConstant K + 2) * Real.log (Fintype.card K) / Real.log n := by
  have h := spectral_gate_of_mode_means (by omega : 2 ≤ n) (singularModeAnchor p) _
    (fun i => singularModeAnchor_budget_mean p i A₀ hl hn hGate)
  simpa [singularBudget, Fintype.card_prod, Nat.mul_two] using h

#print axioms singularPairAnchor_event_le
#print axioms singularPairAnchor_eq_literal
#print axioms singularModeAnchor_budget_mean
#print axioms singular_fiber_spectral_gate

end
end Mathproof.EvenTI.Singular.Coverage
