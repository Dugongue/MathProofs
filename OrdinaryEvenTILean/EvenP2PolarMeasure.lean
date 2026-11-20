import EvenP2PolarVariation
import EvenLiveSingularBlock

namespace Mathproof.EvenOrdinaryTISingular

open scoped BigOperators TensorProduct
open Module PolarOperator EvenTI.Primary

noncomputable section

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}
variable {S R : MatSubspace K n}
variable (hS : S ≤ TraceSpace K n) (hR : R ≤ TraceSpace K n)

local instance : Fintype (S ⊗[K] R) :=
  @Fintype.ofFinite _ (Module.finite_of_finite K)
local instance : Fintype (jointTarget K n) := Fintype.ofFinite _

/-- Transfer a bounded nonnegative statistic on the joint target to
the squared partial traces of a uniform tensor on the smaller subspaces. -/
theorem restricted_covariant_mean_le (c : ℕ) (hn : 64 ≤ n)
    (hc : Fintype.card K ^ c ≤ n)
    (hSc : finrank K (M K n ⧸ S) ≤ c) (hRc : finrank K (M K n ⧸ R) ≤ c)
    (f : jointTarget K n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ B) :
    mean (f ∘ restrictedCovariants hS hR) ≤
      mean f + B * ((Fintype.card K : ℝ) ^ (n*n))⁻¹ :=
  mean_comp_le_uniform_add_l1 _ f B _ hB hf
    (restricted_covariant_l1_error hS hR c hn hc hSc hRc)

/-- Every event on the realized anchor pair has the same one-sided
comparison error. -/
theorem restricted_covariant_event_le (c : ℕ) (hn : 64 ≤ n)
    (hc : Fintype.card K ^ c ≤ n)
    (hSc : finrank K (M K n ⧸ S) ≤ c) (hRc : finrank K (M K n ⧸ R) ≤ c)
    (P : jointTarget K n → Prop) :
    uniformFraction (S ⊗[K] R) (fun x => P (restrictedCovariants hS hR x)) ≤
      uniformFraction (jointTarget K n) P +
        ((Fintype.card K : ℝ) ^ (n*n))⁻¹ := by
  classical
  have h := restricted_covariant_mean_le hS hR c hn hc hSc hRc
    (fun x => if P x then (1 : ℝ) else 0) 1 zero_le_one
    (fun x => by by_cases hx : P x <;> simp [hx])
  change event (fun x => P (restrictedCovariants hS hR x)) ≤
    event P + 1 * ((Fintype.card K : ℝ) ^ (n*n))⁻¹ at h
  rw [event_eq_card, event_eq_card, one_mul] at h
  exact h

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.restricted_covariant_mean_le
#print axioms Mathproof.EvenOrdinaryTISingular.restricted_covariant_event_le
