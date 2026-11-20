import TraceCharacters
import EvenP2PolarAlgebra

namespace Mathproof.EvenOrdinaryTISingular

open scoped TensorProduct Matrix BigOperators
open Module LinearMap Matrix
open Mathproof.Problem17PolarAssembly Mathproof.Problem17TracePairing
open Mathproof.EvenOrdinaryTISingular.PolarOperator
open Mathproof.Problem17TensorEscape
open Mathproof.Problem17TraceCharacters

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}



variable {S R : MatSubspace K n}
variable (hS : S ≤ TraceSpace K n) (hR : R ≤ TraceSpace K n)

section Finite

variable [Fintype K]

noncomputable local instance : Fintype (S ⊗[K] R) :=
  @Fintype.ofFinite _ (Module.finite_of_finite K)

noncomputable local instance : Fintype (jointTarget K n) := Fintype.ofFinite _

omit [Fintype K] in
private theorem scalar_value_on_target (a b : K) (x : jointTarget K n) :
    tracePairing (a • (1 : M K n)) x.val.1 + tracePairing (b • (1 : M K n)) x.val.2 =
      a * x.val.1.trace + b * x.val.2.trace := by
  change Matrix.trace ((a • (1 : M K n)) * x.val.1) +
    Matrix.trace ((b • (1 : M K n)) * x.val.2) = _
  simp [Matrix.trace_smul, smul_eq_mul]

set_option maxHeartbeats 1200000 in
theorem restricted_character_polar_rank (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (c : ℕ) (hSc : finrank K (M K n ⧸ S) ≤ c) (hRc : finrank K (M K n ⧸ R) ≤ c)
    (χ : AddChar (jointTarget K n) ℂ) (hχ : χ ≠ 1) :
    ∃ (P Q : M K n), (∀ z, χ (restrictedCovariants hS hR z) =
      ψ (jointValue P Q (embed (subspaceTensor hS hR z) ^ 2))) ∧
      (n - 4*c) * (n*n - 2*c) ≤ finrank K (restrictedPolar hS hR P Q).range := by
  obtain ⟨P,Q,h⟩ := character_on_pair_subspace (jointTarget K n) tracePairing tracePairing
    tracePairing_nondegenerate tracePairing_nondegenerate ψ hψ χ
  refine ⟨P,Q,fun z => h (restrictedCovariants hS hR z),?_⟩
  by_cases hP : ∀ a : K, P ≠ a • (1 : M K n)
  · exact restrictedPolar_rank_nonscalar_left hS hR P Q hP c hSc hRc
  by_cases hQ : ∀ b : K, Q ≠ b • (1 : M K n)
  · exact restrictedPolar_rank_nonscalar_right hS hR P Q hQ c hSc hRc
  push Not at hP hQ
  obtain ⟨a,rfl⟩ := hP
  obtain ⟨b,rfl⟩ := hQ
  have hs : ¬ ((2 : K) = 0 ∨ a+b = 0) := by
    intro hc
    apply hχ
    ext x
    rw [h, scalar_value_on_target]
    have hx := x.property
    unfold jointTarget at hx
    split_ifs at hx with h2
    · change x.val.1.trace = 0 ∧ x.val.2.trace = 0 at hx
      rw [hx.1,hx.2,mul_zero,mul_zero,zero_add,AddChar.map_zero_eq_one]
      rfl
    · change x.val.1.trace - x.val.2.trace = 0 at hx
      rw [sub_eq_zero.mp hx, ← add_mul, hc.resolve_left h2, zero_mul,AddChar.map_zero_eq_one]
      rfl
  exact restrictedPolar_rank_scalar hS hR a b (fun he => hs (Or.inl he))
    (fun he => hs (Or.inr he)) c hSc hRc

end Finite
end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.restricted_character_polar_rank

