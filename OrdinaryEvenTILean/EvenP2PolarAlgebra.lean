import EvenP2PolarOperators

namespace Mathproof.EvenOrdinaryTISingular

open scoped TensorProduct Matrix BigOperators
open Module LinearMap Matrix
open Mathproof.Problem17PolarAssembly Mathproof.Problem17TracePairing
open Mathproof.EvenOrdinaryTISingular.PolarOperator
open Mathproof.Problem17TensorEscape

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

abbrev TraceSpace (K : Type*) [Field K] (n : ℕ) := TraceZero K (Fin n)

abbrev MatSubspace (K : Type*) (n : ℕ) [Field K] := Submodule K (M K n)

variable {S R : MatSubspace K n}
variable (hS : S ≤ TraceSpace K n) (hR : R ≤ TraceSpace K n)

/-- The rectangular kernel projections produce two possibly different proper
subspaces of the trace-zero matrix spaces. -/
def subspaceTensor : S ⊗[K] R →ₗ[K] T K n :=
  TensorProduct.map (Submodule.inclusion hS) (Submodule.inclusion hR)

def restrictedPolar (P Q : M K n) : LinearMap.BilinForm K (S ⊗[K] R) :=
  (supportedPolar P Q).compl₁₂ (subspaceTensor hS hR) (subspaceTensor hS hR)

def restrictedCovariants (x : S ⊗[K] R) : jointTarget K n :=
  covariants (subspaceTensor hS hR x)

private theorem restrictedPolar_tmul (P Q : M K n) (x x' : S) (y y' : R) :
    restrictedPolar hS hR P Q (x ⊗ₜ[K] y) (x' ⊗ₜ[K] y') =
      tracePairing (matAnti P x.val) x'.val * tracePairing y.val y'.val +
      tracePairing x.val x'.val * tracePairing (matAnti Q y.val) y'.val := by
  change supportedPolar P Q (subspaceTensor hS hR (x ⊗ₜ[K] y))
    (subspaceTensor hS hR (x' ⊗ₜ[K] y')) = _
  simp only [subspaceTensor, TensorProduct.map_tmul]
  simpa only [Submodule.coe_inclusion] using supportedPolar_tmul P Q
    (Submodule.inclusion hS x) (Submodule.inclusion hS x')
    (Submodule.inclusion hR y) (Submodule.inclusion hR y')

private theorem finrank_of_codim_le {X : MatSubspace K n} {k : ℕ}
    (h : finrank K (M K n ⧸ X) ≤ k) :
    n * n - k ≤ finrank K X := by
  have hx := X.finrank_quotient_add_finrank
  simp only [finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hx
  omega

private theorem nondegenerate_restriction {X : MatSubspace K n} {c : ℕ}
    (h : finrank K (M K n ⧸ X) ≤ c) :
    ∃ U : MatSubspace K n, U ≤ X ∧
      ((tracePairing (K := K) (ι := Fin n)).restrict U).Nondegenerate ∧
      finrank K (M K n ⧸ U) ≤ 2*c := by
  obtain ⟨U, hUX, hn, hc⟩ := exists_nondegenerate_subspace
    tracePairing tracePairing_symmetric tracePairing_nondegenerate X
  exact ⟨U, hUX, hn, hc.trans (Nat.mul_le_mul_left 2 h)⟩

theorem restrictedPolar_rank_nonscalar_left (P Q : M K n)
    (hP : ∀ a : K, P ≠ a • (1 : M K n)) (c : ℕ)
    (hSc : finrank K (M K n ⧸ S) ≤ c) (hRc : finrank K (M K n ⧸ R) ≤ c) :
    (n - 4*c) * (n*n - 2*c) ≤ finrank K (restrictedPolar hS hR P Q).range :=
  polar_rank_of_nonscalar_left P Q (restrictedPolar hS hR P Q)
    (restrictedPolar_tmul hS hR P Q) hP c hSc hRc

theorem restrictedPolar_rank_nonscalar_right (P Q : M K n)
    (hQ : ∀ a : K, Q ≠ a • (1 : M K n)) (c : ℕ)
    (hSc : finrank K (M K n ⧸ S) ≤ c) (hRc : finrank K (M K n ⧸ R) ≤ c) :
    (n - 4*c) * (n*n - 2*c) ≤ finrank K (restrictedPolar hS hR P Q).range :=
  polar_rank_of_nonscalar_right P Q (restrictedPolar hS hR P Q)
    (restrictedPolar_tmul hS hR P Q) hQ c hSc hRc

private theorem matAnti_scalar (a : K) :
    matAnti (a • (1 : M K n)) = (a+a) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  change matAnti (a • (1 : M K n)) x = (a+a) • x
  rw [matAnti_apply, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, add_smul]

private theorem tensorSum_scalars {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (a b : K) :
    tensorSum (a • (LinearMap.id : End K V)) (b • (LinearMap.id : End K W)) =
      (a+b) • (LinearMap.id : End K (V ⊗[K] W)) := by
  apply TensorProduct.ext'
  intro x y
  simp only [tensorSum, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.smul_apply,
    LinearMap.id_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul]

set_option maxHeartbeats 1200000 in
theorem restrictedPolar_rank_scalar (a b : K) (h2 : (2 : K) ≠ 0) (hab : a+b ≠ 0)
    (c : ℕ) (hSc : finrank K (M K n ⧸ S) ≤ c) (hRc : finrank K (M K n ⧸ R) ≤ c) :
    (n - 4*c) * (n*n - 2*c) ≤ finrank K
      (restrictedPolar hS hR (a • (1 : M K n)) (b • (1 : M K n))).range := by
  obtain ⟨U, hUS, hU, hUc⟩ := nondegenerate_restriction hSc
  obtain ⟨W, hWR, hW, hWc⟩ := nondegenerate_restriction hRc
  let P : M K n := a • 1
  let Q : M K n := b • 1
  let e : U ⊗[K] W →ₗ[K] S ⊗[K] R :=
    TensorProduct.map (Submodule.inclusion hUS) (Submodule.inclusion hWR)
  have hb := rank_via_tensor_sum (restrictedPolar hS hR P Q) P Q U W hU hW e (by
    intro x x' y y'
    simp only [e, TensorProduct.map_tmul]
    simpa only [Submodule.coe_inclusion] using restrictedPolar_tmul hS hR P Q
      (Submodule.inclusion hUS x) (Submodule.inclusion hUS x')
      (Submodule.inclusion hWR y) (Submodule.inclusion hWR y'))
  have hc (X : MatSubspace K n)
      (hX : ((tracePairing (K:=K) (ι:=Fin n)).restrict X).Nondegenerate) (s : K) :
      (pairingProject (tracePairing (K:=K) (ι:=Fin n)) X hX).comp
      ((matAnti (s • (1 : M K n))).comp X.subtype) = (s+s) • LinearMap.id := by
    rw [matAnti_scalar]
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun (pairingProject_split (tracePairing (K:=K) (ι:=Fin n)) X hX) z
    change pairingProject (tracePairing (K:=K) (ι:=Fin n)) X hX ((s+s) • z.val) = (s+s) • z
    rw [map_smul]
    exact congrArg (fun v : X => (s+s) • v) hz
  dsimp only [P,Q] at hb
  rw [hc U hU a, hc W hW b, tensorSum_scalars] at hb
  have hne : a+a+(b+b) ≠ 0 := by
    have h : a+a+(b+b) = (2 : K)*(a+b) := by ring
    rw [h]
    exact mul_ne_zero h2 hab
  let f : End K (U ⊗[K] W) := (a+a+(b+b)) • LinearMap.id
  have hinj : Function.Injective f := by
    intro x y h
    change (a+a+(b+b)) • x = (a+a+(b+b)) • y at h
    have he := congrArg (fun z : U ⊗[K] W => (a+a+(b+b))⁻¹ • z) h
    simpa [smul_smul, inv_mul_cancel₀ hne] using he
  change finrank K f.range ≤ finrank K
    (restrictedPolar hS hR (a • (1 : M K n)) (b • (1 : M K n))).range at hb
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_tensorProduct] at hb
  have hle : n ≤ n*n := by
    cases n with
    | zero => simp
    | succ n => exact by simpa using Nat.mul_le_mul_left (n+1) (Nat.succ_le_succ (Nat.zero_le n))
  have hfirst : n - 4*c ≤ n*n - 2*c := by omega
  exact (Nat.mul_le_mul (hfirst.trans (finrank_of_codim_le hUc))
    (finrank_of_codim_le hWc)).trans hb


end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.restrictedPolar_rank_nonscalar_left
#print axioms Mathproof.EvenOrdinaryTISingular.restrictedPolar_rank_nonscalar_right
#print axioms Mathproof.EvenOrdinaryTISingular.restrictedPolar_rank_scalar

