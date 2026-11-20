import EvenP2PolarOperators
import EvenP3SingularRectRank

namespace Mathproof.EvenOrdinaryTISingular.RectPolar

open scoped TensorProduct Matrix BigOperators
open Module LinearMap Matrix EvenTI.AnchorCovariance
open Mathproof.Problem17PolarAssembly Mathproof.Problem17TracePairing
open Mathproof.EvenOrdinaryTISingular.PolarOperator
open Mathproof.EvenOrdinaryTISingular.PolarQuadratic
open Mathproof.Problem17TensorEscape

noncomputable section

variable {K : Type*} [Field K] {u v : ℕ}

def leftTrace (K : Type*) [Field K] (u v : ℕ) : M K u × M K v →ₗ[K] K :=
  (Matrix.traceLinearMap (α:=K) (Fin u) K).comp (LinearMap.fst K _ _)

def rightTrace (K : Type*) [Field K] (u v : ℕ) : M K u × M K v →ₗ[K] K :=
  (Matrix.traceLinearMap (α:=K) (Fin v) K).comp (LinearMap.snd K _ _)

noncomputable def jointTarget (K : Type*) [Field K] (u v : ℕ) : Submodule K (M K u × M K v) := by
  classical
  exact if (2 : K) = 0 then (leftTrace K u v).ker ⊓ (rightTrace K u v).ker
    else (leftTrace K u v - rightTrace K u v).ker

def covariants (x : ZSpace K (Fin u) (Fin v)) : jointTarget K u v :=
  ⟨(partialTraceLeft (embed x ^ 2), partialTraceRight (embed x ^ 2)), by
    unfold jointTarget
    split_ifs with h
    · have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by simpa using h)
      exact quadratic_partial_traces_zero_charTwo _ (supported_trace_zero x)
    · change (Matrix.trace (partialTraceLeft (embed x ^ 2)) -
        Matrix.trace (partialTraceRight (embed x ^ 2))) = 0
      rw [partial_traces_same_trace, sub_self]⟩


abbrev TraceSpace (K : Type*) [Field K] (n : ℕ) := TraceZero K (Fin n)

abbrev MatSubspace (K : Type*) (n : ℕ) [Field K] := Submodule K (M K n)

variable {S : MatSubspace K u} {R : MatSubspace K v}
variable (hS : S ≤ TraceSpace K u) (hR : R ≤ TraceSpace K v)

/-- The rectangular kernel projections produce two possibly different proper
subspaces of the trace-zero matrix spaces. -/
def subspaceTensor : S ⊗[K] R →ₗ[K] ZSpace K (Fin u) (Fin v) :=
  TensorProduct.map (Submodule.inclusion hS) (Submodule.inclusion hR)

def restrictedPolar (P : M K u) (Q : M K v) : LinearMap.BilinForm K (S ⊗[K] R) :=
  (supportedPolar P Q).compl₁₂ (subspaceTensor hS hR) (subspaceTensor hS hR)

def restrictedCovariants (x : S ⊗[K] R) : jointTarget K u v :=
  covariants (subspaceTensor hS hR x)

private theorem restrictedPolar_tmul (P : M K u) (Q : M K v) (x x' : S) (y y' : R) :
    restrictedPolar hS hR P Q (x ⊗ₜ[K] y) (x' ⊗ₜ[K] y') =
      tracePairing (matAnti P x.val) x'.val * tracePairing y.val y'.val +
      tracePairing x.val x'.val * tracePairing (matAnti Q y.val) y'.val := by
  change supportedPolar P Q (subspaceTensor hS hR (x ⊗ₜ[K] y))
    (subspaceTensor hS hR (x' ⊗ₜ[K] y')) = _
  simp only [subspaceTensor, TensorProduct.map_tmul]
  simpa only [Submodule.coe_inclusion] using supportedPolar_tmul P Q
    (Submodule.inclusion hS x) (Submodule.inclusion hS x')
    (Submodule.inclusion hR y) (Submodule.inclusion hR y')

theorem restrictedPolar_rank_nonscalar_left (P : M K u) (Q : M K v)
    (hP : ∀ a : K, P ≠ a • (1 : M K u)) (c : ℕ)
    (hSc : finrank K (M K u ⧸ S) ≤ c) (hRc : finrank K (M K v ⧸ R) ≤ c) :
    (u - 4*c) * (v*v - 2*c) ≤ finrank K (restrictedPolar hS hR P Q).range :=
  polar_rank_of_nonscalar_left P Q (restrictedPolar hS hR P Q)
    (restrictedPolar_tmul hS hR P Q) hP c hSc hRc

theorem restrictedPolar_rank_nonscalar_right (P : M K u) (Q : M K v)
    (hQ : ∀ a : K, Q ≠ a • (1 : M K v)) (c : ℕ)
    (hSc : finrank K (M K u ⧸ S) ≤ c) (hRc : finrank K (M K v ⧸ R) ≤ c) :
    (v - 4*c) * (u*u - 2*c) ≤ finrank K (restrictedPolar hS hR P Q).range :=
  polar_rank_of_nonscalar_right P Q (restrictedPolar hS hR P Q)
    (restrictedPolar_tmul hS hR P Q) hQ c hSc hRc

private theorem matAnti_scalar {n : ℕ} (a : K) :
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
    (c : ℕ) (hSc : finrank K (M K u ⧸ S) ≤ c) (hRc : finrank K (M K v ⧸ R) ≤ c) :
    (u*u - 2*c) * (v*v - 2*c) ≤ finrank K
      (restrictedPolar hS hR (a • (1 : M K u)) (b • (1 : M K v))).range := by
  obtain ⟨U, hUS, hU, hUc⟩ := nondegenerate_restriction hSc
  obtain ⟨W, hWR, hW, hWc⟩ := nondegenerate_restriction hRc
  let P : M K u := a • 1
  let Q : M K v := b • 1
  let e : U ⊗[K] W →ₗ[K] S ⊗[K] R :=
    TensorProduct.map (Submodule.inclusion hUS) (Submodule.inclusion hWR)
  have hb := rank_via_tensor_sum (restrictedPolar hS hR P Q) P Q U W hU hW e (by
    intro x x' y y'
    simp only [e, TensorProduct.map_tmul]
    simpa only [Submodule.coe_inclusion] using restrictedPolar_tmul hS hR P Q
      (Submodule.inclusion hUS x) (Submodule.inclusion hUS x')
      (Submodule.inclusion hWR y) (Submodule.inclusion hWR y'))
  have hc {n : ℕ} (X : MatSubspace K n)
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
    (restrictedPolar hS hR (a • (1 : M K u)) (b • (1 : M K v))).range at hb
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_tensorProduct] at hb
  exact (Nat.mul_le_mul (finrank_of_codim_le hUc) (finrank_of_codim_le hWc)).trans hb

end
end Mathproof.EvenOrdinaryTISingular.RectPolar

#print axioms Mathproof.EvenOrdinaryTISingular.RectPolar.restrictedPolar_rank_nonscalar_left
#print axioms Mathproof.EvenOrdinaryTISingular.RectPolar.restrictedPolar_rank_nonscalar_right
#print axioms Mathproof.EvenOrdinaryTISingular.RectPolar.restrictedPolar_rank_scalar

