import EvenP2PolarQuadratic
import EvenSingularRank
import Mathlib.Algebra.CharP.Basic

/-! The Problem 1.7 tensor polar operators and joint target, with narrow
partial trace imports. -/
namespace Mathproof.EvenOrdinaryTISingular.PolarOperator
open scoped BigOperators TensorProduct Matrix
open Module Matrix LinearMap EvenTI.AnchorCovariance
open Mathproof.Problem17TracePairing Mathproof.Problem17TensorEscape
open Mathproof.Problem17PolarAssembly
open Mathproof.EvenOrdinaryTISingular.PolarQuadratic

noncomputable section

section Matrix
variable {K i j : Type*} [Field K] [Fintype i] [Fintype j]
variable [DecidableEq i] [DecidableEq j]

abbrev TraceZero (K : Type*) [Field K] (i : Type*) [Fintype i] :=
  (Matrix.traceLinearMap (α := K) i K).ker

def embed : (TraceZero K i) ⊗[K] (TraceZero K j) →ₗ[K]
    Matrix (i × j) (i × j) K :=
  (kroneckerLinearEquiv i i j j K).toLinearMap.comp
    (TensorProduct.map (Submodule.subtype _) (Submodule.subtype _))

abbrev ZSpace (K : Type*) [Field K] (i j : Type*) [Fintype i] [Fintype j] :=
  TraceZero K i ⊗[K] TraceZero K j

def jointValue (P : Mat K i) (Q : Mat K j) : Mat K (i × j) →ₗ[K] K :=
  ((tracePairing P).comp partialTraceLeft) + ((tracePairing Q).comp partialTraceRight)

def jointPolar (P : Mat K i) (Q : Mat K j) : LinearMap.BilinForm K (Mat K (i × j)) where
  toFun x := (jointValue P Q).comp (LinearMap.mulLeft K x + LinearMap.mulRight K x)
  map_add' x y := by
    ext z
    change jointValue P Q ((x + y) * z + z * (x + y)) =
      jointValue P Q (x*z + z*x) + jointValue P Q (y*z + z*y)
    simp only [add_mul, mul_add, map_add]
    abel
  map_smul' a x := by
    ext z
    change jointValue P Q ((a • x) * z + z * (a • x)) =
      a • jointValue P Q (x*z + z*x)
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, map_smul]

def supportedPolar (P : Mat K i) (Q : Mat K j) :
    LinearMap.BilinForm K (ZSpace K i j) :=
  (jointPolar P Q).compl₁₂ embed embed

theorem jointValue_square_add (P : Mat K i) (Q : Mat K j) (x y : ZSpace K i j) :
    jointValue P Q (embed (x+y) ^ 2) =
      jointValue P Q (embed x ^ 2) + jointValue P Q (embed y ^ 2) +
        supportedPolar P Q x y := by
  change jointValue P Q (embed (x+y) ^ 2) =
    jointValue P Q (embed x ^ 2) + jointValue P Q (embed y ^ 2) +
    jointValue P Q (embed x * embed y + embed y * embed x)
  simp only [map_add, pow_two, add_mul, mul_add]
  abel

theorem supportedPolar_tmul (P : Mat K i) (Q : Mat K j) (x x' : TraceZero K i) (y y' : TraceZero K j) :
    supportedPolar P Q (x ⊗ₜ[K] y) (x' ⊗ₜ[K] y') =
      tracePairing (matAnti P x.val) x'.val * tracePairing y.val y'.val +
        tracePairing x.val x'.val * tracePairing (matAnti Q y.val) y'.val := by
  simpa [supportedPolar, jointPolar, jointValue, embed, tracePairing, matAnti_apply] using
    (polar_trace_tensor_sum P x.val x'.val Q y.val y'.val)

theorem supported_trace_zero (x : ZSpace K i j) : (embed x).trace = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, Matrix.trace_add, hx, hy]
  | tmul x y =>
    have hx : x.val.trace = 0 := x.property
    have hy : y.val.trace = 0 := y.property
    simp [embed, Matrix.trace_kronecker, hx, hy]

end Matrix

section LowerBound
variable {K : Type*} [Field K] {n : ℕ}
abbrev M (K : Type*) (n : ℕ) := Mat K (Fin n)
abbrev T (K : Type*) [Field K] (n : ℕ) := ZSpace K (Fin n) (Fin n)

set_option maxHeartbeats 800000 in
theorem rank_via_tensor_sum {V : Type*} [AddCommMonoid V] [Module K V] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (P Q : M K n)
    (S R : Submodule K (M K n))
    (hs : ((tracePairing (K:=K)).restrict S).Nondegenerate)
    (hr : ((tracePairing (K:=K)).restrict R).Nondegenerate)
    (e : S ⊗[K] R →ₗ[K] V)
    (hB : ∀ (x x' : S) (y y' : R), B (e (x ⊗ₜ[K] y)) (e (x' ⊗ₜ[K] y')) =
      tracePairing (matAnti P x.val) x'.val * tracePairing y.val y'.val +
        tracePairing x.val x'.val * tracePairing (matAnti Q y.val) y'.val) :
    finrank K (tensorSum
      ((pairingProject tracePairing S hs).comp ((matAnti P).comp S.subtype))
      ((pairingProject tracePairing R hr).comp ((matAnti Q).comp R.subtype))).range ≤
      finrank K B.range := by
  let L := (pairingProject tracePairing S hs).comp ((matAnti P).comp S.subtype)
  let N := (pairingProject tracePairing R hr).comp ((matAnti Q).comp R.subtype)
  let F : S ⊗[K] R ≃ₗ[K] Module.Dual K (S ⊗[K] R) := tensorPairing ((tracePairing (K:=K)).restrict S) ((tracePairing (K:=K)).restrict R) hs hr
  have he : B.compl₁₂ e e = F.toLinearMap.comp (tensorSum L N) := by
    apply TensorProduct.ext'
    intro x y
    apply TensorProduct.ext'
    intro x' y'
    change B (e (x ⊗ₜ[K] y)) (e (x' ⊗ₜ[K] y')) =
      F (tensorSum L N (x ⊗ₜ[K] y)) (x' ⊗ₜ[K] y')
    rw [hB]
    simp only [tensorSum, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      map_add, F, tensorPairing_tmul]
    change _ =
      (tracePairing (L x).val x'.val) * tracePairing y.val y'.val +
        tracePairing x.val x'.val * tracePairing (N y).val y'.val
    simp only [L, N, LinearMap.comp_apply, Submodule.subtype_apply, pairingProject_pair]
  have hb := rank_pullback_le B e
  rw [he, rank_comp_pairing F] at hb
  exact hb

end LowerBound
variable {K : Type*} [Field K] {n : ℕ}

def leftTrace (K : Type*) [Field K] (n : ℕ) : M K n × M K n →ₗ[K] K :=
  (Matrix.traceLinearMap (α:=K) (Fin n) K).comp (LinearMap.fst K _ _)

def rightTrace (K : Type*) [Field K] (n : ℕ) : M K n × M K n →ₗ[K] K :=
  (Matrix.traceLinearMap (α:=K) (Fin n) K).comp (LinearMap.snd K _ _)

noncomputable def jointTarget (K : Type*) [Field K] (n : ℕ) : Submodule K (M K n × M K n) := by
  classical
  exact if (2 : K) = 0 then (leftTrace K n).ker ⊓ (rightTrace K n).ker
    else (leftTrace K n - rightTrace K n).ker

def covariants (x : T K n) : jointTarget K n :=
  ⟨(partialTraceLeft (embed x ^ 2), partialTraceRight (embed x ^ 2)), by
    unfold jointTarget
    split_ifs with h
    · have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by simpa using h)
      exact quadratic_partial_traces_zero_charTwo _ (supported_trace_zero x)
    · change (Matrix.trace (partialTraceLeft (embed x ^ 2)) -
        Matrix.trace (partialTraceRight (embed x ^ 2))) = 0
      rw [partial_traces_same_trace, sub_self]⟩

end
end Mathproof.EvenOrdinaryTISingular.PolarOperator

#print axioms Mathproof.EvenOrdinaryTISingular.PolarOperator.rank_via_tensor_sum
#print axioms Mathproof.EvenOrdinaryTISingular.PolarOperator.covariants


