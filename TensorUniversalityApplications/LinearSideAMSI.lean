import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace LinearSideAMSI

open scoped BigOperators

/-- Testing a subspace by a coordinate contraction detects exactly the nonzero coordinates. -/
theorem contraction_support {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (D : Submodule K V) (a : ι → K) :
    (∀ i, ∀ v ∈ U i, a i • v ∈ D) ↔ (∀ i, a i ≠ 0 → U i ≤ D) := by
  constructor
  · intro h i ha v hv
    have hm := D.smul_mem (a i)⁻¹ (h i v hv)
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hm
  · intro h i v hv
    by_cases ha : a i = 0
    · simpa only [ha, zero_smul] using D.zero_mem
    · exact D.smul_mem (a i) (h i ha hv)

/-- Preserving the line of the sum makes all frame scalars equal. -/
theorem frame_common_scale {K V W ι : Type*} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (P : V →ₗ[K] W) (u : ι → V) (v : ι → W) (a : ι → K) (s : K)
    (hv : LinearIndependent K v) (hcols : ∀ i, P (u i) = a i • v i)
    (hsum : P (∑ i, u i) = s • ∑ i, v i) :
    ∀ i, a i = s := by
  apply (Fintype.linearIndependent_iffₛ.mp hv) a (fun _ => s)
  simpa only [map_sum, hcols, Finset.smul_sum] using hsum

/-- The baseline rank from the two disjoint heavy symplectic blocks. -/
def markerRank (b : ℕ) (first second : Bool) : ℕ :=
  (if first then 2 * (b + 1) else 0) + (if second then 4 * (b + 1) else 0)

/-- A perturbation of rank at most `2 * b` leaves the marker support identifiable. -/
theorem rank_window_support (b rank : ℕ) (first second first' second' : Bool)
    (h₁ : markerRank b first second ≤ rank)
    (h₂ : rank ≤ markerRank b first second + 2 * b)
    (h₃ : markerRank b first' second' ≤ rank)
    (h₄ : rank ≤ markerRank b first' second' + 2 * b) :
    first = first' ∧ second = second' := by
  cases first <;> cases second <;> cases first' <;> cases second' <;>
    simp [markerRank] at * <;> omega

end LinearSideAMSI
