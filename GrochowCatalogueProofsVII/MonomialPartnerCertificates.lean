import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi

namespace GrochowCatalogueSeventh

/-- A permutation-invariant coefficient vector pairs to zero with the
    repetition vector if the coordinate count vanishes in the field. -/
theorem invariant_weight_sum {K : Type*} [Field K] {n : ℕ}
    (hn : (n : K) = 0) (w : Fin n → K)
    (h : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n), w (σ i) = w i) :
    (∑ i, w i) = 0 := by
  classical
  by_cases hp : 0 < n
  · let i₀ : Fin n := ⟨0, hp⟩
    have equal (i : Fin n) : w i = w i₀ := by
      simpa using h (Equiv.swap i₀ i) i₀
    calc
      (∑ i, w i) = ∑ _ : Fin n, w i₀ := Finset.sum_congr rfl (fun i _ => equal i)
      _ = 0 := by simp [nsmul_eq_mul, hn]
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hp
    subst n
    simp

/-- An invariant linear functional cannot give a retraction onto the
    repetition line at lengths divisible by the characteristic. -/
theorem invariant_functional_vanishes {K : Type*} [Field K] {n : ℕ}
    (hn : (n : K) = 0) (f : (Fin n → K) →ₗ[K] K)
    (h : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → K), f (fun i => x (σ i)) = f x) :
    f (fun _ => 1) = 0 := by
  classical
  let e (i : Fin n) : Fin n → K := fun j => if j = i then 1 else 0
  have he : (∑ i, e i) = fun _ => 1 := by
    funext j
    simp [e, Finset.sum_apply]
  have hw (σ : Equiv.Perm (Fin n)) (i : Fin n) : f (e (σ i)) = f (e i) := by
    have heq : (fun j => e (σ i) (σ j)) = e i := by
      funext j
      simp [e]
    have hh := h σ (e (σ i))
    rw [heq] at hh
    exact hh.symm
  rw [← he, map_sum]
  exact invariant_weight_sum hn (fun i => f (e i)) hw

end GrochowCatalogueSeventh

#print axioms GrochowCatalogueSeventh.invariant_weight_sum
#print axioms GrochowCatalogueSeventh.invariant_functional_vanishes
